use petgraph::graph::{DefaultIx, EdgeIndex, NodeIndex};
use petgraph::Graph;
use rustc_middle::mir;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyKind, GenericArgsRef};
use std::rc::Rc;
use petgraph::visit::EdgeRef;
use std::collections::{HashSet, VecDeque, HashMap};
use crate::builder::substs_specializer::SubstsSpecializer;
use crate::mir::analysis_context::AnalysisContext;
use crate::mir::function::FuncId;
use rustc_middle::mir::Location;
use crate::pre_analysis::rta::rta::RapidTypeAnalysis;
use crate::mir::path::{PathEnum, PathSelector};
use rustc_span::source_map::Spanned;


use crate::mir::path::Path;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DFGNode {
    pub path: Rc<Path>,
}

impl DFGNode {
    pub fn new(path: Rc<Path>) -> Self {
        DFGNode { path }
    }

    /// Returns the path of the node.
    pub fn path(&self) -> &Rc<Path> {
        &self.path
    }

}

/// What connects two locals in the PFG.
///
/// A node pair can be connected by an intra-procedural assignment *and* by calls
/// at several locations -- `let d = if c { f(a) } else { g(a) };` yields two call
/// edges between the same pair, and `let d = if c { a } else { f(a) };` yields an
/// intra edge and a call edge. Storing a single kind per pair silently discarded
/// all but the first, so `cs_callsites` missed those locations and classified
/// genuinely flow-through callsites as flow entries.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct PFGEdge {
    /// at least one intra-procedural assignment connects these locals
    pub intra: bool,
    /// every callsite whose argument-to-result flow connects them
    pub call_locs: HashSet<Location>,
}

impl From<PFGEdgeEnum> for PFGEdge {
    fn from(kind: PFGEdgeEnum) -> Self {
        let mut e = PFGEdge::default();
        match kind {
            PFGEdgeEnum::IntraPFGEdge => e.intra = true,
            PFGEdgeEnum::CallPFGEdge(l) => { e.call_locs.insert(l); }
        }
        e
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PFGEdgeEnum {
    IntraPFGEdge,
    CallPFGEdge(Location)
}

/// Backward-root sets for every node of a [`FuncPFG`], precomputed by
/// [`FuncPFG::backward_roots_table`]. O(1) per query.
pub struct BackwardRootsTable {
    node_of: HashMap<Rc<Path>, NodeIndex<DefaultIx>>,
    /// node index -> component id
    scc_of: Vec<usize>,
    /// component id -> its backward roots, as sorted deduped node indices
    roots: Vec<Rc<Vec<usize>>>,
}

impl BackwardRootsTable {
    /// `None` when `path` has no node in this PFG -- provenance unknown, so its
    /// callsite must never be merged. Every node that *is* in the PFG has a
    /// non-empty root set, since every component traces back to some source of
    /// the condensation, so `None` is the only degenerate case.
    pub fn roots_of(&self, path: &Rc<Path>) -> Option<&Rc<Vec<usize>>> {
        let n = self.node_of.get(path)?;
        Some(&self.roots[self.scc_of[n.index()]])
    }

    /// The graph node for `path`, or `None` when it has none.
    pub fn node(&self, path: &Rc<Path>) -> Option<NodeIndex<DefaultIx>> {
        self.node_of.get(path).copied()
    }

    /// Roots of an already-resolved node. Always defined, since every component
    /// traces back to some source of the condensation.
    pub fn roots_of_node(&self, n: NodeIndex<DefaultIx>) -> &Rc<Vec<usize>> {
        &self.roots[self.scc_of[n.index()]]
    }
}

// === Pointer Flow Graph for a function ===
#[derive(Clone, Debug)]
pub struct FuncPFG {
    pub(crate) graph: Graph<DFGNode, PFGEdge>,
    edges: HashMap<(NodeIndex<DefaultIx>, NodeIndex<DefaultIx>), EdgeIndex<DefaultIx>>,
    pub func_id: FuncId,
    // whether there is any argument-to-return flow (precision critical)
    pub has_arg_to_return_flow: bool, 
    // call-site to (arg paths, return path) mapping
    pub callsite_to_locals: HashMap<Location, (Vec<(usize, Rc<Path>)>, Rc<Path>)>,
    pub static_callsites: HashSet<Location>,
    // record of function pointer (FnPtr) and definition (FnDef) call-sites
    pub fn_ptr_def_callsites: HashSet<Location>,
    // record of closure and dynamic dispatch call-sites
    pub closure_dyn_callsites: HashSet<Location>, 
    // call-sites with arg->return path
    pub cs_callsites: HashSet<Location>,
    // parameter with flow to return
    pub param_with_flow: HashSet<usize>,
    /// The callee body is a compiler-generated closure/coroutine body. Calls
    /// through `Fn*` pass the receiver as formal 1 and unpack the argument tuple
    /// into formals 2..N for these bodies.
    pub is_closure_body: bool,
    /// The callee is an actual trait-method implementation. Unlike a closure or
    /// function item reached through `Fn*`, its MIR consumes the raw receiver and
    /// tuple arguments directly.
    pub has_self_parameter: bool,
    /// Redundant flow-entry callsite merging.
    ///
    /// Keyed by `(callsite, callee)`, not by callsite alone: one location can
    /// have several callees, and each is grouped against its own siblings using
    /// its own `param_with_flow`. Two callees at one site can therefore end up
    /// in groups with different members and different canonical callsites,
    /// which a location-keyed map cannot hold -- the writes chain or overwrite,
    /// dropping a merge and leaving the result dependent on hash order.
    pub flow_entry_merge: HashMap<(Location, FuncId), Location>,
}


impl FuncPFG {
    pub fn new(func_id: FuncId, is_closure_body: bool, has_self_parameter: bool) -> Self {
        FuncPFG {
            graph: Graph::new(),
            edges: HashMap::new(),
            func_id,
            has_arg_to_return_flow: false,
            callsite_to_locals: HashMap::new(),
            static_callsites: HashSet::new(),
            fn_ptr_def_callsites: HashSet::new(),
            closure_dyn_callsites: HashSet::new(),
            cs_callsites: HashSet::new(),
            param_with_flow: HashSet::new(),
            is_closure_body,
            has_self_parameter,
            flow_entry_merge: HashMap::new(),
        }
    }

    pub fn add_node(&mut self, path: Rc<Path>) -> NodeIndex<DefaultIx> {
        self.graph.add_node(DFGNode::new(path))
    }

    pub fn get_or_insert_node(&mut self, path: Rc<Path>) -> NodeIndex<DefaultIx> {
        // Both sides are already `Rc<Path>`, so compare them directly. Cloning
        // the `Path` into a fresh `Rc` inside the closure, as this used to,
        // deep-copied its projection Vec and allocated an Rc once per node
        // compared -- two allocations per candidate, on a scan that is already
        // linear and runs twice per edge added.
        if let Some(node_index) = self.graph.node_indices().find(|&n| self.graph[n].path == path) {
            node_index
        } else {
            self.add_node(path)
        }
    }

    /// Records `kind` on the edge between `src` and `dst`, creating it if absent.
    /// Returns whether this added information -- a new edge, a first intra
    /// assignment, or a callsite not already recorded -- which is what the
    /// worklist uses to decide whether to re-solve and re-enqueue.
    pub fn add_edge(&mut self, src: Rc<Path>, dst: Rc<Path>, kind: PFGEdgeEnum) -> bool {
        let src_index = self.get_or_insert_node(src);
        let dst_index = self.get_or_insert_node(dst);
        match self.edges.get(&(src_index, dst_index)) {
            Some(&e) => match kind {
                PFGEdgeEnum::IntraPFGEdge => !std::mem::replace(&mut self.graph[e].intra, true),
                PFGEdgeEnum::CallPFGEdge(l) => self.graph[e].call_locs.insert(l),
            },
            None => {
                let e = self.graph.add_edge(src_index, dst_index, PFGEdge::from(kind));
                self.edges.insert((src_index, dst_index), e);
                true
            }
        }
    }

    pub fn get_node(&self, path: &Path) -> Option<&DFGNode> {
        let node = self.graph.node_indices().find(|&n| self.graph[n].path.as_ref() == path);
        if let Some(node_index) = node {
            Some(&self.graph[node_index])
        } else {
            None
        }
    }
    pub fn nodes(&self) -> impl Iterator<Item = &DFGNode> {
        self.graph.node_weights()
    }

    // check loc ⇒ 𝑓 in CTXFunc
    pub fn is_cs_callsite(&self, loc: &Location) -> bool {
        self.cs_callsites.contains(loc)
    }

    /// The canonical flow-entry callsite representing the merge group of `loc`
    /// *as a call to `callee`*, or `loc` itself when that pair is not merged
    /// (always the case under plain --rceus, where the map is empty).
    pub fn canonical_flow_entry(&self, loc: &Location, callee: FuncId) -> Location {
        *self.flow_entry_merge.get(&(*loc, callee)).unwrap_or(loc)
    }

    /// Whether `path` flows into the result of the call at `loc`, i.e. whether
    /// the worklist added a `CallPFGEdge(loc)` out of it.
    ///
    /// This is the pre-analysis's own record of which arguments matter at a
    /// callsite, so reading it back keeps the merge in step with the graph. It
    /// is not the same as testing the callee's `param_with_flow` against the
    /// argument index: `Fn*::call*` passes the arguments as a single tuple, so
    /// caller argument indices and callee parameter indices only correspond for
    /// static calls. The worklist already applies that mapping when it creates
    /// these edges.
    ///
    /// Answered per *location*: `add_edge` deduplicates on `(src, dst)`, so at a
    /// callsite with several callees the edges are the union of what each
    /// contributed. That is a superset of any one callee's flowing arguments,
    /// which costs merges rather than creating unsound ones.
    pub fn flows_at_callsite(&self, n: NodeIndex<DefaultIx>, loc: &Location) -> bool {
        self.graph
            .edges_directed(n, petgraph::Direction::Outgoing)
            .any(|e| e.weight().call_locs.contains(loc))
    }

    /// The backward roots of every node, in one SCC + topological pass.
    ///
    /// A node's roots are the sources it flows from. `compute_flow_entry_merge`
    /// needs them once per flowing argument per callsite, so answering each
    /// query with its own traversal would repeat the same walk for every
    /// callsite sharing a local -- exactly the case merging exists for.
    /// Condensing first gives every node its root set in `O(V + E)`.
    ///
    /// Nodes of one SCC are mutually reachable, so they share a root set, and a
    /// source of the condensation is its own root:
    ///
    /// ```text
    /// roots(S) = { rep(S) }                        if S has no external predecessor
    ///          = U_{P -> S, P != S} roots(P)       otherwise
    /// ```
    ///
    /// Keying on the component rather than on predecessor-less *nodes* matters
    /// for cycles. A node inside a cycle always has a predecessor, so a cycle
    /// with no external entry used to contribute no root at all -- and that
    /// empty set then propagated as an identity element through every union
    /// downstream, so a value derived from such a cycle became
    /// indistinguishable from one that never touched it. Treating the component
    /// as its own root keeps them apart. A predecessor-less node is a singleton
    /// source component whose `rep` is the node itself, so this agrees with the
    /// old rule wherever the old rule was defined.
    pub fn backward_roots_table(&self) -> BackwardRootsTable {
        let n_nodes = self.graph.node_count();

        let mut node_of = HashMap::with_capacity(n_nodes);
        for n in self.graph.node_indices() {
            node_of.insert(self.graph[n].path.clone(), n);
        }

        // tarjan_scc yields the components in reverse topological order (sinks
        // first), so walking it backwards visits every predecessor component
        // before its successors -- the order the propagation below needs.
        let sccs = petgraph::algo::tarjan_scc(&self.graph);
        let mut scc_of = vec![usize::MAX; n_nodes];
        for (i, scc) in sccs.iter().enumerate() {
            for n in scc {
                scc_of[n.index()] = i;
            }
        }

        let mut roots: Vec<Rc<Vec<usize>>> = vec![Rc::new(Vec::new()); sccs.len()];
        for i in (0..sccs.len()).rev() {
            let mut preds: Vec<usize> = Vec::new();
            for &n in &sccs[i] {
                for e in self.graph.edges_directed(n, petgraph::Direction::Incoming) {
                    let p = scc_of[e.source().index()];
                    // Intra-component edges, self-loops included, contribute
                    // nothing: they say where a value came from within its own
                    // cycle, not where the cycle was entered.
                    if p != i {
                        preds.push(p);
                    }
                }
            }
            preds.sort_unstable();
            preds.dedup();

            // A source of the condensation is its own root, named by its least
            // node so the choice is deterministic. This covers a
            // predecessor-less node (a singleton source) and an unentered cycle
            // uniformly.
            if preds.is_empty() {
                let rep = sccs[i].iter().map(|n| n.index()).min().unwrap();
                roots[i] = Rc::new(vec![rep]);
                continue;
            }

            // Chain case -- a single predecessor. Share its Rc rather than
            // rebuilding the vector, which keeps the total work linear in a long
            // flow chain instead of quadratic.
            if preds.len() == 1 {
                let shared = roots[preds[0]].clone();
                roots[i] = shared;
                continue;
            }

            let mut acc: Vec<usize> = Vec::new();
            for p in preds {
                acc.extend_from_slice(&roots[p]);
            }
            acc.sort_unstable();
            acc.dedup();
            roots[i] = Rc::new(acc);
        }

        BackwardRootsTable { node_of, scc_of, roots }
    }

    /// Solve the reachability in the pointer flow graph.
    pub fn solve_graph_reachability(&mut self) {
        // self.print_graph();
        self.has_arg_to_return_flow = false;
        self.cs_callsites.clear();
       
        let param_nodes: Vec<NodeIndex> = self
            .graph
            .node_indices()
            .filter(|&n| matches!(self.graph[n].path.value, PathEnum::Parameter{..}))
            .collect();
        
        let return_idx = self.get_or_insert_node(Path::new_return_value(self.func_id));

        // --- nodes that can reach return (reverse BFS) ---
        let mut reaches_ret: HashSet<NodeIndex> = HashSet::new();
        {
            let mut q = VecDeque::new();
            q.push_back(return_idx);
            while let Some(n) = q.pop_front() {
                if !reaches_ret.insert(n) { continue; }
                for e in self.graph.edges_directed(n, petgraph::Direction::Incoming) {
                    q.push_back(e.source());
                }
            }
        }


        // --- F: nodes reachable from any parameter (forward BFS) ---
        let mut from_param: HashSet<NodeIndex> = HashSet::new();
        {
            let mut q: VecDeque<NodeIndex> = param_nodes.iter().copied().collect();
            while let Some(n) = q.pop_front() {
                if !from_param.insert(n) { continue; }
                for v in self.graph.edges_directed(n, petgraph::Direction::Outgoing) {
                    q.push_back(v.target());
                }
            }
        }
        
        // --- Any arg → return path? ---
        let has_arg_to_return_flow = param_nodes.iter().any(|p| reaches_ret.contains(p));
        self.has_arg_to_return_flow = has_arg_to_return_flow;

        if !has_arg_to_return_flow {
            self.cs_callsites.clear();
            return;
        }

        // --- Collect only parameters that lie on arg→return path ---
        self.param_with_flow.clear();
        for &p in &param_nodes {
            if reaches_ret.contains(&p) {
                let path = &self.graph[p].path;
                let idx = match path.value {
                    PathEnum::Parameter { ordinal, .. } => ordinal,
                    _ => continue,
                };
                self.param_with_flow.insert(idx);
            }
        }

        // --- Collect only call-sites that lie on some arg→return path ---
        for e in self.graph.edge_references() {
            let u = e.source();
            let v = e.target();
            if from_param.contains(&u) && reaches_ret.contains(&v) {
                for loc in &e.weight().call_locs {
                    self.cs_callsites.insert(*loc);
                }
            }
        }
    }

    pub fn print_graph(&self) {
        println!("--- Pointer Flow Graph for function {:?} ---", self.func_id);
        for n in self.graph.node_indices() {
            let node = &self.graph[n];
            println!("  Node {:?}", node.path);
            // println!("  Node {:?}: from_non_param={:?}", node.path, node.from_non_param);
        }
        for e in self.graph.edge_references() {
            let src = &self.graph[e.source()];
            let dst = &self.graph[e.target()];
            println!(
                "  {:?} --{:?}--> {:?}",
                src.path,
                e.weight(),
                dst.path
            );
        }
    }
}


pub struct FuncPointerFlowAnalysis<'a, 'rta, 'tcx, 'compilation> {
    pub(crate) rta: &'rta mut RapidTypeAnalysis<'a, 'tcx, 'compilation>,
    pub(crate) func_id: FuncId,
    pub(crate) mir: &'tcx mir::Body<'tcx>,
    pub (crate) substs_specializer: SubstsSpecializer<'tcx>,
    pub pfg: FuncPFG,
}

impl<'a, 'rta, 'tcx, 'compilation> FuncPointerFlowAnalysis<'a, 'rta, 'tcx, 'compilation> {
    pub fn new(
        rta: &'rta mut RapidTypeAnalysis<'a, 'tcx, 'compilation>, 
        func_id: FuncId,
        mir: &'tcx mir::Body<'tcx>,
    ) -> FuncPointerFlowAnalysis<'a, 'rta, 'tcx, 'compilation> {
        let func_ref = rta.acx.get_function_reference(func_id);
        let substs_specializer = SubstsSpecializer::new(
            rta.acx.tcx, 
            func_ref.generic_args.clone()
        );

        let is_closure_body = rta.acx.tcx.is_closure_or_coroutine(func_ref.def_id);
        let has_self_parameter = crate::util::has_self_parameter(rta.acx.tcx, func_ref.def_id);

        FuncPointerFlowAnalysis {
            rta,
            func_id,
            mir,
            substs_specializer,
            pfg: FuncPFG::new(func_id, is_closure_body, has_self_parameter),
        }
    }

    #[inline]
    fn acx(&mut self) -> &mut AnalysisContext<'tcx, 'compilation> {
        self.rta.acx
    }

    /// Construct the intra dataflow graph and calculate the dataflow information.
    pub fn calculate_intra_pointer_flow(&mut self) -> FuncPFG {

        // Check if any argument or return type contains pointer or reference
        let mut arg_has_ptr = false;
        for arg in self.mir.args_iter() {
            let decl = &self.mir.local_decls[arg];
            let arg_ty = self.substs_specializer.specialize_generic_argument_type(decl.ty);
            if self.type_contains_pointer_or_ref(arg_ty) {
                arg_has_ptr = true;
                break;
            }
        }
        let return_local =  &self.mir.local_decls[mir::Local::from_u32(0)];
        let return_ty = self.substs_specializer.specialize_generic_argument_type(return_local.ty);
        let return_has_ptr = self.type_contains_pointer_or_ref(return_ty);
        // we construct the pointer flow graph only if there exist pointer/ref in args and return type
        if arg_has_ptr && return_has_ptr {
            self.visit_body();
            self.solve_graph_initial();
        } else {
            // --rceus-m: build the graph anyway, without solving reachability.
            // A function that cannot carry an arg->return pointer flow is still
            // a *caller*, and merging its flow-entry callsites needs its graph
            // and callsite_to_locals to root their arguments. Skipping
            // solve_graph_initial keeps has_arg_to_return_flow false, so this
            // function stays non-precision-critical exactly as before.
            if self.rta.acx.analysis_options.rceus_m {
                self.visit_body();
            }
            self.pfg.has_arg_to_return_flow = false;
            self.pfg.cs_callsites.clear();
        }

        return self.pfg.clone();
    }


    fn solve_graph_initial(&mut self) {
        let ret_path = Path::new_local_parameter_or_result(self.func_id, 0, self.mir.arg_count);
        let _return_idx = self.pfg.get_or_insert_node(ret_path);
        self.pfg.solve_graph_reachability();

    }

    fn visit_body(&mut self){
        for bb in self.mir.basic_blocks.indices() {
            self.visit_basic_block(bb);
        }
    }

    fn visit_basic_block(&mut self, bb: mir::BasicBlock,) {
        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = &self.mir[bb];
        let mut location = bb.start_location();
        let terminator_index = statements.len();

        while location.statement_index < terminator_index {
            self.visit_statement(location, &statements[location.statement_index]);
            location.statement_index += 1;
        }

        if let Some(mir::Terminator {
            ref source_info,
            ref kind,
        }) = *terminator
        {
            self.visit_terminator(location, kind, *source_info);
        }
    }

    /// Calls a specialized visitor for each kind of statement.
    fn visit_statement(&mut self, _location: mir::Location, statement: &mir::Statement<'tcx>) {
        let mir::Statement {kind, source_info: _} = statement;
        match kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                
                let place_ty = self.substs_specializer.specialize_generic_argument_type(
                    self.mir.local_decls[place.local].ty
                );
                
                if self.type_contains_pointer_or_ref(place_ty) {
                    self.visit_assign(place, rvalue);
                }
                
            }
            _ => (),
        }   
    }

    fn visit_assign(&mut self, lplace: &mir::Place<'tcx>, rvalue: &mir::Rvalue<'tcx>) {
        match rvalue {
            mir::Rvalue::Use(operand) | mir::Rvalue::Repeat(operand, _) => {
                self.visit_use(lplace, operand);
            }
            mir::Rvalue::Ref(_, _, place) | mir::Rvalue::AddressOf(_, place) => {
                self.add_ref_pfg_edge(lplace, place);
            }
            mir::Rvalue::Cast(_cast_kind, operand, _ty) => {
                self.visit_use(lplace, operand);
            }
            mir::Rvalue::Aggregate(aggregate_kind, operands) => {
                let is_tuple = self.rta.acx.analysis_options.rceus_ap
                    && matches!(**aggregate_kind, mir::AggregateKind::Tuple);
                for (i, operand) in operands.iter().enumerate() {
                    if is_tuple {
                        if let Some(src) = self.pointer_operand_path(operand) {
                            let dst = Path::new_local_parameter_or_result(
                                self.func_id,
                                lplace.local.as_usize(),
                                self.mir.arg_count,
                            );
                            let dst_field =
                                Path::append_projection_elem(&dst, PathSelector::Field(i));
                            self.pfg.add_edge(src, dst_field, PFGEdgeEnum::IntraPFGEdge);
                        }
                    }
                    self.visit_use(lplace, operand);
                }
            }
            mir::Rvalue::BinaryOp(_, box (loperand, _roperand)) => {
                self.visit_use(lplace, loperand);
            }
            mir::Rvalue::ShallowInitBox(operand, _) => {
                self.visit_use(lplace, operand);
            }
            mir::Rvalue::CopyForDeref(place) => {
                self.add_ref_pfg_edge(lplace, place);
            }
            _ => {
                // println!("Skipping rvalue kind: {:?}", rvalue);
            }
        }
    }

    fn visit_use(&mut self, lplace: &mir::Place<'tcx>, operand: &mir::Operand<'tcx>) {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {

                // For Copy and Move operands,
                // we add an edge from rplace to lplace only if rplace contains pointer or reference.
                let local_decls = &self.mir.local_decls;
                let place_ty = place.ty(local_decls, self.acx().tcx);
                let place_ty = self.substs_specializer.specialize_generic_argument_type(place_ty.ty);

                if self.type_contains_pointer_or_ref(place_ty) {
                    let lpath = Path::new_local_parameter_or_result(self.func_id, lplace.local.as_usize(), self.mir.arg_count); 
                    let rpath = Path::new_local_parameter_or_result(self.func_id, place.local.as_usize(), self.mir.arg_count);
                    let edge_kind = PFGEdgeEnum::IntraPFGEdge;
                    self.pfg.add_edge(rpath.clone(), lpath.clone(), edge_kind);

                    // Preserve tuple components across whole-tuple moves/copies.
                    // Fn/FnMut/FnOnce lower user arguments into such tuples, and
                    // argument provenance must follow each field independently.
                    if self.rta.acx.analysis_options.rceus_ap {
                        if let TyKind::Tuple(field_tys) = place_ty.kind() {
                            for (i, field_ty) in field_tys.iter().enumerate() {
                                if self.type_contains_pointer_or_ref(field_ty) {
                                    let rfield = Path::append_projection_elem(
                                        &rpath,
                                        PathSelector::Field(i),
                                    );
                                    let lfield = Path::append_projection_elem(
                                        &lpath,
                                        PathSelector::Field(i),
                                    );
                                    self.pfg.add_edge(
                                        rfield,
                                        lfield,
                                        PFGEdgeEnum::IntraPFGEdge,
                                    );
                                }
                            }
                        }
                    }
                }
            }
            _ => {} // We do not consider constant operands for pointer flow analysis.
        }

    }

    /// Return the local PFG path for a pointer-carrying operand. Constants have
    /// no caller-parameter provenance and therefore intentionally return None.
    fn pointer_operand_path(&mut self, operand: &mir::Operand<'tcx>) -> Option<Rc<Path>> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let ty = place.ty(&self.mir.local_decls, self.acx().tcx).ty;
                let ty = self.substs_specializer.specialize_generic_argument_type(ty);
                self.type_contains_pointer_or_ref(ty).then(|| {
                    Path::new_local_parameter_or_result(
                        self.func_id,
                        place.local.as_usize(),
                        self.mir.arg_count,
                    )
                })
            }
            mir::Operand::Constant(_) => None,
        }
    }

    fn add_ref_pfg_edge(&mut self, lplace: &mir::Place<'tcx>, rplace: &mir::Place<'tcx>) {
        // For Ref and AddressOf rvalues, 
        // we add an edge from rplace to lplace only if rplace contains pointer or reference.
        let rplace_ty = self.substs_specializer.specialize_generic_argument_type(
                    self.mir.local_decls[rplace.local].ty
        );

        if self.type_contains_pointer_or_ref(rplace_ty) {
            let lpath = Path::new_local_parameter_or_result(self.func_id, lplace.local.as_usize(), self.mir.arg_count);
            let rpath = Path::new_local_parameter_or_result(self.func_id, rplace.local.as_usize(), self.mir.arg_count);
            let edge_kind = PFGEdgeEnum::IntraPFGEdge;
            self.pfg.add_edge(rpath, lpath, edge_kind);
        }
    }
    
    fn visit_terminator(
        &mut self,
        location: mir::Location,
        kind: &mir::TerminatorKind<'tcx>,
        _source_info: mir::SourceInfo,
    ) {
        match kind {
            mir::TerminatorKind::Call {
                func, 
                args,
                destination,
                target: _,
                unwind: _,
                call_source: _,
                fn_span: _,
            } => self.visit_call(func, args, destination, location),
            mir::TerminatorKind::InlineAsm { 
                template: _,
                operands: _,
                destination: _, 
                .. 
            } => {}
            _ => {}
        }
    }


    /// visit call for collecting callsite information
    fn visit_call(
        &mut self,
        func: &mir::Operand<'tcx>,
        args: &Vec<Spanned<mir::Operand<'tcx>>>,
        destination: &mir::Place<'tcx>,
        location: mir::Location,
    ) {
        let destination_ty = self.substs_specializer.specialize_generic_argument_type(
            self.mir.local_decls[destination.local].ty
        );
        if !self.type_contains_pointer_or_ref(destination_ty) {
            return;
        }
        // collect callsite information
        let destination_path = Path::new_local_parameter_or_result(self.func_id, destination.local.as_usize(), self.mir.arg_count);
        let args_paths = self.visit_args(args).into_iter().collect();

        self.pfg.callsite_to_locals.insert(location, (args_paths, destination_path.clone()));
        match func {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let fn_item_ty = self.substs_specializer.specialize_generic_argument_type(
                    self.mir.local_decls[place.local].ty
                );
                match fn_item_ty.kind() {
                    TyKind::Closure(callee_def_id, gen_args)
                    | TyKind::FnDef(callee_def_id, gen_args)
                    | TyKind::Coroutine(callee_def_id, gen_args) => {
                        self.resolve_call(callee_def_id, gen_args, args, destination, location)
                    }
                    TyKind::FnPtr(_) => {
                        // consider as static call for PAG only
                        self.pfg.static_callsites.insert(location);
                    }
                    _ => {}
                }
            }
            mir::Operand::Constant(box constant) => {
                match constant.ty().kind() {
                    TyKind::Closure(callee_def_id, gen_args)
                    | TyKind::FnDef(callee_def_id, gen_args)
                    | TyKind::Coroutine(callee_def_id, gen_args) => {
                        self.resolve_call(callee_def_id, gen_args, args, destination, location)
                    }
                    TyKind::FnPtr(_) => {
                        // consider as static call for PAG only
                        self.pfg.static_callsites.insert(location);
                    }
                    _ => {}
                }
                
            }
        }

    }


    /// collecting all dynamic dispatch callsites information
    fn resolve_call(
        &mut self,
        callee_def_id: &DefId,
        gen_args: &GenericArgsRef<'tcx>,
        _args: &Vec<Spanned<mir::Operand<'tcx>>>,
        _destination: &mir::Place<'tcx>,
        location: mir::Location,
    ) {

        if !self.acx().is_std_ops_fntrait_call(*callee_def_id) {
            self.pfg.static_callsites.insert(location);
            return;
        } 

        let mut first_subst_ty = match gen_args.types().next() {
            Some(ty) => ty,
            None => return,
        };
        first_subst_ty = self.substs_specializer.specialize_generic_argument_type(first_subst_ty);
        // Determine the callsite type based on the first generic argument type
        match first_subst_ty.kind() {
            TyKind::FnPtr(_) => {
                self.pfg.fn_ptr_def_callsites.insert(location);
            }
            TyKind::FnDef(_, _) => {
                self.pfg.fn_ptr_def_callsites.insert(location);
            }
            TyKind::Closure(_, _) | TyKind::Coroutine(_, _) => {
                // The dispatch callee of Closure and Coroutine contains 
                // reference to the closure/coroutine as first argument.
                self.pfg.closure_dyn_callsites.insert(location);
            }
            TyKind::Dynamic(_, _, _) => {
                // The dispatch callee of Dynamic contains self reference as first argument.  
                self.pfg.closure_dyn_callsites.insert(location);
            }
            _ => {}
        }
    }

    // Collect argument paths
    fn visit_args(&mut self, args: &Vec<Spanned<mir::Operand<'tcx>>>,) -> Vec<(usize, Rc<Path>)> {
        let mut idx = 0;
        let mut args_paths = Vec::new();
        for arg in args {
            idx += 1;
            match &arg.node {
                mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                    let arg_ty = self.substs_specializer.specialize_generic_argument_type(
                        self.mir.local_decls[place.local].ty
                    );

                    if self.type_contains_pointer_or_ref(arg_ty) {
                        let arg_path = Path::new_local_parameter_or_result(self.func_id, place.local.as_usize(), self.mir.arg_count);
                        args_paths.push((idx, arg_path));
                    }
                }
                _ => {}
            }
        }
        args_paths
    }
 
    fn type_contains_pointer_or_ref(&mut self, ty: Ty<'tcx>) -> bool {
        if ty.is_any_ptr() {
            return true;
        } else {
            let ptr_projs = self.acx().get_pointer_projections(ty);
            if !ptr_projs.is_empty() {
                return true;
            } else {
                return false;
            }
        }
    }

}
