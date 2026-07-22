use std::collections::{HashMap, HashSet, VecDeque};
use std::time::{Duration, Instant};

use petgraph::visit::EdgeRef;

use rustc_middle::mir::Location;

use crate::graph::call_graph::{CGCallSite, CGNodeId};
use crate::mir::function::FuncId;
use crate::pre_analysis::rta::rta::RapidTypeAnalysis;

use super::func_pointer_flow_analysis::{FuncPFG, FuncPointerFlowAnalysis, PFGEdgeEnum};

pub struct PrecCritFnIdent<'r, 'a, 'tcx, 'compilation> {
    pub rta: &'r mut RapidTypeAnalysis<'a, 'tcx, 'compilation>,

    pub func_pfg_map: HashMap<FuncId, FuncPFG>,
    pub cs_funcs: HashSet<FuncId>,

    worklist: VecDeque<CGNodeId>,

    pub analysis_time: Duration,
}

impl<'r, 'a, 'tcx, 'compilation> PrecCritFnIdent<'r, 'a, 'tcx, 'compilation> {
    pub fn new(rta: &'r mut RapidTypeAnalysis<'a, 'tcx, 'compilation>) -> Self {
        PrecCritFnIdent {
            rta,
            func_pfg_map: HashMap::new(),
            cs_funcs: HashSet::new(),
            worklist: VecDeque::new(),
            analysis_time: Duration::ZERO,
        }
    }

    pub fn analyze(&mut self) {
        let now = Instant::now();

        let funcs: Vec<FuncId> = self.rta.call_graph.func_nodes.keys().copied().collect();
        for func_id in funcs {
            if self.rta.specially_handled_functions.contains(&func_id) {
                continue;
            }
            let def_id = self.rta.acx.get_function_reference(func_id).def_id;
            if !self.rta.acx.tcx.is_mir_available(def_id) {
                continue;
            }
            let mir = self.rta.acx.tcx.optimized_mir(def_id);
            let pfg = FuncPointerFlowAnalysis::new(self.rta, func_id, mir).calculate_intra_pointer_flow();
            if pfg.has_arg_to_return_flow {
                if let Some(&node_id) = self.rta.call_graph.func_nodes.get(&func_id) {
                    self.worklist.push_front(node_id);
                }
            }
            self.func_pfg_map.insert(func_id, pfg);
        }

        let specially_handled_pc: Vec<FuncId> =
            self.rta.specially_handled_precision_critical_functions.iter().copied().collect();
        for f in specially_handled_pc {
            if let Some(&node_id) = self.rta.call_graph.func_nodes.get(&f) {
                self.worklist.push_front(node_id);
            }
        }

        self.precision_critical_func_identification();

        for node_id in self.rta.call_graph.graph.node_indices() {
            if let Some(node) = self.rta.call_graph.graph.node_weight(node_id) {
                if node.req_cs {
                    self.cs_funcs.insert(node.func);
                }
            }
        }

        // --rceus-m only: identify redundant flow-entry callsites. Runs after
        // cs_funcs is final, since the grouping only concerns callees that
        // receive a context.
        if self.rta.acx.analysis_options.rceus_m {
            self.compute_flow_entry_merge();
        }

        self.analysis_time = now.elapsed();
        println!(
            "Precision-critical function identification time: {}",
            humantime::format_duration(self.analysis_time).to_string()
        );
    }

    /// Identify redundant flow-entry callsites (`--rceus-m`).
    ///
    /// Within one caller, two flow-entry callsites are redundant when they call
    /// the same callee and every flowing argument -- an argument at a position
    /// in the callee's `param_with_flow`, i.e. one that reaches the callee's
    /// return -- flows from the same local in the caller's PFG. Those callsites
    /// hand the callee identical pointers, so the separate contexts they induce
    /// are duplicates. Each group is keyed by its smallest-bb callsite; the rest
    /// map onto it.
    ///
    /// This only relabels flow-entry contexts. `cs_funcs`, `cs_callsites` and
    /// the PFG reachability are untouched, so which functions are precision
    /// critical is identical to plain --rceus.
    fn compute_flow_entry_merge(&mut self) {
        // (callee, [(arg position, backward roots)]) -> the flow entries carrying it
        type GroupKey = (FuncId, Vec<(usize, Vec<usize>)>);

        let mut merged: HashMap<FuncId, HashMap<Location, Location>> = HashMap::new();
        let mut groups_merged = 0usize;
        let mut sites_merged = 0usize;
        let mut per_callee: HashMap<FuncId, (usize, usize)> = HashMap::new();
        let mut collected: Vec<(FuncId, FuncId, Vec<Location>)> = Vec::new();

        {
            let cg = &self.rta.call_graph;
            for caller_node in cg.graph.node_indices() {
                let caller_func = cg.graph[caller_node].func;
                let caller_pfg = match self.func_pfg_map.get(&caller_func) {
                    Some(p) => p,
                    None => continue,
                };

                let mut groups: HashMap<GroupKey, Vec<Location>> = HashMap::new();
                for e in cg.graph.edges_directed(caller_node, petgraph::Direction::Outgoing) {
                    let loc = *e.weight().callsite.get_location();
                    // Flow entries only: a flow-through callsite inherits its
                    // caller's flow entry and is never labelled by its own site.
                    if caller_pfg.is_cs_callsite(&loc) {
                        continue;
                    }
                    let callee = cg.graph[e.target()].func;
                    // Only callees that actually receive a context.
                    if !self.cs_funcs.contains(&callee) {
                        continue;
                    }
                    // TEMP EXPERIMENT: RCEUS_NOMERGE=<substr> excludes matching callees.
                    if let Ok(pat) = std::env::var("RCEUS_NOMERGE") {
                        if self.rta.acx.get_function_reference(callee).to_string().contains(&pat) {
                            continue;
                        }
                    }
                    let param_with_flow = match self.func_pfg_map.get(&callee) {
                        Some(p) => &p.param_with_flow,
                        None => continue,
                    };
                    let (args, _dest) = match caller_pfg.callsite_to_locals.get(&loc) {
                        Some(x) => x,
                        None => continue,
                    };

                    // Key on the roots of the flowing arguments. If any of them
                    // has no PFG node its provenance is unknown, so leave the
                    // callsite unmerged rather than guess.
                    let mut key_parts: Vec<(usize, Vec<usize>)> = Vec::new();
                    let mut unknown = false;
                    for (arg_idx, arg_path) in args {
                        if !param_with_flow.contains(arg_idx) {
                            continue;
                        }
                        match caller_pfg.backward_roots(arg_path) {
                            Some(roots) => key_parts.push((*arg_idx, roots)),
                            None => {
                                unknown = true;
                                break;
                            }
                        }
                    }
                    if unknown || key_parts.is_empty() {
                        continue;
                    }
                    key_parts.sort();
                    groups.entry((callee, key_parts)).or_default().push(loc);
                }

                for (_key, mut locs) in groups {
                    if locs.len() < 2 {
                        continue;
                    }
                    collected.push((caller_func, _key.0, locs.clone()));
                    // RCEUS_DUMP_MERGES: per-callee tally of (groups, merged sites).
                    per_callee
                        .entry(_key.0)
                        .and_modify(|e: &mut (usize, usize)| {
                            e.0 += 1;
                            e.1 += locs.len() - 1;
                        })
                        .or_insert((1, locs.len() - 1));
                    // Canonical = smallest bb, then statement index so the choice
                    // is deterministic when one block holds several.
                    locs.sort_by_key(|l| (l.block.as_usize(), l.statement_index));
                    let canonical = locs[0];
                    let m = merged.entry(caller_func).or_default();
                    for l in locs.into_iter().skip(1) {
                        m.insert(l, canonical);
                        sites_merged += 1;
                    }
                    groups_merged += 1;
                }
            }
        }

        // EXPERIMENT: RCEUS_ONLY_GROUP=<n> keeps ONLY the n-th new_display group.
        if let Ok(nv) = std::env::var("RCEUS_ONLY_GROUP") {
            let want: usize = nv.trim().parse().unwrap_or(usize::MAX);
            let mut nd: Vec<&(FuncId, FuncId, Vec<Location>)> = collected
                .iter()
                .filter(|(_, callee, _)| {
                    self.rta.acx.get_function_reference(*callee).to_string().contains("new_display")
                })
                .collect();
            nd.sort_by_key(|(caller, callee, locs)| {
                let m = locs.iter().map(|l| (l.block.as_usize(), l.statement_index)).min().unwrap();
                (caller.as_usize(), callee.as_usize(), m.0, m.1)
            });
            eprintln!("ONLY_GROUP: {} new_display groups total", nd.len());
            merged.clear();
            if let Some((caller, _callee, locs)) = nd.get(want) {
                let mut ls = locs.clone();
                ls.sort_by_key(|l| (l.block.as_usize(), l.statement_index));
                let canon = ls[0];
                let m = merged.entry(*caller).or_default();
                for l in ls.into_iter().skip(1) { m.insert(l, canon); }
            }
        }

        for (func_id, map) in merged {
            if let Some(pfg) = self.func_pfg_map.get_mut(&func_id) {
                pfg.flow_entry_merge = map;
            }
        }

        if let Ok(path) = std::env::var("RCEUS_DUMP_MERGES") {
            use std::io::Write;
            let mut w = std::fs::File::create(&path).expect("merge dump");
            writeln!(w, "# {} redundant flow-entry callsites merged into {} groups",
                     sites_merged, groups_merged).unwrap();
            writeln!(w, "# merged_sites\tgroups\tcallee").unwrap();
            let mut v: Vec<_> = per_callee.iter().collect();
            v.sort_by(|a, b| b.1 .1.cmp(&a.1 .1));
            for (f, (g, sites)) in v {
                let n = self.rta.acx.get_function_reference(*f).to_string();
                writeln!(w, "{}\t{}\t{}", sites, g, n).unwrap();
            }
        }

    }

    // Worklist algorithm for context sensitivity identification.
    // The initial worklist contains functions with intra-procedural argument-to-return flow.
    // For each function in the worklist, we propagate the pointer flow to its callers,
    // and add the callers into the worklist if a caller now has argument-to-return flow.
    fn precision_critical_func_identification(&mut self) {
        // Split the borrows up-front so the inner loop can independently mutate
        // func_pfg_map, worklist, and the call graph.
        let call_graph = &mut self.rta.call_graph;
        let func_pfg_map = &mut self.func_pfg_map;
        let worklist = &mut self.worklist;

        let mut visited = HashSet::new();

        while let Some(node_id) = worklist.pop_front() {
            let node = match call_graph.graph.node_weight(node_id) {
                Some(n) => n,
                None => continue,
            };
            let func_id = node.func;
            visited.insert(node_id);

            // Extracting the parameters that have return flow in the callee.
            // Here, arguments to all special handled callsites (without pag) will be connected to return directly.
            let param_with_flow = match func_pfg_map.get(&func_id) {
                Some(pfg) => Some(pfg.param_with_flow.clone()),
                None => None,
            };

            // Collect incoming edges first to release the iterator's borrow on the graph
            // before we mutate func_pfg_map / worklist below.
            let incoming: Vec<(CGNodeId, rustc_middle::mir::Location)> = call_graph
                .graph
                .edges_directed(node_id, petgraph::Direction::Incoming)
                .map(|e| (e.source(), *e.weight().callsite.get_location()))
                .collect();

            for (src_node_id, location) in incoming {
                let src_node = match call_graph.graph.node_weight(src_node_id) {
                    Some(n) => n,
                    None => continue,
                };

                let src_func_id = src_node.func;
                let src_func_pfg = match func_pfg_map.get_mut(&src_func_id) {
                    Some(pfg) => pfg,
                    None => continue, // This should not happen, caller always has pfg
                };

                // propagate pointer flow from callee to caller
                let mut new_edges_added = false;
                if src_func_pfg.callsite_to_locals.contains_key(&location) {
                    let (args, destination) = src_func_pfg.callsite_to_locals[&location].clone();
                    let is_static_call = src_func_pfg.static_callsites.contains(&location);
                    let is_closure_or_dyn_call = src_func_pfg.closure_dyn_callsites.contains(&location);
                    for arg in args {
                        let (arg_idx, arg_path) = arg.clone();
                        // For static calls, only consider the parameters that have flow to the callee.
                        // For closure/dyn calls, the second argument will be dispatched to parameter 2..N in callee,
                        // we connect arg 2 to return if any of parameter 2..N has flow in callee.
                        // for other dynamic resolved calls (fnptr),
                        // the second argument will be dispatched to parameter 1..N in callee,
                        // we connect arg 2 to return if any of parameter 1..N has flow in callee.
                        if let Some(param_with_flow) = &param_with_flow {
                            if is_static_call {
                                if !param_with_flow.contains(&arg_idx) {
                                    continue;
                                }
                            }
                            if is_closure_or_dyn_call {
                                if !param_with_flow.contains(&arg_idx) && arg_idx == 1 {
                                    continue;
                                }
                            }
                        }
                        let edge_kind = PFGEdgeEnum::CallPFGEdge(location);
                        new_edges_added |= src_func_pfg.add_edge(arg_path.clone(), destination.clone(), edge_kind);
                    }
                }

                if new_edges_added {
                    src_func_pfg.solve_graph_reachability();
                    if src_func_pfg.has_arg_to_return_flow {
                        worklist.push_back(src_node_id);
                    }
                }
            }
        }

        for node_id in &visited {
            if let Some(node) = call_graph.graph.node_weight_mut(*node_id) {
                node.req_cs = true;
            }
        }
    }
}
