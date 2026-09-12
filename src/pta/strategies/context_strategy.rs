// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

//! Context strategies for context-sensitive pointer analyses, 
//! such as k-callsite-sensitive, k-object-sensitive, ...
//! 
//! Only k-callsite-sensitive pointer analyses have been thoroughly evaluated so far.

use std::rc::Rc;
use std::collections::HashSet;
use std::collections::hash_map::Iter;
use std::collections::HashMap;
use std::collections::{BTreeSet, VecDeque};
use petgraph::visit::EdgeRef;
use rustc_middle::mir::Location;
use crate::mir::call_site::{BaseCallSite, CSCallSite};
use crate::mir::context::{Context, ContextCache, ContextElement, ContextId, HybridCtxElem};
use crate::mir::function::FuncId;
use crate::mir::path::{CSPath, Path, PathEnum, PathSelector};
use crate::rustc_index::Idx;
use super::stack_filtering::{StackFilter, SFReachable};
use crate::pre_analysis::precision_critical_func_identification::func_pointer_flow_analysis::FuncPFG;


pub trait ContextStrategy {
    type E: ContextElement;
    fn empty_context(&self) -> Rc<Context<Self::E>>;
    fn get_empty_context_id(&mut self) -> ContextId;
    fn get_context_id(&mut self, context: &Rc<Context<Self::E>>) -> ContextId;
    fn get_context_by_id(&self, context_id: ContextId) -> Rc<Context<Self::E>>;
    fn get_context_iter(&self) -> Option<Iter<'_, Rc<Context<Self::E>>, ContextId>> {
        None
    }
    fn new_instance_call_context(
        &mut self,
        callsite: &Rc<CSCallSite>,
        receiver: Option<&Rc<CSPath>>,
        callee: FuncId,
    ) -> Option<ContextId>;

    fn new_static_call_context(&mut self, callsite: &Rc<CSCallSite>, callee: FuncId) -> ContextId;

    fn with_stack_filter<F: SFReachable>(&mut self, _stack_filter: &mut StackFilter<F>)
    where
        F: Copy + Into<FuncId> + std::cmp::Eq + std::hash::Hash,
    {}

    fn set_prec_crit_fn_ident_data(
        &mut self,
        _cs_funcs: HashSet<FuncId>,
        _func_pfg_map: HashMap<FuncId, FuncPFG>,
    ) {}

    /// ABLATION hook (argprov only): flow-entry callees whose provenance seeding
    /// should be suppressed. Default no-op.
    fn set_noprov_callees(&mut self, _callees: HashSet<FuncId>) {}

    /// ABLATION: restrict `set_noprov_callees` to these flow-entry Site funcs.
    fn set_noprov_sites(&mut self, _sites: HashSet<FuncId>) {}

    /// Library-ablation (RCEUS_LIB_MODE): treat the given set of functions as
    /// precision-critical instead of running the pre-analysis. Flow entries are
    /// the user->library boundary (a callsite whose caller is not in the set).
    fn set_library_mode(&mut self, _library_funcs: HashSet<FuncId>) {}

    /// The precision-critical functions this strategy was handed, for the
    /// end-of-analysis report. `None` for strategies that do not use them.
    fn cs_funcs(&self) -> Option<&HashSet<FuncId>> {
        None
    }
}

pub struct ContextInsensitive {}


impl ContextStrategy for ContextInsensitive {
    type E = BaseCallSite;

    fn empty_context(&self) -> Rc<Context<BaseCallSite>> {
        Context::new_empty()
    }

    fn get_empty_context_id(&mut self) -> ContextId {
        ContextId::new(0)
    }
    
    fn get_context_id(&mut self, _context: &Rc<Context<BaseCallSite>>) -> ContextId {
        ContextId::new(0)
    } 

    fn get_context_by_id(&self, _context_id: ContextId) -> Rc<Context<BaseCallSite>> {
        self.empty_context()
    }  

    fn new_instance_call_context(
        &mut self,
        _callsite: &Rc<CSCallSite>,
        _receiver: Option<&Rc<CSPath>>,
        _callee: FuncId,
    ) -> Option<ContextId> {
        Some(ContextId::new(0))
    }

    fn new_static_call_context(&mut self, _callsite: &Rc<CSCallSite>, _callee: FuncId) -> ContextId {
        ContextId::new(0)
    }
}

pub struct KCallSiteSensitive {
    /// Context length limit for methods
    pub(crate) k: usize,
    pub ctx_cache: ContextCache<BaseCallSite>,
}

impl KCallSiteSensitive {
    pub fn new(k: usize) -> Self {
        Self {
            k, 
            ctx_cache: ContextCache::new(),
        }
    }

    pub fn new_context(&mut self, callsite: &Rc<CSCallSite>) -> ContextId {
        let caller_ctx_id = callsite.func.cid;
        let caller_ctx = self.ctx_cache.get_context(caller_ctx_id).unwrap();
        let callee_ctx = Context::new_k_limited_context(
            &caller_ctx,
            callsite.into(),
            self.k,
        );  
        let callee_ctx_id = self.ctx_cache.get_context_id(&callee_ctx);
        callee_ctx_id
    }
}

impl ContextStrategy for KCallSiteSensitive {
    type E = BaseCallSite;

    fn empty_context(&self) -> Rc<Context<BaseCallSite>> {
        Context::new_empty()
    }
    
    fn get_context_id(&mut self, context: &Rc<Context<BaseCallSite>>) -> ContextId {
        self.ctx_cache.get_context_id(context)
    } 

    fn get_context_by_id(&self, context_id: ContextId) -> Rc<Context<BaseCallSite>> {
        self.ctx_cache.get_context(context_id).unwrap_or(Context::new_empty())
    }  

    fn get_empty_context_id(&mut self) -> ContextId {
        self.get_context_id(&Context::new_empty())
    }

    fn get_context_iter(&self) -> Option<Iter<'_, Rc<Context<Self::E>>, ContextId>> {
        Some(self.ctx_cache.get_context_iter())
    }

    fn new_instance_call_context(
        &mut self,
        callsite: &Rc<CSCallSite>,
        _receiver: Option<&Rc<CSPath>>,
        _callee: FuncId,
    ) -> Option<ContextId> {
        Some(self.new_context(callsite))
    }

    fn new_static_call_context(&mut self, callsite: &Rc<CSCallSite>, _callee: FuncId) -> ContextId {
       self.new_context(callsite)
    }

    fn with_stack_filter<F: SFReachable>(&mut self, stack_filter: &mut StackFilter<F>)
    where
        F: Copy + Into<FuncId> + std::cmp::Eq + std::hash::Hash,
    {
        stack_filter.with_kcs_context_strategy(self);
    }
}


pub struct KObjectSensitive {
    /// Context length limit for methods
    k: usize,
    pub(crate) ctx_cache: ContextCache<Rc<Path>>,
}

impl KObjectSensitive {
    pub fn new(k: usize) -> Self {
        Self {
            k, 
            ctx_cache: ContextCache::new(),
        }
    }

    pub fn new_context(&mut self, receiver: Rc<CSPath>) -> ContextId {
        let receiver_ctx_id = receiver.cid;
        let receiver_ctx = self.ctx_cache.get_context(receiver_ctx_id).unwrap();
        let callee_ctx = Context::new_k_limited_context(
            &receiver_ctx,
            receiver.path.clone(),
            self.k,
        );
        let callee_ctx_id = self.ctx_cache.get_context_id(&callee_ctx);
        callee_ctx_id
    }
}

impl ContextStrategy for KObjectSensitive {
    type E = Rc<Path>;

    fn empty_context(&self) -> Rc<Context<Rc<Path>>> {
        Context::new_empty()
    }
    
    fn get_context_id(&mut self, context: &Rc<Context<Rc<Path>>>) -> ContextId {
        self.ctx_cache.get_context_id(context)
    } 

    fn get_context_by_id(&self, context_id: ContextId) -> Rc<Context<Rc<Path>>> {
        self.ctx_cache.get_context(context_id).unwrap_or(Context::new_empty())
    }  

    fn get_empty_context_id(&mut self) -> ContextId {
        self.get_context_id(&Context::new_empty())
    }

    fn new_instance_call_context(
        &mut self,
        _callsite: &Rc<CSCallSite>,
        receiver: Option<&Rc<CSPath>>,
        _callee: FuncId,
    ) -> Option<ContextId> {
        if let Some(cs_path) = receiver {
            Some(self.new_context(cs_path.clone()))
        } else {
            None
        }
    }

    fn new_static_call_context(&mut self, callsite: &Rc<CSCallSite>, _callee: FuncId) -> ContextId {
        // use the same context as the caller function
        callsite.func.cid
    }
}


// A simple hybrid context sensitive approach, which analyzes instance-invoked methods in a object-sensitive way 
// and statically invoked functions in a callsite-sensitive way
pub struct SimpleHybridContextSensitive {
    /// Context length limit for methods
    k: usize,
    pub(crate) ctx_cache: ContextCache<HybridCtxElem>,
}

impl SimpleHybridContextSensitive {
    pub fn new(k: usize) -> Self {
        Self {
            k, 
            ctx_cache: ContextCache::new(),
        }
    }

    pub fn new_instance_call_context(&mut self, receiver: Rc<CSPath>) -> ContextId {
        let receiver_ctx_id = receiver.cid;
        let receiver_ctx = self.ctx_cache.get_context(receiver_ctx_id).unwrap();
        let callee_ctx = Context::new_k_limited_context(
            &receiver_ctx,
            HybridCtxElem::Object(receiver.path.clone()),
            self.k,
        );
        let callee_ctx_id = self.ctx_cache.get_context_id(&callee_ctx);
        callee_ctx_id
    }

    pub fn new_static_call_context(&mut self, callsite: &Rc<CSCallSite>) -> ContextId {
        let caller_ctx_id = callsite.func.cid;
        let caller_ctx = self.ctx_cache.get_context(caller_ctx_id).unwrap();
        let callee_ctx = Context::new_k_limited_context(
            &caller_ctx,
            HybridCtxElem::CallSite(callsite.into()),
            self.k,
        );
        let callee_ctx_id = self.ctx_cache.get_context_id(&callee_ctx);
        callee_ctx_id
    }

}

impl ContextStrategy for SimpleHybridContextSensitive {
    type E = HybridCtxElem;

    fn empty_context(&self) -> Rc<Context<HybridCtxElem>> {
        Context::new_empty()
    }
    
    fn get_context_id(&mut self, context: &Rc<Context<HybridCtxElem>>) -> ContextId {
        self.ctx_cache.get_context_id(context)
    } 

    fn get_context_by_id(&self, context_id: ContextId) -> Rc<Context<HybridCtxElem>> {
        self.ctx_cache.get_context(context_id).unwrap_or(Context::new_empty())
    }  

    fn get_empty_context_id(&mut self) -> ContextId {
        self.get_context_id(&Context::new_empty())
    }

    fn new_instance_call_context(
        &mut self,
        _callsite: &Rc<CSCallSite>,
        receiver: Option<&Rc<CSPath>>,
        _callee: FuncId,
    ) -> Option<ContextId> {
        if let Some(cs_path) = receiver {
            Some(self.new_instance_call_context(cs_path.clone()))
        } else {
            None
        }
    }

    fn new_static_call_context(&mut self, callsite: &Rc<CSCallSite>, _callee: FuncId) -> ContextId {
        // use the same context as the caller function
        self.new_static_call_context(callsite)
    }
}


/// Call-site-sensitive context strategy that applies the RCEUS context-augmentation
/// algorithm to precision-critical callees, and falls back to plain k-cfa for
/// non-PC callees (or PC callees whose caller has no PFG entry).
pub struct RCEUSCallSiteSensitive {
    inner: KCallSiteSensitive,
    cs_funcs: HashSet<FuncId>,
    func_pfg_map: HashMap<FuncId, FuncPFG>,
    /// `--rceus --selective-cs` (RCEUS-SEL). A precision-critical callee still
    /// gets the RCEUS-augmented context; a non-critical callee is given the
    /// empty context instead of the k-limited one plain RCEUS would use. Plain
    /// RCEUS keeps this `false`, so every non-critical callee is k-limited.
    selective: bool,
    /// Library-ablation mode (RCEUS_LIB_MODE). When `Some`, the pre-analysis is
    /// skipped: `cs_funcs` is the library-function set, and a callsite is a flow
    /// entry iff its caller is not in this set (the user->library boundary).
    library_funcs: Option<HashSet<FuncId>>,
}

impl RCEUSCallSiteSensitive {
    pub fn new(k: usize) -> Self {
        Self {
            inner: KCallSiteSensitive::new(k),
            cs_funcs: HashSet::new(),
            func_pfg_map: HashMap::new(),
            selective: false,
            library_funcs: None,
        }
    }

    /// Library-ablation context: like `rceus_context`, but a callsite is a flow
    /// entry iff its caller is not a library function (the user->library
    /// boundary), rather than by the PFG's `is_cs_callsite`.
    fn library_context(
        inner: &mut KCallSiteSensitive,
        callsite: &Rc<CSCallSite>,
        library_funcs: &HashSet<FuncId>,
    ) -> ContextId {
        let caller_ctx = inner.get_context_by_id(callsite.func.cid);
        let caller_ctx_elem = &caller_ctx.context_elems;
        let flow_entry = if !library_funcs.contains(&callsite.func.func_id)
            || caller_ctx_elem.is_empty()
        {
            // caller is not library (or has no context of its own): the flow
            // enters the library here.
            callsite.into()
        } else {
            caller_ctx_elem.first().unwrap().clone()
        };
        let mut new_callee_ctx_elem = vec![flow_entry];
        let callee_ctx = Context::new_k_limited_context(&caller_ctx, callsite.into(), inner.k);
        new_callee_ctx_elem.extend(callee_ctx.context_elems.iter().cloned());
        let new_callee_ctx = Rc::new(Context { context_elems: new_callee_ctx_elem });
        inner.ctx_cache.get_context_id(&new_callee_ctx)
    }

    /// RCEUS-SEL: as [`new`], but non-critical callees are context-insensitive.
    pub fn new_selective(k: usize) -> Self {
        Self { selective: true, ..Self::new(k) }
    }

    /// Apply the RCEUS context-augmentation algorithm using the caller's PFG.
    /// The first context element is forced to a "flow-entry" callsite, then the
    /// k-limited tail is appended.
    ///
    /// Takes `&mut KCallSiteSensitive` rather than `&mut self` so callers can
    /// hold an immutable borrow of `self.func_pfg_map` simultaneously (disjoint
    /// field borrow).
    fn rceus_context(
        inner: &mut KCallSiteSensitive,
        callsite: &Rc<CSCallSite>,
        caller_pfg: &FuncPFG,
    ) -> ContextId {
        let caller_ctx = inner.get_context_by_id(callsite.func.cid);
        let caller_ctx_elem = &caller_ctx.context_elems;
        let callsite_location = callsite.location;

        // This callsite is the flow entry unless the caller is already inside a
        // precision-critical flow and propagates its own flow entry. That holds
        // only when the callsite lies on the caller's arg→return path
        // (is_cs_callsite) AND the caller actually carries a context. A
        // precision-critical caller reached as the root/entry instance has an
        // empty context and thus no flow entry to inherit, so the flow enters here.
        let flow_entry = if !caller_pfg.is_cs_callsite(&callsite_location)
            || caller_ctx_elem.is_empty()
        {
            // callsite_location ⇒ 𝑓 ∉ CTXFuncs (or caller has no context of its
            // own): this callsite is the flow entry.
            callsite.into()
        } else {
            // The first element of the caller context is the flow-entry callsite
            // from RCEUS; the guard above makes this unwrap safe.
            caller_ctx_elem.first().unwrap().clone()
        };

        let mut new_callee_ctx_elem = vec![flow_entry];
        let callee_ctx = Context::new_k_limited_context(&caller_ctx, callsite.into(), inner.k);
        new_callee_ctx_elem.extend(callee_ctx.context_elems.iter().cloned());
        let new_callee_ctx = Rc::new(Context { context_elems: new_callee_ctx_elem });
        inner.ctx_cache.get_context_id(&new_callee_ctx)
    }
}

impl ContextStrategy for RCEUSCallSiteSensitive {
    type E = BaseCallSite;

    fn empty_context(&self) -> Rc<Context<BaseCallSite>> { self.inner.empty_context() }
    fn get_empty_context_id(&mut self) -> ContextId { self.inner.get_empty_context_id() }
    fn get_context_id(&mut self, context: &Rc<Context<BaseCallSite>>) -> ContextId {
        self.inner.get_context_id(context)
    }
    fn get_context_by_id(&self, context_id: ContextId) -> Rc<Context<BaseCallSite>> {
        self.inner.get_context_by_id(context_id)
    }
    fn get_context_iter(&self) -> Option<Iter<'_, Rc<Context<BaseCallSite>>, ContextId>> {
        self.inner.get_context_iter()
    }

    fn new_static_call_context(&mut self, callsite: &Rc<CSCallSite>, callee: FuncId) -> ContextId {
        if self.cs_funcs.contains(&callee) {
            // Specially-handled callee: in cs_funcs but has no PFG body (its
            // effect is summarised inline as arg->result edges in the caller's
            // PFG). Its points-to is context-independent, so give it the empty
            // context rather than a flow-entry callsite context.
            if !self.func_pfg_map.contains_key(&callee) {
                return self.inner.get_empty_context_id();
            }
            if let Some(lib) = self.library_funcs.as_ref() {
                return Self::library_context(&mut self.inner, callsite, lib);
            }
            if let Some(caller_pfg) = self.func_pfg_map.get(&callsite.func.func_id) {
                return Self::rceus_context(&mut self.inner, callsite, caller_pfg);
            }
        }
        // Non-critical callee: RCEUS-SEL makes it context-insensitive; plain
        // RCEUS keeps it k-limited.
        if self.selective {
            return self.inner.get_empty_context_id();
        }
        self.inner.new_static_call_context(callsite, callee)
    }

    fn new_instance_call_context(
        &mut self,
        callsite: &Rc<CSCallSite>,
        receiver: Option<&Rc<CSPath>>,
        callee: FuncId,
    ) -> Option<ContextId> {
        if self.cs_funcs.contains(&callee) {
            // Specially-handled callee (in cs_funcs, no PFG body): context-
            // independent inline summary, so give it the empty context.
            if !self.func_pfg_map.contains_key(&callee) {
                return Some(self.inner.get_empty_context_id());
            }
            if let Some(lib) = self.library_funcs.as_ref() {
                return Some(Self::library_context(&mut self.inner, callsite, lib));
            }
            if let Some(caller_pfg) = self.func_pfg_map.get(&callsite.func.func_id) {
                return Some(Self::rceus_context(&mut self.inner, callsite, caller_pfg));
            }
        }
        if self.selective {
            return Some(self.inner.get_empty_context_id());
        }
        self.inner.new_instance_call_context(callsite, receiver, callee)
    }

    fn with_stack_filter<F: SFReachable>(&mut self, stack_filter: &mut StackFilter<F>)
    where
        F: Copy + Into<FuncId> + std::cmp::Eq + std::hash::Hash,
    {
        self.inner.with_stack_filter(stack_filter);
    }

    fn set_prec_crit_fn_ident_data(&mut self, cs_funcs: HashSet<FuncId>, func_pfg_map: HashMap<FuncId, FuncPFG>) {
        self.cs_funcs = cs_funcs;
        self.func_pfg_map = func_pfg_map;
    }

    fn set_library_mode(&mut self, library_funcs: HashSet<FuncId>) {
        self.cs_funcs = library_funcs.clone();
        self.library_funcs = Some(library_funcs);
    }

    fn cs_funcs(&self) -> Option<&HashSet<FuncId>> {
        Some(&self.cs_funcs)
    }
}


/// Selective context sensitivity (`--selective-cs`).
///
/// Plain k-callsite sensitivity, but spent only where the pre-analysis says it
/// buys precision: a callee in `cs_funcs` gets the same k-limited callsite
/// context `KCallSiteSensitive` would give it, and every other callee is handed
/// the empty context, i.e. analysed context-insensitively.
///
/// This shares RCEUS's precision-critical function identification and differs
/// from [`RCEUSCallSiteSensitive`] only in what a critical callee's context is:
/// RCEUS augments it with a flow-entry element derived from the caller's PFG,
/// whereas this strategy leaves the k-limited context untouched. The PFG map is
/// therefore not needed and is dropped on arrival.
///
/// Both the instance and the static case use *callsite* contexts -- selective-cs
/// is a call-site-sensitive analysis, so a receiver never contributes a context
/// element.
pub struct SelectiveCallSiteSensitive {
    inner: KCallSiteSensitive,
    cs_funcs: HashSet<FuncId>,
}

impl SelectiveCallSiteSensitive {
    pub fn new(k: usize) -> Self {
        Self {
            inner: KCallSiteSensitive::new(k),
            cs_funcs: HashSet::new(),
        }
    }

    /// The context for a non-critical callee: empty, so all of its callsites
    /// share one context. Resolved through the cache rather than hardcoding id 0
    /// so it stays correct whatever order contexts are interned in.
    fn insensitive_context(&mut self) -> ContextId {
        self.inner.get_empty_context_id()
    }
}

impl ContextStrategy for SelectiveCallSiteSensitive {
    type E = BaseCallSite;

    fn empty_context(&self) -> Rc<Context<BaseCallSite>> { self.inner.empty_context() }
    fn get_empty_context_id(&mut self) -> ContextId { self.inner.get_empty_context_id() }
    fn get_context_id(&mut self, context: &Rc<Context<BaseCallSite>>) -> ContextId {
        self.inner.get_context_id(context)
    }
    fn get_context_by_id(&self, context_id: ContextId) -> Rc<Context<BaseCallSite>> {
        self.inner.get_context_by_id(context_id)
    }
    fn get_context_iter(&self) -> Option<Iter<'_, Rc<Context<BaseCallSite>>, ContextId>> {
        self.inner.get_context_iter()
    }

    fn new_static_call_context(&mut self, callsite: &Rc<CSCallSite>, callee: FuncId) -> ContextId {
        if self.cs_funcs.contains(&callee) {
            self.inner.new_static_call_context(callsite, callee)
        } else {
            self.insensitive_context()
        }
    }

    fn new_instance_call_context(
        &mut self,
        callsite: &Rc<CSCallSite>,
        _receiver: Option<&Rc<CSPath>>,
        callee: FuncId,
    ) -> Option<ContextId> {
        if self.cs_funcs.contains(&callee) {
            // Deliberately the callsite context, not the receiver's.
            Some(self.inner.new_context(callsite))
        } else {
            Some(self.insensitive_context())
        }
    }

    fn with_stack_filter<F: SFReachable>(&mut self, stack_filter: &mut StackFilter<F>)
    where
        F: Copy + Into<FuncId> + std::cmp::Eq + std::hash::Hash,
    {
        self.inner.with_stack_filter(stack_filter);
    }

    fn set_prec_crit_fn_ident_data(&mut self, cs_funcs: HashSet<FuncId>, _func_pfg_map: HashMap<FuncId, FuncPFG>) {
        self.cs_funcs = cs_funcs;
    }

    fn cs_funcs(&self) -> Option<&HashSet<FuncId>> {
        Some(&self.cs_funcs)
    }
}


/// RCEUS with redundant flow-entry callsite merging (`--rceus-m`).
///
/// Identical to [`RCEUSCallSiteSensitive`] except for the label given to a
/// flow-entry callsite. RCEUS labels a flow entry with the callsite itself, so
/// two callsites handing a callee the very same pointers still induce two
/// contexts. This strategy instead labels each flow entry with the canonical
/// member of its redundant group -- the smallest-bb callsite among those in the
/// caller that target the same callee and whose flowing arguments share
/// backward roots -- so those duplicate contexts collapse into one.
///
/// The groups are computed in the pre-analysis and carried on each caller's
/// [`FuncPFG::flow_entry_merge`]; here we only consult them. Which functions are
/// precision critical is unaffected.
pub struct RCEUSMergeCallSiteSensitive {
    inner: KCallSiteSensitive,
    cs_funcs: HashSet<FuncId>,
    func_pfg_map: HashMap<FuncId, FuncPFG>,
}

impl RCEUSMergeCallSiteSensitive {
    pub fn new(k: usize) -> Self {
        Self {
            inner: KCallSiteSensitive::new(k),
            cs_funcs: HashSet::new(),
            func_pfg_map: HashMap::new(),
        }
    }

    /// As `RCEUSCallSiteSensitive::rceus_context`, but a flow-entry callsite is
    /// labelled by its group's canonical callsite.
    fn rceus_merge_context(
        inner: &mut KCallSiteSensitive,
        callsite: &Rc<CSCallSite>,
        caller_pfg: &FuncPFG,
        callee: FuncId,
    ) -> ContextId {
        let caller_ctx = inner.get_context_by_id(callsite.func.cid);
        let caller_ctx_elem = &caller_ctx.context_elems;
        let callsite_location = callsite.location;

        let flow_entry = if !caller_pfg.is_cs_callsite(&callsite_location)
            || caller_ctx_elem.is_empty()
        {
            // This callsite is the flow entry: either it is not a cs_callsite, or
            // the caller is a root/entry instance with an empty context and thus
            // no flow entry to inherit. Label it with the canonical member of its
            // redundant group; callsites that are their own representative keep
            // their own location, exactly as in RCEUS.
            let mut elem: BaseCallSite = callsite.into();
            elem.location = caller_pfg.canonical_flow_entry(&callsite_location, callee);
            elem
        } else {
            // Flow-through: inherit the caller's flow entry, which is already
            // canonical because it was labelled when that entry was created.
            caller_ctx_elem.first().unwrap().clone()
        };

        let mut new_callee_ctx_elem = vec![flow_entry];
        let callee_ctx = Context::new_k_limited_context(&caller_ctx, callsite.into(), inner.k);
        new_callee_ctx_elem.extend(callee_ctx.context_elems.iter().cloned());
        let new_callee_ctx = Rc::new(Context { context_elems: new_callee_ctx_elem });
        inner.ctx_cache.get_context_id(&new_callee_ctx)
    }
}

impl ContextStrategy for RCEUSMergeCallSiteSensitive {
    type E = BaseCallSite;

    fn empty_context(&self) -> Rc<Context<BaseCallSite>> { self.inner.empty_context() }
    fn get_empty_context_id(&mut self) -> ContextId { self.inner.get_empty_context_id() }
    fn get_context_id(&mut self, context: &Rc<Context<BaseCallSite>>) -> ContextId {
        self.inner.get_context_id(context)
    }
    fn get_context_by_id(&self, context_id: ContextId) -> Rc<Context<BaseCallSite>> {
        self.inner.get_context_by_id(context_id)
    }
    fn get_context_iter(&self) -> Option<Iter<'_, Rc<Context<BaseCallSite>>, ContextId>> {
        self.inner.get_context_iter()
    }

    fn new_static_call_context(&mut self, callsite: &Rc<CSCallSite>, callee: FuncId) -> ContextId {
        if self.cs_funcs.contains(&callee) {
            // Specially-handled callee: in cs_funcs but has no PFG body (its
            // effect is summarised inline as arg->result edges in the caller's
            // PFG). Its points-to is context-independent, so give it the empty
            // context, exactly as RCEUS does.
            if !self.func_pfg_map.contains_key(&callee) {
                return self.inner.get_empty_context_id();
            }
            if let Some(caller_pfg) = self.func_pfg_map.get(&callsite.func.func_id) {
                return Self::rceus_merge_context(&mut self.inner, callsite, caller_pfg, callee);
            }
        }
        self.inner.new_static_call_context(callsite, callee)
    }

    fn new_instance_call_context(
        &mut self,
        callsite: &Rc<CSCallSite>,
        receiver: Option<&Rc<CSPath>>,
        callee: FuncId,
    ) -> Option<ContextId> {
        if self.cs_funcs.contains(&callee) {
            // Specially-handled callee (in cs_funcs, no PFG body): context-
            // independent inline summary, so give it the empty context.
            if !self.func_pfg_map.contains_key(&callee) {
                return Some(self.inner.get_empty_context_id());
            }
            if let Some(caller_pfg) = self.func_pfg_map.get(&callsite.func.func_id) {
                return Some(Self::rceus_merge_context(&mut self.inner, callsite, caller_pfg, callee));
            }
        }
        self.inner.new_instance_call_context(callsite, receiver, callee)
    }

    fn with_stack_filter<F: SFReachable>(&mut self, stack_filter: &mut StackFilter<F>)
    where
        F: Copy + Into<FuncId> + std::cmp::Eq + std::hash::Hash,
    {
        self.inner.with_stack_filter(stack_filter);
    }

    fn set_prec_crit_fn_ident_data(&mut self, cs_funcs: HashSet<FuncId>, func_pfg_map: HashMap<FuncId, FuncPFG>) {
        self.cs_funcs = cs_funcs;
        self.func_pfg_map = func_pfg_map;
    }

    fn cs_funcs(&self) -> Option<&HashSet<FuncId>> {
        Some(&self.cs_funcs)
    }
}

// ===========================================================================
// EXPERIMENTAL (`--rceus-ap`): argument-provenance-qualified flow-entry.
//
// Refines RCEUS's single flow-entry element [ℓ] into
//   [ Site(ℓ), ParamProv(p, {entry-args})... ]
// separating precision-critical callees by WHICH argument(s) of the flow-entry
// callsite their data originates from. Entry-arg indices are the ORIGIN
// positions at the flow-entry callsite (provenance), carried unchanged down the
// chain, and each set is kept ascending so {#1,#2} and {#2,#1} intern to the
// same context (no duplicated contexts).
// ===========================================================================

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ProvElem {
    Site(BaseCallSite),
    /// (callee parameter ordinal, sorted-ascending set of flow-entry arg indices)
    ParamProv(u32, Vec<u32>),
}
impl ContextElement for ProvElem {}

/// A logical actual-argument source at a lowered MIR callsite. `Whole(i)` is
/// raw MIR argument i; `TupleField(i, f)` is field f of raw tuple argument i.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum ArgSlot {
    Whole(u32),
    TupleField(u32, u32),
}

type ArgParamReach = HashMap<FuncId, HashMap<Location, Vec<(ArgSlot, Vec<u32>)>>>;

pub struct RCEUSArgProvSensitive {
    ctx_cache: ContextCache<ProvElem>,
    cs_funcs: HashSet<FuncId>,
    func_pfg_map: HashMap<FuncId, FuncPFG>,
    /// caller func -> callsite loc -> [(arg index, caller param ordinals reaching it)]
    arg_param_reach: ArgParamReach,
    /// ABLATION (env ARGPROV_NOPROV=<name substr>): flow-entry callees for which
    /// provenance seeding is suppressed -- they get the plain RCEUS `[Site]`
    /// context, so their whole flow-through subtree carries no provenance. Used to
    /// measure how much precision a specific flow entry's provenance contributes.
    noprov_callees: HashSet<FuncId>,
    /// ABLATION (env ARGPROV_NOPROV_SITE): if non-empty, `noprov_callees`
    /// suppression only applies when the context's flow-entry Site's function is
    /// in this set -- i.e. ablate a callee's provenance ONLY under specific flow
    /// entries. Empty = apply everywhere.
    noprov_sites: HashSet<FuncId>,
}

/// The callee's flow-carrying parameter indices (its `param_with_flow`), used to
/// seed its identity provenance. `argprov_context` is only reached for PFG
/// callees (the dispatch sends specially-handled/no-PFG callees straight to the
/// empty context), so a missing PFG yields no params.
fn callee_flow_params(func_pfg_map: &HashMap<FuncId, FuncPFG>, callee: FuncId) -> Vec<u32> {
    func_pfg_map
        .get(&callee)
        .map(|pfg| pfg.param_with_flow.iter().map(|p| *p as u32).collect())
        .unwrap_or_default()
}

impl RCEUSArgProvSensitive {
    pub fn new(_k: usize) -> Self {
        Self {
            ctx_cache: ContextCache::new(),
            cs_funcs: HashSet::new(),
            func_pfg_map: HashMap::new(),
            arg_param_reach: HashMap::new(),
            noprov_callees: HashSet::new(),
            noprov_sites: HashSet::new(),
        }
    }

    /// For a function's PFG: which caller parameters reach each callsite argument
    /// (reverse reachability). Computed once in pre-analysis.
    fn build_arg_param_reach(pfg: &FuncPFG) -> HashMap<Location, Vec<(ArgSlot, Vec<u32>)>> {
        let mut node_of: HashMap<Rc<Path>, _> = HashMap::new();
        let mut tuple_fields: HashMap<Rc<Path>, Vec<(u32, _)>> = HashMap::new();
        for n in pfg.graph.node_indices() {
            let path = pfg.graph[n].path.clone();
            if let PathEnum::QualifiedPath { base, projection } = &path.value {
                if let [PathSelector::Field(field)] = projection.as_slice() {
                    tuple_fields
                        .entry(base.clone())
                        .or_default()
                        .push((*field as u32, n));
                }
            }
            node_of.insert(path, n);
        }

        let reaching_params = |start: petgraph::graph::NodeIndex| {
            let mut seen: HashSet<_> = HashSet::new();
            let mut q: VecDeque<_> = VecDeque::new();
            q.push_back(start);
            let mut params: BTreeSet<u32> = BTreeSet::new();
            while let Some(x) = q.pop_front() {
                if !seen.insert(x) { continue; }
                if let PathEnum::Parameter { ordinal, .. } = pfg.graph[x].path.value {
                    params.insert(ordinal as u32);
                }
                for e in pfg.graph.edges_directed(x, petgraph::Direction::Incoming) {
                    q.push_back(e.source());
                }
            }
            params.into_iter().collect::<Vec<_>>()
        };

        let mut out: HashMap<Location, Vec<(ArgSlot, Vec<u32>)>> = HashMap::new();
        for (loc, (args, _dest)) in &pfg.callsite_to_locals {
            let mut per_call: Vec<(ArgSlot, Vec<u32>)> = Vec::new();
            for (arg_idx, arg_path) in args {
                if let Some(&start) = node_of.get(arg_path) {
                    let params = reaching_params(start);
                    if !params.is_empty() {
                        per_call.push((ArgSlot::Whole(*arg_idx as u32), params));
                    }
                }

                if let Some(fields) = tuple_fields.get(arg_path) {
                    for &(field, start) in fields {
                        let params = reaching_params(start);
                        if !params.is_empty() {
                            per_call.push((
                                ArgSlot::TupleField(*arg_idx as u32, field),
                                params,
                            ));
                        }
                    }
                }
            }
            if !per_call.is_empty() {
                out.insert(*loc, per_call);
            }
        }
        out
    }

    fn argprov_context(
        cache: &mut ContextCache<ProvElem>,
        func_pfg_map: &HashMap<FuncId, FuncPFG>,
        arg_param_reach: &ArgParamReach,
        noprov_callees: &HashSet<FuncId>,
        noprov_sites: &HashSet<FuncId>,
        callsite: &Rc<CSCallSite>,
        caller_pfg: &FuncPFG,
        callee: FuncId,
    ) -> ContextId {
        let caller_func = callsite.func.func_id;
        let loc = callsite.location;
        let caller_ctx = cache.get_context(callsite.func.cid).unwrap_or(Context::new_empty());
        // A PFG flow-through site can inherit only when the caller actually has
        // a flow-entry context. A precision-critical root/entry function starts
        // a fresh chain even when this location lies on its param-to-return path.
        let is_flow_entry = !caller_pfg.is_cs_callsite(&loc)
            || caller_ctx.context_elems.is_empty();

        let mut elems: Vec<ProvElem> = Vec::new();

        if is_flow_entry {
            // Case 2 (flow entry): the callee's params ARE the entry args
            // (identity provenance). A callee with no flow-carrying params is a
            // specially-handled function with context-independent points-to, so
            // it gets the empty context -- exactly RCEUS's treatment of it.
            let mut params = callee_flow_params(func_pfg_map, callee);
            params.sort();
            params.dedup();
            if params.is_empty() {
                return cache.get_context_id(&Context::new_empty());
            }
            elems.push(ProvElem::Site(BaseCallSite::new(caller_func, loc)));
            // ABLATION: suppress provenance for this flow-entry callee -> plain
            // RCEUS `[Site]`; the whole flow-through subtree then carries none.
            if noprov_callees.contains(&callee)
                && (noprov_sites.is_empty() || noprov_sites.contains(&caller_func)) {
                let ctx = Rc::new(Context { context_elems: elems });
                return cache.get_context_id(&ctx);
            }
            for p in params {
                elems.push(ProvElem::ParamProv(p, vec![p]));
            }
        } else {
            // flow-through: inherit the flow-entry site; map each callee param to
            // entry-args by tracing the callsite arg back through the caller's
            // provenance (initial arg number, not the current position).
            let site = match caller_ctx.context_elems.first() {
                Some(ProvElem::Site(s)) => *s,
                _ => BaseCallSite::new(caller_func, loc),
            };
            elems.push(ProvElem::Site(site));
            // ABLATION: suppress provenance for this callee -> plain RCEUS
            // `[Site]` (inherited flow entry, no ParamProv appended).
            if noprov_callees.contains(&callee)
                && (noprov_sites.is_empty() || noprov_sites.contains(&site.func)) {
                let ctx = Rc::new(Context { context_elems: elems });
                return cache.get_context_id(&ctx);
            }
            // Provenance refinement applies only to callees with a PFG. A
            // specially-handled callee (no PFG) has its effect summarised inline
            // as arg->result edges in the caller's PFG -- there is no callee body
            // or param-ordinal space to refine -- so it just follows RCEUS: the
            // bare `[Site]` (falls through to the normal return below).
            if let Some(cpfg) = func_pfg_map.get(&callee) {
                let mut caller_map: HashMap<u32, Vec<u32>> = HashMap::new();
                for e in &caller_ctx.context_elems {
                    if let ProvElem::ParamProv(p, s) = e { caller_map.insert(*p, s.clone()); }
                }
                // Fold the caller's per-parameter provenance onto each CALLER
                // ARGUMENT: arg_prov[a] = union of entry-arg sets over the caller
                // parameters that reach argument a.
                let mut arg_prov: HashMap<ArgSlot, BTreeSet<u32>> = HashMap::new();
                if let Some(argreach) = arg_param_reach.get(&caller_func).and_then(|m| m.get(&loc)) {
                    for (slot, caller_params) in argreach {
                        let entry = arg_prov.entry(*slot).or_default();
                        for cp in caller_params {
                            if let Some(s) = caller_map.get(cp) {
                                for e in s { entry.insert(*e); }
                            }
                        }
                    }
                }
                // Map logical actuals onto CALLEE PARAMETER ordinals. Ordinary
                // calls are positional. Fn* lowering uses `(receiver, tuple)`:
                // closure bodies receive receiver + tuple fields, function
                // items/pointers receive tuple fields only, and an actual trait
                // implementation method consumes the raw pair.
                // Only callee parameters that reach the callee's return carry
                // provenance (mirrors the Case-2 seed): a parameter that does not
                // reach g's return produces "dead" provenance that never reaches
                // an output boundary, so tracking it would add contexts without
                // refining any return/callee points-to set.
                let is_static = caller_pfg.static_callsites.contains(&loc);
                let is_fn_lowered = caller_pfg.fn_ptr_def_callsites.contains(&loc)
                    || caller_pfg.closure_dyn_callsites.contains(&loc);
                let empty: BTreeSet<u32> = BTreeSet::new();
                let mut callee_params: Vec<u32> =
                    cpfg.param_with_flow.iter().map(|x| *x as u32).collect();
                callee_params.sort();
                callee_params.dedup();
                let mut prov: Vec<(u32, Vec<u32>)> = Vec::new();
                for cp in callee_params {
                    let (primary, fallback) = if is_static || !is_fn_lowered {
                        (ArgSlot::Whole(cp), None)
                    } else if cpfg.has_self_parameter {
                        // An actual Fn/FnMut/FnOnce implementation consumes the
                        // raw `(receiver, tuple)` MIR signature.
                        (ArgSlot::Whole(cp), None)
                    } else if cpfg.is_closure_body {
                        // Closure body: formal 1 is the receiver; formals 2..N
                        // are fields 0.. of the lowered tuple argument.
                        if cp == 1 {
                            (ArgSlot::Whole(1), None)
                        } else {
                            (ArgSlot::TupleField(2, cp - 2), Some(ArgSlot::Whole(2)))
                        }
                    } else {
                        // Function item/pointer reached through Fn*: the receiver
                        // selects the target but is not passed to it. Formal i is
                        // field i-1 of the tuple argument.
                        (ArgSlot::TupleField(2, cp - 1), Some(ArgSlot::Whole(2)))
                    };
                    // Whole-tuple provenance is a conservative fallback for a
                    // tuple whose construction/projections are unavailable.
                    let set = arg_prov
                        .get(&primary)
                        .or_else(|| fallback.and_then(|slot| arg_prov.get(&slot)))
                        .unwrap_or(&empty);
                    if !set.is_empty() {
                        prov.push((cp, set.iter().copied().collect()));
                    }
                }
                prov.sort();
                for (p, s) in prov {
                    elems.push(ProvElem::ParamProv(p, s));
                }
            }
        }

        // Return RCEUS's flow-entry Site plus any argprov provenance appended
        // above. When no provenance was added this is a bare `[Site]` -- the pure
        // RCEUS context (a Case-3 flow-through of a local-origin value, or a
        // no-PFG specially-handled callee): the flow-entry Site still separates
        // the call per-entry exactly as RCEUS would.
        let ctx = Rc::new(Context { context_elems: elems });
        cache.get_context_id(&ctx)
    }
}

impl ContextStrategy for RCEUSArgProvSensitive {
    type E = ProvElem;

    fn empty_context(&self) -> Rc<Context<ProvElem>> { Context::new_empty() }
    fn get_empty_context_id(&mut self) -> ContextId {
        self.ctx_cache.get_context_id(&Context::new_empty())
    }
    fn get_context_id(&mut self, context: &Rc<Context<ProvElem>>) -> ContextId {
        self.ctx_cache.get_context_id(context)
    }
    fn get_context_by_id(&self, context_id: ContextId) -> Rc<Context<ProvElem>> {
        self.ctx_cache.get_context(context_id).unwrap_or(Context::new_empty())
    }
    fn get_context_iter(&self) -> Option<Iter<'_, Rc<Context<ProvElem>>, ContextId>> {
        Some(self.ctx_cache.get_context_iter())
    }

    fn new_static_call_context(&mut self, callsite: &Rc<CSCallSite>, callee: FuncId) -> ContextId {
        if self.cs_funcs.contains(&callee) {
            // A specially-handled callee (no PFG) has its effect inlined into the
            // caller's PFG, so its own context never refines anything: RCEUS gives
            // it the empty context and argprov appends no provenance -> empty.
            if !self.func_pfg_map.contains_key(&callee) {
                return self.get_empty_context_id();
            }
            if let Some(caller_pfg) = self.func_pfg_map.get(&callsite.func.func_id) {
                return Self::argprov_context(
                    &mut self.ctx_cache, &self.func_pfg_map, &self.arg_param_reach, &self.noprov_callees, &self.noprov_sites,
                    callsite, caller_pfg, callee);
            }
        }
        self.get_empty_context_id()
    }

    fn new_instance_call_context(
        &mut self,
        callsite: &Rc<CSCallSite>,
        _receiver: Option<&Rc<CSPath>>,
        callee: FuncId,
    ) -> Option<ContextId> {
        if self.cs_funcs.contains(&callee) {
            // Specially-handled callee (no PFG): empty context (see the static case).
            if !self.func_pfg_map.contains_key(&callee) {
                return Some(self.get_empty_context_id());
            }
            if let Some(caller_pfg) = self.func_pfg_map.get(&callsite.func.func_id) {
                return Some(Self::argprov_context(
                    &mut self.ctx_cache, &self.func_pfg_map, &self.arg_param_reach, &self.noprov_callees, &self.noprov_sites,
                    callsite, caller_pfg, callee));
            }
        }
        Some(self.get_empty_context_id())
    }

    fn set_prec_crit_fn_ident_data(&mut self, cs_funcs: HashSet<FuncId>, func_pfg_map: HashMap<FuncId, FuncPFG>) {
        let mut reach: ArgParamReach = HashMap::new();
        for (f, pfg) in &func_pfg_map {
            let m = Self::build_arg_param_reach(pfg);
            if !m.is_empty() { reach.insert(*f, m); }
        }
        self.cs_funcs = cs_funcs;
        self.func_pfg_map = func_pfg_map;
        self.arg_param_reach = reach;
    }

    fn set_noprov_callees(&mut self, callees: HashSet<FuncId>) {
        self.noprov_callees = callees;
    }

    fn set_noprov_sites(&mut self, sites: HashSet<FuncId>) {
        self.noprov_sites = sites;
    }
}

// ===========================================================================
// EXPERIMENTAL (`--rceus-m --rceus-ap`): merged flow-entry with
// argument-provenance qualification.
//
// This is deliberately a separate context strategy. RCEUS-M and RCEUS-AP keep
// their existing behavior. At a new flow entry this strategy first replaces
// the callsite location with RCEUS-M's canonical group representative, then
// applies RCEUS-AP to construct
//   [ Site(canonical(ℓ)), ParamProv(p, {entry-args})... ].
// Flow-through calls retain the inherited canonical Site and only remap AP's
// provenance, exactly as RCEUS-AP normally does.
// ===========================================================================

pub struct RCEUSMergeArgProvSensitive {
    argprov: RCEUSArgProvSensitive,
}

impl RCEUSMergeArgProvSensitive {
    pub fn new(k: usize) -> Self {
        Self { argprov: RCEUSArgProvSensitive::new(k) }
    }

    /// Replace a flow-entry callsite's location with its RCEUS-M representative.
    /// Flow-through callsites are returned unchanged so AP can inherit the Site
    /// already carried by the caller's context.
    fn canonicalize_flow_entry(
        callsite: &Rc<CSCallSite>,
        caller_pfg: &FuncPFG,
        callee: FuncId,
        caller_context_is_empty: bool,
    ) -> Rc<CSCallSite> {
        if caller_pfg.is_cs_callsite(&callsite.location) && !caller_context_is_empty {
            return callsite.clone();
        }

        let canonical = caller_pfg.canonical_flow_entry(&callsite.location, callee);
        if canonical == callsite.location {
            return callsite.clone();
        }

        let mut merged_callsite = callsite.as_ref().clone();
        merged_callsite.location = canonical;
        Rc::new(merged_callsite)
    }

    fn merged_argprov_context(
        cache: &mut ContextCache<ProvElem>,
        func_pfg_map: &HashMap<FuncId, FuncPFG>,
        arg_param_reach: &ArgParamReach,
        noprov_callees: &HashSet<FuncId>,
        noprov_sites: &HashSet<FuncId>,
        callsite: &Rc<CSCallSite>,
        caller_pfg: &FuncPFG,
        callee: FuncId,
    ) -> ContextId {
        let caller_context_is_empty = cache
            .get_context(callsite.func.cid)
            .map_or(true, |ctx| ctx.context_elems.is_empty());
        let merged_callsite = Self::canonicalize_flow_entry(
            callsite,
            caller_pfg,
            callee,
            caller_context_is_empty,
        );
        RCEUSArgProvSensitive::argprov_context(
            cache,
            func_pfg_map,
            arg_param_reach,
            noprov_callees,
            noprov_sites,
            &merged_callsite,
            caller_pfg,
            callee,
        )
    }
}

impl ContextStrategy for RCEUSMergeArgProvSensitive {
    type E = ProvElem;

    fn empty_context(&self) -> Rc<Context<ProvElem>> {
        self.argprov.empty_context()
    }

    fn get_empty_context_id(&mut self) -> ContextId {
        self.argprov.get_empty_context_id()
    }

    fn get_context_id(&mut self, context: &Rc<Context<ProvElem>>) -> ContextId {
        self.argprov.get_context_id(context)
    }

    fn get_context_by_id(&self, context_id: ContextId) -> Rc<Context<ProvElem>> {
        self.argprov.get_context_by_id(context_id)
    }

    fn get_context_iter(&self) -> Option<Iter<'_, Rc<Context<ProvElem>>, ContextId>> {
        self.argprov.get_context_iter()
    }

    fn new_static_call_context(&mut self, callsite: &Rc<CSCallSite>, callee: FuncId) -> ContextId {
        if self.argprov.cs_funcs.contains(&callee) {
            if !self.argprov.func_pfg_map.contains_key(&callee) {
                return self.get_empty_context_id();
            }
            if let Some(caller_pfg) = self.argprov.func_pfg_map.get(&callsite.func.func_id) {
                return Self::merged_argprov_context(
                    &mut self.argprov.ctx_cache,
                    &self.argprov.func_pfg_map,
                    &self.argprov.arg_param_reach,
                    &self.argprov.noprov_callees,
                    &self.argprov.noprov_sites,
                    callsite,
                    caller_pfg,
                    callee,
                );
            }
        }
        self.get_empty_context_id()
    }

    fn new_instance_call_context(
        &mut self,
        callsite: &Rc<CSCallSite>,
        _receiver: Option<&Rc<CSPath>>,
        callee: FuncId,
    ) -> Option<ContextId> {
        if self.argprov.cs_funcs.contains(&callee) {
            if !self.argprov.func_pfg_map.contains_key(&callee) {
                return Some(self.get_empty_context_id());
            }
            if let Some(caller_pfg) = self.argprov.func_pfg_map.get(&callsite.func.func_id) {
                return Some(Self::merged_argprov_context(
                    &mut self.argprov.ctx_cache,
                    &self.argprov.func_pfg_map,
                    &self.argprov.arg_param_reach,
                    &self.argprov.noprov_callees,
                    &self.argprov.noprov_sites,
                    callsite,
                    caller_pfg,
                    callee,
                ));
            }
        }
        Some(self.get_empty_context_id())
    }

    fn set_prec_crit_fn_ident_data(
        &mut self,
        cs_funcs: HashSet<FuncId>,
        func_pfg_map: HashMap<FuncId, FuncPFG>,
    ) {
        self.argprov.set_prec_crit_fn_ident_data(cs_funcs, func_pfg_map);
    }

    fn set_noprov_callees(&mut self, callees: HashSet<FuncId>) {
        self.argprov.set_noprov_callees(callees);
    }

    fn set_noprov_sites(&mut self, sites: HashSet<FuncId>) {
        self.argprov.set_noprov_sites(sites);
    }

    fn cs_funcs(&self) -> Option<&HashSet<FuncId>> {
        self.argprov.cs_funcs()
    }
}
