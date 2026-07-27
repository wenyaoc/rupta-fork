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
use crate::mir::call_site::{BaseCallSite, CSCallSite};
use crate::mir::context::{Context, ContextCache, ContextElement, ContextId, HybridCtxElem};
use crate::mir::function::FuncId;
use crate::mir::path::{CSPath, Path};
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
}

impl RCEUSCallSiteSensitive {
    pub fn new(k: usize) -> Self {
        Self {
            inner: KCallSiteSensitive::new(k),
            cs_funcs: HashSet::new(),
            func_pfg_map: HashMap::new(),
            selective: false,
        }
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