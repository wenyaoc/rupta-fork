# Call Graph of `update_data` — Flow-Entry Merging Worked Example

Reference data for `fig:merge_example` / `fig:merge_cg` in §3-Design of the TOPLAS
paper. Every number here is **measured**, not estimated.

## 1. Provenance

The example is `ModuleCacheEntryInner::update_data` from **wasmtime**:



```
benchmarks/wasmtime/crates/cache/src/lib.rs:163
fn update_data(&self, hash: &str, serialized_data: &[u8]) -> Option<()>
```

The real function reaches its local `mod_cache_path` **six** times (five in the
paper's simplified figure — the sixth is the `warn!(… mod_cache_path.display() …)`
inside the `Err` arm, which the figure elides as `Err(err) => { None }`). The
paper's prose and figure are internally consistent at five; treat the counts as a
simplification of the real function, not as measured values.

Because dumping wasmtime's call graph is expensive, the structure below was
obtained from a **faithful toy replica** (`/tmp/cachetoy`) that reproduces the
pattern exactly — 5 × `PathBuf::deref`, 2 × `Path::display`, 2 ×
`Argument::new_display` — matching the paper's figure. The replica's merge
behaviour matches real wasmtime (same group shapes, `fs_write_atomic` rejected as
`callee-not-cs` in both).

## 2. `update_data`'s direct callees (14)

| callee | flow entry? | outcome |
|---|---|---|
| `std::path::{impl#44}::deref` | yes | **merged, 5→1** (+1 singleton) |
| `std::path::{impl#63}::display` | yes | **merged, 2→1** |
| `core::fmt::rt::{impl#1}::new_display<Display>` | yes | **merged, 2→1** (inexact) |
| `core::fmt::{impl#2}::new_v1<>` | yes | 2 singletons (distinct roots) |
| `std::path::{impl#63}::parent` | yes | singleton |
| `core::option::{impl#0}::unwrap<&Path>` | yes | singleton |
| `cachetoy::fs_write_atomic` (×2) | — | skipped: `callee-not-cs` |
| `std::io::stdio::_print` (×2) | — | skipped: `callee-not-cs` |
| `std::path::{impl#63}::join<&str>` | — | skipped: `callee-not-cs` |
| `std::fs::create_dir_all<&Path>` | — | skipped: `callee-not-cs` |
| `core::result::{impl#0}::is_ok` | — | skipped: `callee-not-cs` |
| `core::result::{impl#0}::ok` | — | skipped: `callee-not-cs` |
| `core::option::{impl#40}::branch<()>` | — | skipped: `callee-not-cs` |
| `core::option::{impl#41}::from_residual<()>` | — | skipped: `callee-not-cs` |

**14 flow-entry callsites → 8 contexts** (6 callsites eliminated). The paper's
figure shows the 9 → 3 subset covering `deref`/`display`/`new_display`.

> `fs_write_atomic` is **not merged** — and not because its arguments differ, but
> because it is not precision-critical at all (`callee-not-cs`), so it never
> receives a context. The merge question never arises for it. This holds in real
> wasmtime too.

## 3. Merge groups

Key = `(callee, [(arg_idx, backward_roots)])` over the callee's `param_with_flow`
positions. Canonical member = smallest `(bb, statement_index)`.

| callee | size | callsites | roots | argument paths |
|---|---|---|---|---|
| `PathBuf::deref` | **5** | bb2, bb7, bb14, bb19, bb26 | `[(1,[4])]` | `local_17, local_22, local_33, local_37, local_44` |
| `Path::display` | **2** | bb3, bb15 | `[(1,[4])]` | `local_16, local_32` |
| `new_display<Display>` | **2** | bb4, bb16 | `[(1,[4])]` | `local_14, local_30` |
| `PathBuf::deref` | 1 | bb0 | `[(1,[0])]` | `local_6` |
| `fmt::new_v1` | 1 | bb5 | `[(1,[2]),(2,[4])]` | `local_9, local_10` |
| `fmt::new_v1` | 1 | bb17 | `[(1,[15]),(2,[4])]` | `local_25, local_26` |
| `Path::parent` | 1 | bb20 | `[(1,[4])]` | `local_36` |
| `Option::unwrap<&Path>` | 1 | bb21 | `[(1,[4])]` | `local_35` |

Two observations that matter for the paper's argument:

1. **The five `deref` arguments are five distinct MIR temporaries**
   (`local_17/22/33/37/44`) that share root `[4]` (= `mod_cache_path`). Comparing
   argument *variables* would find nothing to merge; only root equality does.
2. **The `deref` at bb0 is correctly left alone.** Its root is `[0]`
   (`self.root_path`, from `self.root_path.join(hash)`), a different origin — so
   the equivalence relation separates it from the other five.

The two `new_v1` callsites also stay separate: their first arguments have roots
`[2]` and `[15]` (different format-string argument arrays), so root equality does
not conflate them.

## 4. Call graph under `deref`'s flow-entry callsite

This is why merging pays off — but the relevant count is smaller than the raw
subtree size.

Three different numbers, easy to conflate:

| measure | value |
|---|---|
| CI transitive closure under `deref` | 41 fns, depth 14 |
| …of those, context-sensitive (`cs_funcs`) | 18 |
| **…actually carrying `deref`'s flow-entry context** | **16 fns (deref + 15), depth 10** |

**16 / depth 10 is the number that matters** — it is what a duplicate context
re-analyses. The 41 includes context-insensitive functions analysed once
globally. The 18 is an upper bound: three context-sensitive functions in the
subtree (`fmt::new_const`, `panic_info::internal_constructor`,
`const_ptr::cast<(),()>`) sit in the panic plumbing and are reached through their
*own* flow entries, so duplicating `deref` does not multiply them.

### The call graph rooted at the flow entry (16 functions, depth 10)

```
deref                                       (flow entry, depth 0)
 1  std::path::{impl#63}::new<OsString>
 2  std::ffi::os_str::{impl#54}::as_ref
 3  std::ffi::os_str::{impl#7}::deref
 4  std::ffi::os_str::{impl#5}::index
 5  std::ffi::os_str::{impl#23}::from_inner | std::sys::os_str::bytes::{impl#7}::as_slice
 6  alloc::vec::{impl#8}::deref<u8>
 7  alloc::vec::{impl#1}::as_ptr<u8>        | core::slice::raw::from_raw_parts<u8>
 8  alloc::raw_vec::{impl#2}::ptr<u8>       | core::ptr::slice_from_raw_parts<u8>
 9  core::ptr::const_ptr::{impl#0}::cast<u8,()> | core::ptr::metadata::from_raw_parts<[u8]>
    core::ptr::unique::{impl#3}::as_ptr<u8>
10  core::ptr::non_null::{impl#3}::as_ptr<u8>   <- raw pointer, chain ends
```

The context propagates through the whole abstraction stack
(`PathBuf → Path → OsStr → OsString → Vec → RawVec → Unique → NonNull`) and stops
exactly when it reaches the raw pointer, where there is no further pointer flow to
carry.

### Reference: full context-insensitive closure

The listing below is the *context-insensitive* reachability closure under
`deref` (41 functions, 14 layers). It is **not** the call graph that the flow
entry induces — it additionally contains context-insensitive functions analysed
once globally, and context-sensitive functions reached via their own flow
entries. Members carrying `deref`'s context are marked **[fe]**; compare with the
chain above.



```
PathBuf::deref
 L1  std::path::{impl#63}::new<std::ffi::OsString>   [fe]
 L2  std::ffi::os_str::{impl#54}::as_ref   [fe]
 L3  std::ffi::os_str::{impl#7}::deref   [fe]
 L4  std::ffi::os_str::{impl#5}::index   [fe]
 L5  std::ffi::os_str::{impl#23}::from_inner   [fe]
     std::sys::os_str::bytes::{impl#7}::as_slice   [fe]
 L6  alloc::vec::{impl#8}::deref<u8, Global>   [fe]
 L7  alloc::vec::{impl#1}::as_ptr<u8, Global>   [fe]
     core::slice::raw::from_raw_parts<u8>   [fe]
 L8  alloc::raw_vec::{impl#2}::ptr<u8, Global>   [fe]
     core::ptr::slice_from_raw_parts<u8>   [fe]
     core::slice::raw::from_raw_parts::runtime<u8>
 L9  core::ptr::unique::{impl#3}::as_ptr<u8>   [fe]
     core::ptr::const_ptr::{impl#0}::cast<u8, ()>   [fe]
     core::ptr::metadata::from_raw_parts<[u8]>   [fe]
     core::intrinsics::is_aligned_and_not_null<u8>
     core::intrinsics::is_valid_allocation_size<u8>
     core::panicking::panic_nounwind
 L10 core::ptr::non_null::{impl#3}::as_ptr<u8>   [fe]
     core::ptr::const_ptr::{impl#0}::is_aligned<u8>
     core::ptr::const_ptr::{impl#0}::is_null<u8>
     core::fmt::{impl#2}::new_const
     core::panicking::panic_nounwind_fmt
 L11 core::mem::align_of<u8>
     core::ptr::const_ptr::{impl#0}::is_aligned_to<u8>
     core::ptr::const_ptr::{impl#0}::is_null::runtime_impl
     core::panicking::panic_fmt
     core::panicking::panic_nounwind_fmt::runtime
 L12 core::num::{impl#11}::is_power_of_two
     core::ptr::const_ptr::{impl#0}::is_aligned_to::runtime_impl
     core::ptr::const_ptr::{impl#0}::addr<u8>
     core::intrinsics::{extern#0}::abort
     core::panic::location::{impl#0}::caller
     core::panic::panic_info::{impl#0}::internal_constructor
     core::panicking::panic_fmt::{extern#0}::panic_impl
     core::panicking::panic_nounwind_fmt::runtime::{extern#0}::panic_impl
 L13 core::num::{impl#11}::count_ones
     core::ptr::const_ptr::{impl#0}::addr<()>
     core::intrinsics::{extern#0}::caller_location
 L14 core::intrinsics::{extern#0}::ctpop<u64>
     core::ptr::const_ptr::{impl#0}::cast<(), ()>
```

The spine is the layered-abstraction chain the paper argues about:
`PathBuf → Path → OsStr → OsString → Vec<u8> → RawVec → Unique → NonNull → *const u8`.
Layers 9–14 are panic/alignment plumbing pulled in by the raw-pointer operations.

## 5. Internal layers of the other two

| callee | direct callees | transitive | note |
|---|---|---|---|
| `Path::display` | 0 | 0 | leaf |
| `new_display<Display>` | 1 | 1 | `core::fmt::rt::{impl#1}::new<Display>` |

So the memory/time saving is dominated by `deref`, not by the other two classes:
merging `deref` 5 → 1 removes **four** copies of a 16-function, depth-10 chain,
while merging `display` and
`new_display` removes almost nothing structurally.

Measured directly by dumping per-function contexts (`RCEUS_DUMP_FCTX`) and
selecting those whose context is `[FuncId(2)@bb2[3]]`, the canonical `deref` flow
entry.

## 6. Context counts

| | \tool (RCEUS) | \toolmerge (RCEUS-M) |
|---|---|---|
| `deref` contexts | 5 (+1 for `self.root_path`) | 1 (+1) |
| `display` contexts | 2 | 1 |
| `new_display` contexts | 2 | 1 |
| **figure subtotal** | **9** | **3** |
| all flow entries in `update_data` | 14 | 8 |
| `deref` chain re-analyses | 5 × 16 fns (depth 10) | 1 × 16 fns |

Whole-program (toy): `cs_funcs` 623; **46 redundant flow-entry callsites merged
into 31 groups**; `#dce` unchanged.

## 7. Exactness

- `deref` (5→1) — **exact**: all five arguments are references to the *same*
  object reached through different temporaries.
- `display` (2→1) — **exact**: same reasoning.
- `new_display` (2→1) — **not exact**: the two callsites pass `&display1` and
  `&display2`, addresses of two *distinct* locals that happen to share the root
  `mod_cache_path`. Root equality cannot see the difference, so the two
  `Argument`s each end up pointing to both `Display` values. This is the
  `\roots_f` over-approximation discussed in §3-Design, and the case that the
  AddrOf refinement (stopping at a freshly created local) would fix.

## 8. Reproduction

```bash
cd rupta-fork && git checkout rceus-merge-fe && cargo build --release
export PATH="$PWD/target/release:$PATH"
export LD_LIBRARY_PATH=~/.rustup/toolchains/nightly-2024-02-06-x86_64-unknown-linux-gnu/lib

cd /tmp/cachetoy
cargo clean -p cachetoy --target x86_64-unknown-linux-gnu
PTA_BUILD_STD=1 cargo-pta pta --bin cachetoy -- --rceus-m --context-depth 0 \
  --dump-call-graph /tmp/toy_cg.dot
```

`--dump-call-graph` writes the **context-insensitive** call graph as DOT (node
ids + labels, then edges). The §4 reference closure is a BFS over it from the
`PathBuf::deref` node. `--dump-mir` also exists but writes MIR for *every*
reachable function — fine for the toy (1.9 MB), impractical for wasmtime (~420k
functions), so stream-filter it there.

`--rceus-m` prints one statistic, consumed by RQ5's Sites/Groups column:

```
RCEUS merge-fe: 46 redundant flow-entry callsites merged into 31 groups
```

### Re-deriving the flow-entry numbers

The merge groups (§3) and the flow-entry call graph (§4) were measured with
temporary instrumentation that has since been **stripped** from the branch, so
plain `--rceus` output stays clean. To reproduce them, re-add either hook:

- **Merge groups / skip reasons** — in `compute_flow_entry_merge`
  (`precision_critical_func_identification.rs`), print each callsite's outcome
  (`flow-through` / `callee-not-cs` / `callee-no-pfg` / `unknown-roots` /
  `no-flowing-args`) and its grouping key, then dump every group *including
  singletons* with member callsites and argument paths.
- **Flow-entry call graph** — in `ContextSensitivePTA::finalize`
  (`context_sensitive.rs`), call the existing
  `results_dumper::dump_func_contexts(self.acx, &self.call_graph, &self.ctx_strategy, &path)`.
  Then select every function whose context set contains the canonical `deref`
  flow entry, `[FuncId(2)@bb2[3]]`; that set *is* §4's 16-function chain, and its
  depth is a BFS over the call graph restricted to it.

Caveat: FuncIds renumber between runs, so the context dump and the DOT must come
from the **same** run, and the `FuncId(2)@bb2[3]` site must be re-read from that
run rather than reused from this document.
