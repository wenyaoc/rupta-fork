# Functions merged by RCEUS flow-entry merging (`--rceus-m`)

Measured across all 16 benchmarks. Every callee listed is a **direct flow-entry
callee**: `compute_flow_entry_merge` only considers callsites where
`!caller_pfg.is_cs_callsite(loc)`, so flow-through callsites never appear.

| file | rows | contents |
|---|---|---|
| `merged-flow-entry-functions.tsv` | 2,124 | one row per function, generic instantiations collapsed |
| `merged-flow-entry-functions-by-monomorphisation.tsv` | 8,180 | one row per monomorphisation |

Columns: `sites` = callsites eliminated (group size − 1, summed);
`groups` = equivalence classes formed; `benchmarks` = how many of the 16 it
appears in; `monomorphisations` = distinct instantiations (collapsed file only).

Totals: **60,192 callsites eliminated**, 8,180 monomorphisations, 2,124 distinct
functions.

## Reproduce

```bash
RCEUS_DUMP_MERGES=<file> PTA_BUILD_STD=1 \
  cargo-pta pta --bin <bin> -- --rceus-m --context-depth 0
```

The dump's header carries the totals; each row is `merged_sites <TAB> groups <TAB> callee`.

## Top 20 (collapsed)

| # | sites | groups | benches | function |
|---|---|---|---|---|
| 1 | 3708 | 1883 | 16/16 | `core::fmt::rt::Argument::new_display` |
| 2 | 3113 | 1320 | 16/16 | `core::mem::ManuallyDrop::deref` |
| 3 | 2486 | 974 | 16/16 | `core::slice::get_unchecked` |
| 4 | 1580 | 627 | 16/16 | `alloc::vec::Vec::index` |
| 5 | 1436 | 704 | 16/16 | `alloc::sync::Arc::deref` |
| 6 | 1369 | 818 | 16/16 | `alloc::vec::Vec::deref` |
| 7 | 1276 | 658 | 16/16 | `core::slice::index::index` |
| 8 | 970 | 450 | 16/16 | `alloc::string::String::deref` |
| 9 | 927 | 683 | 16/16 | `core::slice::iter` |
| 10 | 805 | 509 | 16/16 | `core::iter::IntoIterator::into_iter` |
| 11 | 773 | 359 | 16/16 | `core::slice::iter::next` |
| 12 | 742 | 204 | 10/16 | `crossbeam_utils::CachePadded::deref` |
| 13 | 730 | 283 | 16/16 | `core::fmt::builders::field` |
| 14 | 720 | 198 | 10/16 | `clap_builder::Arg::get_id` |
| 15 | 702 | 651 | 16/16 | `core::slice::index_mut` |
| 16 | 701 | 170 | 16/16 | `core::slice::split_at_mut` |
| 17 | 669 | 118 | 10/16 | `std::sync::mpmc::utils::deref` |
| 18 | 644 | 240 | 16/16 | `core::option::Option::unwrap` |
| 19 | 611 | 290 | 14/16 | `core::result::Try::branch` |
| 20 | 584 | 146 | 1/16 | `serde_cbor::de::parse_str` |

The shape is `Deref` impls, slice indexing/iteration, and formatting-argument
wrappers -- the layered std abstractions a caller reaches repeatedly from many
syntactic callsites. 16 of the top 20 appear in all 16 benchmarks.

## Volume does not predict precision cost

Ranking by merge *volume* and by *harm* are nearly disjoint -- only row 1
overlaps. Measured on zoxide by enabling one merge group at a time
(`RCEUS_ONLY_GROUP` / `RCEUS_NOMERGE`, env-gated experiment flags; inert unless set):

- `new_display` is **15.7%** of merged sites but causes **93%** of the spurious
  points-to edges. Excluding it takes zoxide from **+1.91%** to **+0.12%**
  while keeping 84% of the merges. bandwhich +2.16% -> +0.47%, lsd +1.46% -> +0.12%.
- Of its 95 groups on zoxide, **83 (87%) are lossy, 12 (13%) are exactly
  precise**. Per-group costs sum to 7,039, matching the aggregate exactly, so
  group effects are additive.
- The loss is highly skewed: median cost is **2 edges**, but **3 groups exceed
  200** (max 3,422). Most `new_display` merges are nearly harmless by count; a
  handful of callsites where many distinct objects share one root do the damage.
- Everything else merges at **0.46--1.06** spurious edges per site, i.e.
  effectively free.
- `Path::display` and other `::display` adapters are **exactly** precise:
  excluding them on top of `new_display` gave bit-identical edge counts
  (bandwhich 1,975; lsd 1,416) while giving up 74 and 8 further merged sites.

---

# Real merging cases for the top 20

Each entry gives a **measured** merge group: the callee, the caller it was merged
in, the group size, and the source that produces the repeated callsites. Group
data from `RCEUS_DUMP_GROUPS` on zoxide / mdbook / gitui (qdrant for #20);
callers are chosen as the largest group available, preferring application code.

The recurring shape is the one §3-Design describes: several syntactically
distinct callsites whose flowing arguments trace back to **one root**, so the
callee is handed the same pointer each time.

---

### 1. `core::fmt::rt::Argument::new_display` — 3708 sites / 1883 groups
**Caller:** `clap_builder::builder::debug_asserts::assert_app` (mdbook, **35 callsites merged**)

```rust
// clap_builder-4.5.2/src/builder/debug_asserts.rs
assert!(!l.starts_with('-'), "Argument {}: long {:?} must not start with a `-`, \
        that will be handled by the parser", arg.get_id(), l);
short_flags.push(Flag::Arg(format!("-{s}"), arg.get_id().as_str()));
// ... 35 such format arguments across the function
```
Every `{}` placeholder expands to `Argument::new_display(&tmp)`. All 35 temporaries
trace back to the same `cmd` parameter, so they form one group.
**This is the lossy pattern** — each temporary holds a *different* value, so
merging conflates them (see the precision analysis above).

### 2. `core::mem::ManuallyDrop::deref` — 3113 sites / 1320 groups
**Caller:** `anyhow::error::Error::downcast<SilentExit>` (zoxide, 2 merged)

```rust
// anyhow-1.0.82/src/error.rs
let addr = match (vtable(inner.ptr).object_downcast)(inner.by_ref(), target) { ... };
let addr = match (vtable(inner.ptr).object_downcast_mut)(inner, target) { ... };
```
`inner` is a `ManuallyDrop<Own<ErrorImpl>>`; each use auto-derefs. Both derefs
reach the same `inner`, so the merge is exact.

### 3. `core::slice::get_unchecked` — 2486 sites / 974 groups
**Caller:** `futf::decode` (mdbook, **9 merged**)

```rust
// futf-0.1.5/src/lib.rs
n = ((*buf.get_unchecked(0) & 0b11111) as u32) << 6
  | ((*buf.get_unchecked(1) & 0x3F) as u32);
n = ((*buf.get_unchecked(0) & 0b1111) as u32) << 12
  | ((*buf.get_unchecked(1) & 0x3F) as u32) << 6
  | ((*buf.get_unchecked(2) & 0x3F) as u32);
```
Nine unchecked reads of the *same* `buf` across the UTF-8 length branches.
Classic re-access: one object, nine callsites.

### 4. `alloc::vec::Vec::index` — 1580 sites / 627 groups
**Caller:** `aho_corasick::nfa::contiguous::next_state` (mdbook, **9 merged**)

```rust
// aho-corasick-1.1.3/src/nfa/contiguous.rs
let kind = repr[o] & 0xFF;
let next = u32tosid(repr[o + 2 + usize::from(class)]);
if class == repr[o].low_u16().high_u8() { return u32tosid(repr[o + 2]); }
```
Repeated indexing into one `repr` vector while decoding a state.

### 5. `alloc::sync::Arc::deref` — 1436 sites / 704 groups
**Caller:** `tokio::runtime::blocking::pool::Spawner::spawn_task` (mdbook, **9 merged**)

```rust
// tokio-1.37.0/src/runtime/blocking/pool.rs
let mut shared = self.inner.shared.lock();
self.inner.metrics.inc_queue_depth();
if self.inner.metrics.num_idle_threads() == 0 { ... }
if self.inner.metrics.num_threads() == self.inner.thread_cap { ... }
```
`self.inner` is an `Arc<Inner>`; every field access derefs it. Nine derefs of one
`Arc`.

### 6. `alloc::vec::Vec::deref` — 1369 sites / 818 groups
**Caller:** `mdbook::renderer::html_handlebars::copy_static_files` (mdbook, **13 merged**)

```rust
// mdBook/src/renderer/html_handlebars/hbs_renderer.rs
write_file(destination, "book.js", &theme.js)?;
write_file(destination, "css/general.css", &theme.general_css)?;
write_file(destination, "css/chrome.css", &theme.chrome_css)?;
write_file(destination, "css/variables.css", &theme.variables_css)?;
write_file(destination, "highlight.css", &theme.highlight_css)?;
```
Each `&theme.X` coerces `&Vec<u8>` to `&[u8]` via `Vec::deref`. Note these are
**distinct fields of one `theme`** — the second over-approximation case named in
§3-Design (distinct fields projected from one parameter), not pure re-access.

### 7. `core::slice::index::index` — 1276 sites / 658 groups
**Caller:** `pulldown_cmark::firstpass::parse_block` (mdbook, **16 merged**)

```rust
// pulldown-cmark-0.9.3/src/firstpass.rs
let mut line_start = LineStart::new(&bytes[start_ix..]);
start_ix += scan_blank_line(&bytes[start_ix..]).unwrap_or(0);
if let Some(n) = scan_blank_line(&bytes[after_marker_index..]) { ... }
```
Sixteen slicings of the same `bytes` buffer at different offsets while scanning a
block.

### 8. `alloc::string::String::deref` — 970 sites / 450 groups
**Caller:** `tui_textarea::cursor::next_cursor` (gitui, **17 merged**)

```rust
// tui-textarea-0.4.0/src/cursor.rs
Forward if col >= lines[row].chars().count() => ...
End => Some((row, lines[row].chars().count())),
Top => Some((0, fit_col(col, &lines[0]))),
if let Some(col) = find_word_start_forward(&lines[row], col) { ... }
```
Every `lines[row]` yields a `&String` that derefs to `&str`. Seventeen callsites,
one `lines` vector.

### 9. `core::slice::iter` — 927 sites / 683 groups
**Caller:** `url::host::parse_ipv4number` (mdbook, 3 merged)

```rust
// url-2.5.0/src/host.rs:281
fn parse_ipv4number(mut input: &str) -> Result<Option<u32>, ()> {
    if input.starts_with("0x") || input.starts_with("0X") { input = &input[2..]; r = 16; }
    else if input.len() >= 2 && input.starts_with('0') { input = &input[1..]; r = 8; }
```
The radix branches each re-scan the same `input`, producing three iteration entries
over one buffer.

### 10. `core::iter::IntoIterator::into_iter` — 805 sites / 509 groups
**Caller:** `regex_automata::nfa::thompson::compiler::c_unicode_class` (mdbook, 3 merged)

```rust
// regex-automata-0.4.6/src/nfa/thompson/compiler.rs
for r in cls.iter() { ... }          // reverse-suffix branch
for rng in cls.iter() { ... }        // forward branch
for rng in cls.iter() { ... }        // fallback branch
```
Three loops over the *same* class `cls` on mutually exclusive paths — the
branch-repetition case, one object.

### 11. `core::slice::iter::Iter::next` — 773 sites / 359 groups
**Caller:** `clap_builder::builder::debug_asserts::assert_app` (mdbook, **7 merged**)

Seven `for arg in cmd.get_arguments()`-style loops in the same validation
function, all iterating the one command's argument slice.

### 12. `crossbeam_utils::CachePadded::deref` — 742 sites / 204 groups
**Caller:** `crossbeam_channel::flavors::list::Channel::start_send` (mdbook, **12 merged**)

```rust
// crossbeam-channel-0.5.8/src/flavors/list.rs
let mut tail  = self.tail.index.load(Ordering::Acquire);
let mut block = self.tail.block.load(Ordering::Acquire);
...
tail  = self.tail.index.load(Ordering::Acquire);
block = self.tail.block.load(Ordering::Acquire);
self.head.block.store(new, Ordering::Release);
```
`tail`/`head` are `CachePadded<...>`; every access derefs. Twelve derefs inside
one CAS retry loop — note the repetition here comes from a **loop**, not from
distinct operations.

### 13. `core::fmt::builders::DebugStruct::field` — 730 sites / 283 groups
**Caller:** `notify::event::Event::fmt` (mdbook, **6 merged**)

Generated by `#[derive(Debug)]`: one `.field(...)` call per struct field, all on
the same `DebugStruct` builder. There is no hand-written source — the six
callsites come from the derive expansion.

### 14. `clap_builder::builder::Arg::get_id` — 720 sites / 198 groups
**Caller:** `clap_builder::builder::debug_asserts::assert_app` (mdbook, **25 merged**)

```rust
// clap_builder-4.5.2/src/builder/debug_asserts.rs
short_flags.push(Flag::Arg(format!("-{s}"), arg.get_id().as_str()));
assert!(!l.starts_with('-'), "Argument {}: ...", arg.get_id(), l);
```
Twenty-five `arg.get_id()` calls in one validation pass over the same command.

### 15. `core::slice::index_mut` — 702 sites / 651 groups
**Caller:** `aho_corasick::dfa::finish_build_both_starts` (mdbook, 2 merged)

```rust
// aho-corasick-1.1.3/src/dfa.rs
remap_unanchored[oldsid] = newsid;
remap_anchored[oldsid]   = newsid;
```

### 16. `core::slice::split_at_mut` — 701 sites / 170 groups
**Caller:** `miniz_oxide::inflate::core::apply_match` (mdbook, 2 merged)

```rust
// miniz_oxide-0.7.2/src/inflate/core.rs
let (from_slice, to_slice) = out_slice.split_at_mut(out_pos);
let (to_slice, from_slice) = out_slice.split_at_mut(source_pos);
```
Two splits of the same output buffer on the forward/backward copy paths.

### 17. `std::sync::mpmc::utils::CachePadded::deref` — 669 sites / 118 groups
**Caller:** `std::sync::mpmc::list::Channel::start_send` (mdbook, **13 merged**)

The std vendored copy of the crossbeam list channel — same code shape as #12,
thirteen `self.tail.*` / `self.head.*` derefs in the retry loop.

### 18. `core::option::Option::unwrap` — 644 sites / 240 groups
**Caller:** `regex_syntax::hir::translate::visit_class_set_item_post` (mdbook, **13 merged**)

```rust
// regex-syntax-0.8.3/src/hir/translate.rs
let mut cls = self.pop().unwrap().unwrap_class_unicode();
let mut cls = self.pop().unwrap().unwrap_class_bytes();
// ... 13 such arms, one per class-item kind
```
Thirteen `self.pop().unwrap()` calls across the match arms, all popping the same
stack.

### 19. `core::result::Try::branch` — 611 sites / 290 groups
**Caller:** `iana_time_zone::platform::openwrt::etc_config_system` (mdbook, **8 merged**)

```rust
// iana-time-zone-0.1.60/src/tz_linux.rs
let f = fs::OpenOptions::new().read(true).open("/etc/config/system")?;
...
f.read_line(&mut line)?;
```
Each `?` expands to `Try::branch`. Eight `?` operators in one function, all on
results derived from the same file handle.

### 20. `serde_cbor::de::parse_str` — 584 sites / 146 groups
**Caller:** derive-generated `Deserialize::deserialize` visitors (qdrant, 4 merged each)

Produced by `#[derive(Deserialize)]` — each generated `__FieldVisitor` calls
`parse_str` once per field while decoding from one `SliceRead` reader. No
hand-written source; the repetition is entirely from the derive expansion.

---

## What the 20 cases show

- **Re-access dominates.** 15 of 20 are repeated access to *one* object through
  `Deref`/`Index`/iterator methods — exactly the pattern §3-Design argues is
  syntactic rather than semantic, and merging them is exact.
- **Repetition has several sources**, not just "different operations on the same
  object": mutually exclusive **branches** (#3, #9, #10, #16, #18), **loops**
  (#12, #17), **derive expansions** (#13, #20), and genuinely different
  operations (#6, #14).
- **Two cases are not pure re-access.** #1 (`new_display`) packages distinct
  values into per-argument temporaries, and #6 (`Vec::deref`) projects distinct
  *fields* from one parameter. These are precisely the two over-approximation
  cases §3-Design names, and #1 is where nearly all the measured precision loss
  comes from.

---

# Real merging cases for the top 20

Each entry gives a **measured** merge group: the callee, the caller it was merged
in, the group size, and the source that produces the repeated callsites. Group
data from `RCEUS_DUMP_GROUPS` on zoxide / mdbook / gitui (qdrant for #20);
callers are the largest group available, preferring application code.

The recurring shape is the one §3-Design describes: several syntactically
distinct callsites whose flowing arguments trace back to **one root**, so the
callee is handed the same pointer each time.

---

### 1. `core::fmt::rt::Argument::new_display` — 3708 sites / 1883 groups
**Caller:** `clap_builder::builder::debug_asserts::assert_app` (mdbook, **35 callsites merged**)

```rust
// clap_builder-4.5.2/src/builder/debug_asserts.rs
assert!(!l.starts_with('-'), "Argument {}: long {:?} must not start with a `-`, \
        that will be handled by the parser", arg.get_id(), l);
short_flags.push(Flag::Arg(format!("-{s}"), arg.get_id().as_str()));
// ... 35 such format arguments across the function
```

Every `{}` placeholder expands to `Argument::new_display(&tmp)`. All 35
temporaries trace back to the same `cmd` parameter, so they form one group.
**This is the lossy pattern** — each temporary holds a *different* value, so
merging conflates them.

### 2. `core::mem::ManuallyDrop::deref` — 3113 sites / 1320 groups
**Caller:** `anyhow::error::Error::downcast<SilentExit>` (zoxide, 2 merged)

```rust
// anyhow-1.0.82/src/error.rs
let addr = match (vtable(inner.ptr).object_downcast)(inner.by_ref(), target) { ... };
let addr = match (vtable(inner.ptr).object_downcast_mut)(inner, target) { ... };
```

`inner` is a `ManuallyDrop<Own<ErrorImpl>>`; each use auto-derefs. Both reach the
same `inner`, so the merge is exact.

### 3. `core::slice::get_unchecked` — 2486 sites / 974 groups
**Caller:** `futf::decode` (mdbook, **9 merged**)

```rust
// futf-0.1.5/src/lib.rs
n = ((*buf.get_unchecked(0) & 0b11111) as u32) << 6
  | ((*buf.get_unchecked(1) & 0x3F) as u32);
n = ((*buf.get_unchecked(0) & 0b1111) as u32) << 12
  | ((*buf.get_unchecked(1) & 0x3F) as u32) << 6
  | ((*buf.get_unchecked(2) & 0x3F) as u32);
```

Nine unchecked reads of the *same* `buf` across the UTF-8 length branches.
Classic re-access: one object, nine callsites.

### 4. `alloc::vec::Vec::index` — 1580 sites / 627 groups
**Caller:** `aho_corasick::nfa::contiguous::next_state` (mdbook, **9 merged**)

```rust
// aho-corasick-1.1.3/src/nfa/contiguous.rs
let kind = repr[o] & 0xFF;
let next = u32tosid(repr[o + 2 + usize::from(class)]);
if class == repr[o].low_u16().high_u8() { return u32tosid(repr[o + 2]); }
```

Repeated indexing into one `repr` vector while decoding a state.

### 5. `alloc::sync::Arc::deref` — 1436 sites / 704 groups
**Caller:** `tokio::runtime::blocking::pool::Spawner::spawn_task` (mdbook, **9 merged**)

```rust
// tokio-1.37.0/src/runtime/blocking/pool.rs
let mut shared = self.inner.shared.lock();
self.inner.metrics.inc_queue_depth();
if self.inner.metrics.num_idle_threads() == 0 { ... }
if self.inner.metrics.num_threads() == self.inner.thread_cap { ... }
```

`self.inner` is an `Arc<Inner>`; every field access derefs it. Nine derefs of one
`Arc`.

### 6. `alloc::vec::Vec::deref` — 1369 sites / 818 groups
**Caller:** `mdbook::renderer::html_handlebars::copy_static_files` (mdbook, **13 merged**)

```rust
// mdBook/src/renderer/html_handlebars/hbs_renderer.rs
write_file(destination, "book.js", &theme.js)?;
write_file(destination, "css/general.css", &theme.general_css)?;
write_file(destination, "css/chrome.css", &theme.chrome_css)?;
write_file(destination, "css/variables.css", &theme.variables_css)?;
write_file(destination, "highlight.css", &theme.highlight_css)?;
```

Each `&theme.X` coerces `&Vec<u8>` to `&[u8]` via `Vec::deref`. Note these are
**distinct fields of one `theme`** — the second over-approximation case named in
§3-Design (distinct fields projected from one parameter), not pure re-access.

### 7. `core::slice::index::index` — 1276 sites / 658 groups
**Caller:** `pulldown_cmark::firstpass::parse_block` (mdbook, **16 merged**)

```rust
// pulldown-cmark-0.9.3/src/firstpass.rs
let mut line_start = LineStart::new(&bytes[start_ix..]);
start_ix += scan_blank_line(&bytes[start_ix..]).unwrap_or(0);
if let Some(n) = scan_blank_line(&bytes[after_marker_index..]) { ... }
```

Sixteen slicings of the same `bytes` buffer at different offsets while scanning a
block.

### 8. `alloc::string::String::deref` — 970 sites / 450 groups
**Caller:** `tui_textarea::cursor::next_cursor` (gitui, **17 merged**)

```rust
// tui-textarea-0.4.0/src/cursor.rs
Forward if col >= lines[row].chars().count() => ...
End => Some((row, lines[row].chars().count())),
Top => Some((0, fit_col(col, &lines[0]))),
if let Some(col) = find_word_start_forward(&lines[row], col) { ... }
```

Every `lines[row]` yields a `&String` that derefs to `&str`. Seventeen callsites,
one `lines` vector.

### 9. `core::slice::iter` — 927 sites / 683 groups
**Caller:** `url::host::parse_ipv4number` (mdbook, 3 merged)

```rust
// url-2.5.0/src/host.rs:281
fn parse_ipv4number(mut input: &str) -> Result<Option<u32>, ()> {
    if input.starts_with("0x") || input.starts_with("0X") { input = &input[2..]; r = 16; }
    else if input.len() >= 2 && input.starts_with('0') { input = &input[1..]; r = 8; }
```

The radix branches each re-scan the same `input`, producing three iteration
entries over one buffer.

### 10. `core::iter::IntoIterator::into_iter` — 805 sites / 509 groups
**Caller:** `regex_automata::nfa::thompson::compiler::c_unicode_class` (mdbook, 3 merged)

```rust
// regex-automata-0.4.6/src/nfa/thompson/compiler.rs
for r   in cls.iter() { ... }   // reverse-suffix branch
for rng in cls.iter() { ... }   // forward branch
for rng in cls.iter() { ... }   // fallback branch
```

Three loops over the *same* class `cls` on mutually exclusive paths — the
branch-repetition case, one object.

### 11. `core::slice::iter::Iter::next` — 773 sites / 359 groups
**Caller:** `clap_builder::builder::debug_asserts::assert_app` (mdbook, **7 merged**)

Seven `for arg in ...`-style loops in the same validation function, all iterating
the one command's argument slice.

### 12. `crossbeam_utils::CachePadded::deref` — 742 sites / 204 groups
**Caller:** `crossbeam_channel::flavors::list::Channel::start_send` (mdbook, **12 merged**)

```rust
// crossbeam-channel-0.5.8/src/flavors/list.rs
let mut tail  = self.tail.index.load(Ordering::Acquire);
let mut block = self.tail.block.load(Ordering::Acquire);
// ... inside the CAS retry loop:
tail  = self.tail.index.load(Ordering::Acquire);
block = self.tail.block.load(Ordering::Acquire);
self.head.block.store(new, Ordering::Release);
```

`tail`/`head` are `CachePadded<...>`; every access derefs. Twelve derefs inside
one retry loop — the repetition here comes from a **loop**, not from distinct
operations.

### 13. `core::fmt::builders::DebugStruct::field` — 730 sites / 283 groups
**Caller:** `notify::event::Event::fmt` (mdbook, **6 merged**)

Generated by `#[derive(Debug)]`: one `.field(...)` call per struct field, all on
the same `DebugStruct` builder. No hand-written source — the six callsites come
from the derive expansion.

### 14. `clap_builder::builder::Arg::get_id` — 720 sites / 198 groups
**Caller:** `clap_builder::builder::debug_asserts::assert_app` (mdbook, **25 merged**)

```rust
// clap_builder-4.5.2/src/builder/debug_asserts.rs
short_flags.push(Flag::Arg(format!("-{s}"), arg.get_id().as_str()));
assert!(!l.starts_with('-'), "Argument {}: ...", arg.get_id(), l);
```

Twenty-five `arg.get_id()` calls in one validation pass over the same command.

### 15. `core::slice::index_mut` — 702 sites / 651 groups
**Caller:** `aho_corasick::dfa::finish_build_both_starts` (mdbook, 2 merged)

```rust
// aho-corasick-1.1.3/src/dfa.rs
remap_unanchored[oldsid] = newsid;
remap_anchored[oldsid]   = newsid;
```

### 16. `core::slice::split_at_mut` — 701 sites / 170 groups
**Caller:** `miniz_oxide::inflate::core::apply_match` (mdbook, 2 merged)

```rust
// miniz_oxide-0.7.2/src/inflate/core.rs
let (from_slice, to_slice) = out_slice.split_at_mut(out_pos);
let (to_slice, from_slice) = out_slice.split_at_mut(source_pos);
```

Two splits of the same output buffer on the forward/backward copy paths.

### 17. `std::sync::mpmc::utils::CachePadded::deref` — 669 sites / 118 groups
**Caller:** `std::sync::mpmc::list::Channel::start_send` (mdbook, **13 merged**)

The std vendored copy of the crossbeam list channel — same code shape as #12,
thirteen `self.tail.*` / `self.head.*` derefs in the retry loop.

### 18. `core::option::Option::unwrap` — 644 sites / 240 groups
**Caller:** `regex_syntax::hir::translate::visit_class_set_item_post` (mdbook, **13 merged**)

```rust
// regex-syntax-0.8.3/src/hir/translate.rs
let mut cls = self.pop().unwrap().unwrap_class_unicode();
let mut cls = self.pop().unwrap().unwrap_class_bytes();
// ... 13 such arms, one per class-item kind
```

Thirteen `self.pop().unwrap()` calls across the match arms, all popping the same
stack.

### 19. `core::result::Try::branch` — 611 sites / 290 groups
**Caller:** `iana_time_zone::platform::openwrt::etc_config_system` (mdbook, **8 merged**)

```rust
// iana-time-zone-0.1.60/src/tz_linux.rs
let f = fs::OpenOptions::new().read(true).open("/etc/config/system")?;
// ...
f.read_line(&mut line)?;
```

Each `?` expands to `Try::branch`. Eight `?` operators in one function, all on
results derived from the same file handle.

### 20. `serde_cbor::de::parse_str` — 584 sites / 146 groups
**Caller:** derive-generated `Deserialize::deserialize` visitors (qdrant, 4 merged each)

Produced by `#[derive(Deserialize)]` — each generated `__FieldVisitor` calls
`parse_str` once per field while decoding from one `SliceRead` reader. No
hand-written source; the repetition is entirely from the derive expansion.

---

## What the 20 cases show

- **Re-access dominates.** 18 of 20 are repeated access to *one* object through
  `Deref`/`Index`/iterator methods — the pattern §3-Design argues is syntactic
  rather than semantic, and merging them is exact.
- **Repetition has several sources**, not only "different operations on the same
  object": mutually exclusive **branches** (#3, #9, #10, #16, #18), **loops**
  (#12, #17), **derive expansions** (#13, #20), and genuinely different
  operations (#6, #14).
- **Two cases are not pure re-access.** #1 (`new_display`) packages distinct
  values into per-argument temporaries, and #6 (`Vec::deref`) projects distinct
  *fields* from one parameter. These are exactly the two over-approximation cases
  §3-Design names, and #1 is where nearly all the measured precision loss comes
  from.
