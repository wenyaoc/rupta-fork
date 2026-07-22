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
