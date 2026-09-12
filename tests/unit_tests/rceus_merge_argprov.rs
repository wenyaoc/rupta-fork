// A Figure-15-style test for composing redundant flow-entry merging with
// argument-provenance refinement.

#[inline(never)]
fn id(x: &i32) -> &i32 {
    x
}

#[inline(never)]
fn pair<'a, 'b>(a: &'a i32, b: &'b i32) -> (&'a i32, &'b i32) {
    (id(a), id(b))
}

fn main() {
    let x = 1;
    let y = 2;
    let xr = &x;
    let yr = &y;

    // Like Figure 15's repeated accesses to one PathBuf, these two callsites
    // pass pointer flows from exactly the same roots. RCEUS-M should represent
    // both with the first callsite, while AP should continue to distinguish the
    // first and second argument inside `pair`.
    let p1 = pair(xr, yr);
    let p2 = pair(xr, yr);

    let _ = std::hint::black_box((p1, p2));
}
