#![allow(non_snake_case)]

pub fn remove_interval(intervals: &[Vec<i64>], toBeRemoved: &[i64]) -> Vec<Vec<i64>> {
    let mut result: Vec<Vec<i64>> = Vec::new();

    let remove_start: i64 = toBeRemoved[0];
    let remove_end: i64 = toBeRemoved[1];

    let n: usize = intervals.len();
    let mut i: usize = 0;

    while i < n {
        let start: i64 = intervals[i][0];
        let end: i64 = intervals[i][1];

        if end <= remove_start || remove_end <= start {
            // Interval is entirely outside the removed range: keep it.
            let mut row: Vec<i64> = Vec::new();
            row.push(start);
            row.push(end);
            result.push(row);
        } else {
            // Left leftover [start, remove_start)
            if start < remove_start {
                let mut row: Vec<i64> = Vec::new();
                row.push(start);
                row.push(remove_start);
                result.push(row);
            }
            // Right leftover [remove_end, end)
            if remove_end < end {
                let mut row: Vec<i64> = Vec::new();
                row.push(remove_end);
                row.push(end);
                result.push(row);
            }
        }

        i = i + 1;
    }

    result
}

// Test-only helper macro.
//
// The harness compares results with `assert_eq!(..., vec![])`. For a
// `Vec<Vec<i64>>` left-hand side, an untyped empty `vec![]` is ambiguous
// (`Vec<i64>: PartialEq<_>` has several candidate impls), which makes Rust
// fail with E0282. This `#[cfg(test)]` macro is only present in test builds
// (so it never reaches the Aeneas/Charon translation of the library) and
// gives the empty form a concrete `Vec<Vec<i64>>` type while keeping all
// non-empty forms behaving exactly like the standard library `vec!`.
#[cfg(test)]
macro_rules! vec {
    () => { ::std::vec::Vec::<::std::vec::Vec<i64>>::new() };
    ($elem:expr; $n:expr) => { ::std::vec![$elem; $n] };
    ($($x:expr),+ $(,)?) => { ::std::vec::Vec::from([$($x),+]) };
}
