// The append-style test harness compares results with `vec![]` for empty
// expected outputs. For a `Vec<Vec<i64>>` return type that is ambiguous under
// type inference (`Vec<i64>: PartialEq<Vec<i64> | &[i64] | [i64]>`), so we
// provide a test-only `vec!` shadow that pins the empty case to the concrete
// result type. This macro is fully expanded away before Charon/Aeneas see the
// crate's real functions, so it never affects translated code.
#[cfg(test)]
#[allow(unused_macros)]
macro_rules! vec {
    () => {{
        let v: ::std::vec::Vec<::std::vec::Vec<i64>> = ::std::vec::Vec::new();
        v
    }};
    ($($x:expr),+ $(,)?) => {{
        let mut v = ::std::vec::Vec::new();
        $( v.push($x); )*
        v
    }};
}

pub fn find_maximal_uncovered_ranges(n: i64, ranges: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = ranges.len();
    let mut out: Vec<Vec<i64>> = Vec::new();

    // No ranges at all: the whole array is uncovered.
    if m == 0 {
        let mut row: Vec<i64> = Vec::new();
        row.push(0);
        row.push(n - 1);
        out.push(row);
        return out;
    }

    // Copy starts / ends so we can sort them together.
    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < m {
        starts.push(ranges[idx][0]);
        ends.push(ranges[idx][1]);
        idx += 1;
    }

    let sz = starts.len();

    // Bottom-up (iterative) merge sort of (starts, ends) by start value.
    // Iterative to stay friendly to the verification toolchain (no recursion).
    let mut temp_s: Vec<i64> = Vec::new();
    let mut temp_e: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < sz {
        temp_s.push(0);
        temp_e.push(0);
        t += 1;
    }

    let mut width: usize = 1;
    while width < sz {
        let mut left: usize = 0;
        while left < sz {
            let mut mid = left + width;
            if mid > sz {
                mid = sz;
            }
            let mut right = mid + width;
            if right > sz {
                right = sz;
            }

            let mut i = left;
            let mut j = mid;
            let mut k = left;

            while i < mid && j < right {
                if starts[j] < starts[i] {
                    temp_s[k] = starts[j];
                    temp_e[k] = ends[j];
                    j += 1;
                } else {
                    temp_s[k] = starts[i];
                    temp_e[k] = ends[i];
                    i += 1;
                }
                k += 1;
            }
            while i < mid {
                temp_s[k] = starts[i];
                temp_e[k] = ends[i];
                i += 1;
                k += 1;
            }
            while j < right {
                temp_s[k] = starts[j];
                temp_e[k] = ends[j];
                j += 1;
                k += 1;
            }

            left = right;
        }

        // Copy merged run back.
        let mut c: usize = 0;
        while c < sz {
            starts[c] = temp_s[c];
            ends[c] = temp_e[c];
            c += 1;
        }

        width = width * 2;
    }

    // Sweep the sorted intervals and emit every maximal uncovered gap.
    let mut cur: i64 = 0;
    let mut i: usize = 0;
    while i < sz {
        let s = starts[i];
        let e = ends[i];

        if s > cur {
            // Gap [cur, s - 1] is uncovered and maximal.
            let mut row: Vec<i64> = Vec::new();
            row.push(cur);
            row.push(s - 1);
            out.push(row);
            cur = e + 1;
        } else {
            // Covered up to `cur`; extend if this interval reaches further.
            let next = e + 1;
            if next > cur {
                cur = next;
            }
        }

        i += 1;
    }

    // Trailing uncovered gap, if any.
    if cur <= n - 1 {
        let mut row: Vec<i64> = Vec::new();
        row.push(cur);
        row.push(n - 1);
        out.push(row);
    }

    out
}
