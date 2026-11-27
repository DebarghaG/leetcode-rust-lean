// The harness-generated tests use the literal `vec![]` for the empty expected
// result while comparing against `Vec<Vec<i64>>`.  With nested vectors that
// literal is otherwise ambiguous (`Vec<i64>: PartialEq<?E>` has several std
// impls), producing `E0282: type annotations needed`.  Providing a local
// `vec!` macro that pins the empty case to `Vec<Vec<i64>>` (and behaves like the
// standard macro for the non-empty cases) resolves the ambiguity and keeps the
// whole thing inside the safe subset.
#[allow(unused_macros)]
macro_rules! vec {
    () => {
        ::std::vec::Vec::<Vec<i64>>::new()
    };
    ($($x:expr),+ $(,)?) => {{
        let mut __v = ::std::vec::Vec::new();
        $( __v.push($x); )+
        __v
    }};
    ($x:expr; $n:expr) => {{
        let __n = $n;
        let mut __v = ::std::vec::Vec::new();
        let mut __i = 0;
        while __i < __n {
            __v.push(($x).clone());
            __i += 1;
        }
        __v
    }};
}

pub fn combination_sum3(k: i64, n: i64) -> Vec<Vec<i64>> {
    let mut res: Vec<Vec<i64>> = Vec::new();

    if k < 1 || k > 9 {
        return res;
    }

    // Build the lexicographically smallest k-combination: [1, 2, ..., k].
    let mut cur: Vec<i64> = Vec::new();
    let mut c: i64 = 1;
    while c <= k {
        cur.push(c);
        c += 1;
    }

    loop {
        let mut sum: i64 = 0;
        let mut idx: usize = 0;
        while idx < cur.len() {
            sum += cur[idx];
            idx += 1;
        }

        if sum == n {
            let mut row: Vec<i64> = Vec::new();
            let mut t: usize = 0;
            while t < cur.len() {
                row.push(cur[t]);
                t += 1;
            }
            res.push(row);
        }

        // Find the rightmost position that can still be incremented while
        // leaving room for the remaining elements (they stay strictly
        // increasing and at most 9).
        let len: usize = cur.len();
        let mut i: usize = len;
        let mut logical: i64 = k;
        let mut found: bool = false;
        let mut found_idx: usize = 0;

        while i > 0 {
            i -= 1;
            logical -= 1;
            let max_val: i64 = 9 - (k - 1 - logical);
            if cur[i] < max_val {
                found = true;
                found_idx = i;
                break;
            }
        }

        if !found {
            break;
        }

        cur[found_idx] += 1;
        let mut j: usize = found_idx + 1;
        while j < len {
            cur[j] = cur[j - 1] + 1;
            j += 1;
        }
    }

    res
}
