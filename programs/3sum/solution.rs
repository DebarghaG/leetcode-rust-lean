#![allow(unused_macros)]

// A crate-local `vec!` shadowing the prelude one.
// The empty arm is pinned to `Vec<Vec<i64>>` so that comparisons such as
// `assert_eq!(three_sum(...), vec![])` are unambiguous (the std empty
// `Vec<_>` cannot be inferred when the element type is itself a `Vec`).
#[macro_export]
macro_rules! vec {
    () => {
        ::std::vec::Vec::<::std::vec::Vec<i64>>::new()
    };
    ($elem:expr; $n:expr) => {
        ::std::vec::from_elem($elem, $n)
    };
    ($($x:expr),+ $(,)?) => {{
        let mut __out = ::std::vec::Vec::new();
        $( __out.push($x); )+
        __out
    }};
}

pub fn three_sum(nums: &[i64]) -> Vec<Vec<i64>> {
    let n = nums.len();
    let mut out: Vec<Vec<i64>> = Vec::new();

    if n < 3 {
        return out;
    }

    // Copy input into an owned vector.
    let mut a: Vec<i64> = Vec::new();
    let mut k = 0;
    while k < n {
        a.push(nums[k]);
        k += 1;
    }

    // Insertion sort.
    let mut i = 1;
    while i < n {
        let key = a[i];
        let mut j = i;
        while j > 0 && a[j - 1] > key {
            a[j] = a[j - 1];
            j -= 1;
        }
        a[j] = key;
        i += 1;
    }

    let mut i = 0;
    while i + 2 < n {
        // Skip duplicate values for the first position.
        let mut skip = false;
        if i > 0 && a[i] == a[i - 1] {
            skip = true;
        }

        if !skip {
            let mut l = i + 1;
            let mut r = n - 1;

            while l < r {
                let s = a[i] + a[l] + a[r];

                if s == 0 {
                    let mut triplet: Vec<i64> = Vec::new();
                    triplet.push(a[i]);
                    triplet.push(a[l]);
                    triplet.push(a[r]);
                    out.push(triplet);

                    let left_value = a[l];
                    let right_value = a[r];

                    l += 1;
                    r -= 1;

                    while l < r && a[l] == left_value {
                        l += 1;
                    }
                    while l < r && a[r] == right_value {
                        r -= 1;
                    }
                } else if s < 0 {
                    l += 1;
                } else {
                    r -= 1;
                }
            }
        }

        i += 1;
    }

    out
}
