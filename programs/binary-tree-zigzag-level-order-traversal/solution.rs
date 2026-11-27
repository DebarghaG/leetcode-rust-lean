// Some harnesses emit `assert_eq!(zigzag_level_order(...), vec![])` for the
// empty-tree case. In plain Rust the element type of that bare `vec![]`
// cannot be inferred when the left side is `Vec<Vec<i64>>` (E0282), because
// `Vec<i64>` implements `PartialEq` against `Vec<i64>`, `&[i64]`, `[i64; N]`,
// ... . This textual macro makes the *empty* form resolve to the concrete
// `Vec<Vec<i64>>`, delegating every other form to the standard `vec!`.
// It is not used by `zigzag_level_order`, so it does not affect translation.
#[allow(unused_macros)]
macro_rules! vec {
    () => {
        ::std::vec::Vec::<::std::vec::Vec<i64>>::new()
    };
    ($($t:tt)*) => {
        ::std::vec![$($t)*]
    };
}

fn tree_height(t: &Tree) -> usize {
    match t {
        Tree::Null => 0,
        Tree::Node(_, l, r) => {
            let hl = tree_height(&**l);
            let hr = tree_height(&**r);
            if hl > hr {
                hl + 1
            } else {
                hr + 1
            }
        }
    }
}

fn values_at_level(t: &Tree, current: usize, target: usize) -> Vec<i64> {
    if current > target {
        return Vec::new();
    }

    match t {
        Tree::Null => Vec::new(),
        Tree::Node(v, l, r) => {
            if current == target {
                let mut res: Vec<i64> = Vec::new();
                res.push(*v);
                res
            } else {
                let mut res: Vec<i64> = values_at_level(&**l, current + 1, target);
                let right_vals: Vec<i64> = values_at_level(&**r, current + 1, target);

                let mut i: usize = 0;
                while i < right_vals.len() {
                    res.push(right_vals[i]);
                    i = i + 1;
                }

                res
            }
        }
    }
}

pub fn zigzag_level_order(root: &Tree) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = Vec::new();
    let h: usize = tree_height(root);

    let mut level: usize = 0;
    while level < h {
        let mut vals: Vec<i64> = values_at_level(root, 0, level);

        if level % 2 == 1 {
            let mut left: usize = 0;
            let mut right: usize = vals.len();

            while left < right {
                right = right - 1;
                if left >= right {
                    break;
                }

                let tmp: i64 = vals[left];
                vals[left] = vals[right];
                vals[right] = tmp;
                left = left + 1;
            }
        }

        out.push(vals);
        level = level + 1;
    }

    out
}
