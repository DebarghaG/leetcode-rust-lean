fn perfect_height(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, left, right) => {
            let lh = perfect_height(left);
            let rh = perfect_height(right);
            if lh >= 0 && rh >= 0 && lh == rh {
                lh + 1
            } else {
                -1
            }
        }
    }
}

fn collect_perfect_sizes(t: &Tree) -> Vec<i64> {
    match t {
        Tree::Null => Vec::new(),
        Tree::Node(_, left, right) => {
            let mut sizes = collect_perfect_sizes(left);
            let right_sizes = collect_perfect_sizes(right);

            let mut i = 0;
            while i < right_sizes.len() {
                sizes.push(right_sizes[i]);
                i += 1;
            }

            let h = perfect_height(t);
            if h >= 0 {
                let sz = (1_i64 << h) - 1;
                sizes.push(sz);
            }

            sizes
        }
    }
}

pub fn kth_largest_perfect_subtree(root: &Tree, k: i64) -> i64 {
    if k <= 0 {
        return -1;
    }

    let mut sizes = collect_perfect_sizes(root);
    let n = sizes.len();

    let mut i = 0;
    while i < n {
        let mut j = i + 1;
        while j < n {
            if sizes[j] > sizes[i] {
                let tmp = sizes[i];
                sizes[i] = sizes[j];
                sizes[j] = tmp;
            }
            j += 1;
        }
        i += 1;
    }

    let idx = k - 1;
    if idx >= n as i64 {
        return -1;
    }

    sizes[idx as usize]
}
