fn descend(tree: &[i64], size: usize, mut node: usize, x: i64) -> i64 {
    while node < size {
        let left = node * 2;
        if tree[left] > x {
            node = left;
        } else {
            node = left + 1;
        }
    }
    (node - size) as i64
}

fn first_greater(tree: &[i64], size: usize, n: usize, l: usize, x: i64) -> i64 {
    let mut result: i64 = -1;

    if l < n {
        let mut left_nodes: Vec<i64> = Vec::new();
        let mut right_nodes: Vec<i64> = Vec::new();

        let mut lo = l + size;
        let mut hi = n + size;

        while lo < hi {
            if lo % 2 == 1 {
                left_nodes.push(lo as i64);
                lo += 1;
            }
            if hi % 2 == 1 {
                hi -= 1;
                right_nodes.push(hi as i64);
            }
            lo = lo / 2;
            hi = hi / 2;
        }

        let mut done = false;

        let mut i = 0usize;
        while i < left_nodes.len() {
            if !done {
                let node = left_nodes[i] as usize;
                if tree[node] > x {
                    result = descend(tree, size, node, x);
                    done = true;
                }
            }
            i += 1;
        }

        let mut j = right_nodes.len();
        while j > 0 {
            if !done {
                j -= 1;
                let node = right_nodes[j] as usize;
                if tree[node] > x {
                    result = descend(tree, size, node, x);
                    done = true;
                }
            } else {
                j -= 1;
            }
        }
    }

    result
}

pub fn leftmost_building_queries(heights: &[i64], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = heights.len();

    let mut size = 1usize;
    while size < n {
        size = size * 2;
    }

    let total = size * 2;
    let mut tree: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < total {
        tree.push(-1);
        i += 1;
    }

    i = 0;
    while i < n {
        tree[size + i] = heights[i];
        i += 1;
    }

    let mut p = size;
    while p > 1 {
        p -= 1;
        let left = tree[p * 2];
        let right = tree[p * 2 + 1];
        if left > right {
            tree[p] = left;
        } else {
            tree[p] = right;
        }
    }

    let mut ans: Vec<i64> = Vec::new();
    let q = queries.len();
    let mut qi = 0usize;

    while qi < q {
        let a = queries[qi][0] as usize;
        let b = queries[qi][1] as usize;

        if a == b {
            ans.push(a as i64);
        } else {
            let mut l = a;
            let mut r = b;
            if l > r {
                let tmp = l;
                l = r;
                r = tmp;
            }

            if heights[l] < heights[r] {
                ans.push(r as i64);
            } else {
                let res = first_greater(&tree, size, n, r + 1, heights[l]);
                ans.push(res);
            }
        }

        qi += 1;
    }

    ans
}
