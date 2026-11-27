pub fn count_great_enough_nodes(root: &Tree, k: i64) -> i64 {
    let result = dfs(root, k);
    result[result.len() - 1]
}

fn dfs(t: &Tree, k: i64) -> Vec<i64> {
    match t {
        Tree::Null => {
            let mut v: Vec<i64> = Vec::new();
            v.push(0); // subtree size
            v.push(0); // number of great enough nodes
            v
        }
        Tree::Node(val, left, right) => {
            let lv = dfs(&**left, k);
            let rv = dfs(&**right, k);

            let lsz = lv[lv.len() - 2];
            let lcnt = lv[lv.len() - 1];
            let rsz = rv[rv.len() - 2];
            let rcnt = rv[rv.len() - 1];

            let lm = lv.len() - 2;
            let rm = rv.len() - 2;

            let mut vals: Vec<i64> = Vec::new();

            let mut i = 0;
            while i < lm {
                vals.push(lv[i]);
                i += 1;
            }

            i = 0;
            while i < rm {
                vals.push(rv[i]);
                i += 1;
            }

            vals.push(*val);

            // Sort vals in nondecreasing order using insertion sort.
            let m = vals.len();
            let mut a = 0;
            while a < m {
                let mut b = a;
                while b > 0 && vals[b - 1] > vals[b] {
                    let tmp = vals[b - 1];
                    vals[b - 1] = vals[b];
                    vals[b] = tmp;
                    b -= 1;
                }
                a += 1;
            }

            let size = lsz + rsz + 1;
            let ku = k as usize;
            let mut great = 0;

            if size >= k && ku <= vals.len() {
                if vals[ku - 1] < *val {
                    great = 1;
                }
            }

            let mut kept: Vec<i64> = Vec::new();
            let limit = if ku < vals.len() { ku } else { vals.len() };

            let mut j = 0;
            while j < limit {
                kept.push(vals[j]);
                j += 1;
            }

            kept.push(size);
            kept.push(lcnt + rcnt + great);
            kept
        }
    }
}
