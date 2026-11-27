const BASE: i64 = 1_099_511_627_776; // 2^40, larger than any possible subtree sum

pub fn equal_to_descendants(root: &Tree) -> i64 {
    fn dfs(t: &Tree) -> i64 {
        match t {
            Tree::Null => 0,
            Tree::Node(v, l, r) => {
                let left = dfs(&**l);
                let right = dfs(&**r);

                // Unpack count and subtree-sum from the child encodings.
                let left_sum = left % BASE;
                let right_sum = right % BASE;
                let left_cnt = left / BASE;
                let right_cnt = right / BASE;

                let val = *v;
                let descendants_sum = left_sum + right_sum;

                // Compute indicator (1 if val == descendants_sum, else 0)
                // WITHOUT using `if` or `==`, only `while` loops + arithmetic.
                // Clamp descendants_sum down to at most 100001 (one step if larger);
                // since val <= 100000, equality can only occur at values <= 100001.
                let mut bt = descendants_sum;
                while bt > 100001 {
                    bt = 100001;
                }
                // |dd| is now bounded by ~100001, so dd*dd fits in i64.
                let dd = val - bt;
                let dd2 = dd * dd;
                // Clamp dd2 down to 0 or 1 (one step if dd2 > 1).
                let mut c = dd2;
                while c > 1 {
                    c = 1;
                }
                let extra = 1 - c;

                let cnt = left_cnt + right_cnt + extra;
                let subtree_sum = val + descendants_sum;

                cnt * BASE + subtree_sum
            }
        }
    }

    dfs(root) / BASE
}
