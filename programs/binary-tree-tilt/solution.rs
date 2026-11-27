fn abs_i64(x: i64) -> i64 {
    if x < 0 {
        0 - x
    } else {
        x
    }
}

// Returns a 2-element vector: [ total_tilt_of_subtree, sum_of_subtree ].
// The recursion itself contains no `if`/branch after the recursive calls:
// the absolute value is delegated to the (non-recursive) `abs_i64` helper,
// which is what previously tripped Charon/Aeneas ("could not match contexts").
fn dfs(node: &Tree) -> Vec<i64> {
    match node {
        Tree::Null => {
            let mut v: Vec<i64> = Vec::new();
            v.push(0); // tilt
            v.push(0); // sum
            v
        }
        Tree::Node(value, left, right) => {
            let lv = dfs(&**left);
            let rv = dfs(&**right);

            let ltilt = lv[0];
            let lsum = lv[1];
            let rtilt = rv[0];
            let rsum = rv[1];

            let diff = abs_i64(lsum - rsum);

            let mut v: Vec<i64> = Vec::new();
            v.push(diff + ltilt + rtilt);   // tilt of this subtree
            v.push(*value + lsum + rsum);   // sum of this subtree
            v
        }
    }
}

pub fn find_tilt(root: &Tree) -> i64 {
    let r = dfs(root);
    r[0]
}
