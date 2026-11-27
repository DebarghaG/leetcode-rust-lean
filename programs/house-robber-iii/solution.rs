fn max2(a: i64, b: i64) -> i64 {
    let mut m: i64 = a;
    if b > m {
        m = b;
    }
    m
}

fn dp(t: &Tree) -> Vec<i64> {
    // Returns [take, skip] for this subtree:
    //   take = best total if we rob this node
    //   skip = best total if we do not rob this node
    let mut out: Vec<i64> = Vec::new();
    match t {
        Tree::Null => {
            out.push(0);
            out.push(0);
        }
        Tree::Node(v, l, r) => {
            let val: i64 = *v;
            let ldp: Vec<i64> = dp(&**l);
            let rdp: Vec<i64> = dp(&**r);

            let ltake: i64 = ldp[0];
            let lskip: i64 = ldp[1];
            let rtake: i64 = rdp[0];
            let rskip: i64 = rdp[1];

            // Rob this node: children must be skipped.
            let take: i64 = val + lskip + rskip;

            // Skip this node: each child contributes its own best.
            let skip: i64 = max2(ltake, lskip) + max2(rtake, rskip);

            out.push(take);
            out.push(skip);
        }
    }
    out
}

pub fn rob(root: &Tree) -> i64 {
    let res: Vec<i64> = dp(root);
    let take: i64 = res[0];
    let skip: i64 = res[1];
    max2(take, skip)
}
