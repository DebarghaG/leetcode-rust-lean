pub fn path_in_zig_zag_tree(label: i64) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();
    let mut cur: i64 = label;

    while cur > 0 {
        ans.push(cur);

        if cur == 1 {
            break;
        }

        let temp: i64 = cur / 2;

        let mut level: i64 = 0;
        let mut pow: i64 = 1;
        while pow * 2 <= temp {
            pow = pow * 2;
            level = level + 1;
        }

        let parent: i64 = pow + pow * 2 - 1 - temp;
        cur = parent;
    }

    let mut out: Vec<i64> = Vec::new();
    let n: usize = ans.len();
    let mut i: usize = n;

    while i > 0 {
        i = i - 1;
        out.push(ans[i]);
    }

    out
}
