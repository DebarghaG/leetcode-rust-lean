fn dfs(t: &Tree, distance: i64) -> Vec<i64> {
    match t {
        Tree::Null => {
            let mut res: Vec<i64> = Vec::new();
            res.push(0);
            res
        }
        Tree::Node(_, left, right) => {
            let left_null = match &**left {
                Tree::Null => true,
                Tree::Node(_, _, _) => false,
            };
            let right_null = match &**right {
                Tree::Null => true,
                Tree::Node(_, _, _) => false,
            };

            if left_null && right_null {
                let mut res: Vec<i64> = Vec::new();
                res.push(0);
                res.push(0);
                return res;
            }

            let lres = dfs(&**left, distance);
            let rres = dfs(&**right, distance);

            let mut count: i64 = 0;
            if lres.len() > 0 {
                count += lres[0];
            }
            if rres.len() > 0 {
                count += rres[0];
            }

            let mut i: usize = 1;
            while i < lres.len() {
                let mut j: usize = 1;
                while j < rres.len() {
                    if lres[i] + rres[j] + 2 <= distance {
                        count += 1;
                    }
                    j += 1;
                }
                i += 1;
            }

            let mut out: Vec<i64> = Vec::new();
            out.push(count);

            let mut a: usize = 1;
            while a < lres.len() {
                let d: i64 = lres[a] + 1;
                if d <= distance {
                    out.push(d);
                }
                a += 1;
            }

            let mut b: usize = 1;
            while b < rres.len() {
                let d: i64 = rres[b] + 1;
                if d <= distance {
                    out.push(d);
                }
                b += 1;
            }

            out
        }
    }
}

pub fn count_pairs(root: &Tree, distance: i64) -> i64 {
    let res = dfs(root, distance);
    if res.len() > 0 {
        res[0]
    } else {
        0
    }
}
