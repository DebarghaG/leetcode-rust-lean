pub fn color_red(n: i64) -> Vec<Vec<i64>> {
    let mut ans: Vec<Vec<i64>> = Vec::new();

    let mut first: Vec<i64> = Vec::new();
    first.push(1);
    first.push(1);
    ans.push(first);

    if n <= 1 {
        return ans;
    }

    let mut r: i64 = n;
    while r >= 2 {
        let d = n - r;

        if d % 2 == 0 {
            let start = if d % 4 == 0 { 1 } else { 3 };
            let mut j = start;
            let end = 2 * r - 1;

            while j <= end {
                let mut v: Vec<i64> = Vec::new();
                v.push(r);
                v.push(j);
                ans.push(v);
                j += 2;
            }
        } else {
            let val = if d % 4 == 1 { 2 } else { 1 };

            let mut v: Vec<i64> = Vec::new();
            v.push(r);
            v.push(val);
            ans.push(v);
        }

        r -= 1;
    }

    ans
}
