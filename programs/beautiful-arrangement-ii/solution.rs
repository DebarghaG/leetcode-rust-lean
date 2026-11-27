pub fn construct_array(n: i64, k: i64) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();
    let mut low: i64 = 1;
    let mut high: i64 = n;
    let mut i: i64 = 0;

    while i < k {
        if i % 2 == 0 {
            ans.push(low);
            low += 1;
        } else {
            ans.push(high);
            high -= 1;
        }
        i += 1;
    }

    if k % 2 == 0 {
        while high >= low {
            ans.push(high);
            high -= 1;
        }
    } else {
        while low <= high {
            ans.push(low);
            low += 1;
        }
    }

    ans
}
