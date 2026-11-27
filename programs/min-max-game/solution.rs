pub fn min_max_game(nums: &[i64]) -> i64 {
    let mut cur: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < nums.len() {
        cur.push(nums[k]);
        k += 1;
    }

    while cur.len() > 1 {
        let n: usize = cur.len();
        let mut next: Vec<i64> = Vec::new();
        let mut i: usize = 0;

        while i < n / 2 {
            let a: i64 = cur[2 * i];
            let b: i64 = cur[2 * i + 1];

            if i % 2 == 0 {
                if a < b {
                    next.push(a);
                } else {
                    next.push(b);
                }
            } else {
                if a > b {
                    next.push(a);
                } else {
                    next.push(b);
                }
            }

            i += 1;
        }

        cur = next;
    }

    cur[0]
}
