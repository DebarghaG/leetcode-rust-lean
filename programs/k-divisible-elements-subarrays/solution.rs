pub fn count_distinct(nums: &[i64], k: i64, p: i64) -> i64 {
    let n = nums.len();

    let mut node_vals: Vec<Vec<i64>> = Vec::new();
    let mut node_children: Vec<Vec<usize>> = Vec::new();

    node_vals.push(Vec::new());
    node_children.push(Vec::new());

    let mut ans: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let mut cur: usize = 0;
        let mut divisible_count: i64 = 0;
        let mut j: usize = i;

        while j < n {
            if nums[j] % p == 0 {
                divisible_count += 1;
            }

            if divisible_count > k {
                break;
            }

            let val = nums[j];

            let mut idx: usize = 0;
            let mut found: bool = false;
            let mut next: usize = 0;
            let clen = node_vals[cur].len();

            while idx < clen {
                if node_vals[cur][idx] == val {
                    next = node_children[cur][idx];
                    found = true;
                    break;
                }
                idx += 1;
            }

            if !found {
                next = node_vals.len();

                node_vals.push(Vec::new());
                node_children.push(Vec::new());

                node_vals[cur].push(val);
                node_children[cur].push(next);

                ans += 1;
            }

            cur = next;
            j += 1;
        }

        i += 1;
    }

    ans
}
