pub fn array_nesting(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut visited: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < n {
        visited.push(false);
        i += 1;
    }

    let mut best: i64 = 0;
    let mut start: usize = 0;

    while start < n {
        if !visited[start] {
            let mut count: i64 = 0;
            let mut cur: usize = start;

            while !visited[cur] {
                visited[cur] = true;
                cur = nums[cur] as usize;
                count += 1;
            }

            if count > best {
                best = count;
            }
        }

        start += 1;
    }

    best
}
