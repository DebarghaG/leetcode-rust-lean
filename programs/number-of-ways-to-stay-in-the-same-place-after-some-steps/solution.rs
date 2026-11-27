pub fn num_ways(steps: i64, arrLen: i64) -> i64 {
    let modulus: i64 = 1000000007;

    let steps_usize: usize = steps as usize;
    let arr_len_usize: usize = arrLen as usize;

    // Positions farther than steps / 2 can never return to index 0 in time.
    let max_possible: usize = steps_usize / 2 + 1;
    let n: usize = if arr_len_usize < max_possible {
        arr_len_usize
    } else {
        max_possible
    };

    let mut prev: Vec<i64> = Vec::new();
    prev.push(1);

    let mut idx: usize = 1;
    while idx < n {
        prev.push(0);
        idx += 1;
    }

    let mut curr: Vec<i64> = Vec::new();
    idx = 0;
    while idx < n {
        curr.push(0);
        idx += 1;
    }

    let mut step: usize = 0;
    while step < steps_usize {
        let mut pos: usize = 0;
        while pos < n {
            let mut ways: i64 = prev[pos];

            if pos > 0 {
                ways = (ways + prev[pos - 1]) % modulus;
            }

            if pos + 1 < n {
                ways = (ways + prev[pos + 1]) % modulus;
            }

            curr[pos] = ways;
            pos += 1;
        }

        let mut copy_idx: usize = 0;
        while copy_idx < n {
            prev[copy_idx] = curr[copy_idx];
            copy_idx += 1;
        }

        step += 1;
    }

    prev[0]
}
