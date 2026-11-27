pub fn max_hamming_distances(nums: &[i64], m: i64) -> Vec<i64> {
    let mut n_states: i64 = 1;
    let mut t: i64 = 0;
    while t < m {
        n_states = n_states * 2;
        t += 1;
    }

    let n_usize = n_states as usize;

    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        dist.push(-1);
        i += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    let n = nums.len();

    let mut j: usize = 0;
    while j < n {
        let x = nums[j];
        let xi = x as usize;
        if dist[xi] == -1 {
            dist[xi] = 0;
            queue.push(x);
        }
        j += 1;
    }

    let mut head: usize = 0;
    while head < queue.len() {
        let cur = queue[head];
        let cur_idx = cur as usize;

        let mut bit: i64 = 1;
        let mut b: i64 = 0;
        while b < m {
            let digit = (cur / bit) % 2;
            let mut nb_i = cur;
            if digit == 0 {
                nb_i = cur + bit;
            } else {
                nb_i = cur - bit;
            }

            let nb = nb_i as usize;
            if dist[nb] == -1 {
                dist[nb] = dist[cur_idx] + 1;
                queue.push(nb_i);
            }

            bit = bit * 2;
            b += 1;
        }

        head += 1;
    }

    let full = n_states - 1;
    let mut answer: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < n {
        let x = nums[k];
        let complement = full - x;
        let ci = complement as usize;
        answer.push(m - dist[ci]);
        k += 1;
    }

    answer
}
