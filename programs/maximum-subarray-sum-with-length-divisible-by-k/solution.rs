pub fn max_subarray_sum(nums: &[i64], k: i64) -> i64 {
    let sent: i64 = 1000000000000000000;
    let n: usize = nums.len();
    let kk: usize = k as usize;

    let mut min_pref: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < kk {
        min_pref.push(sent);
        t += 1;
    }

    if kk > 0 {
        min_pref[0] = 0;
    }

    let mut pref: i64 = 0;
    let mut best: i64 = -sent;
    let mut j: usize = 0;

    while j < n {
        pref = pref + nums[j];
        let idx: usize = j + 1;
        let r: usize = idx % kk;

        if min_pref[r] != sent {
            let cand: i64 = pref - min_pref[r];
            if cand > best {
                best = cand;
            }
        }

        if pref < min_pref[r] {
            min_pref[r] = pref;
        }

        j += 1;
    }

    best
}
