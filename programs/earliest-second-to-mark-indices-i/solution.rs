pub fn earliest_second_to_mark_indices(nums: &[i64], change_indices: &[i64]) -> i64 {
    let m = change_indices.len();
    let mut result: i64 = -1;

    if can_mark_all(nums, change_indices, m) {
        let mut lo: usize = 1;
        let mut hi: usize = m;

        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if can_mark_all(nums, change_indices, mid) {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }

        result = lo as i64;
    }

    result
}

fn can_mark_all(nums: &[i64], change_indices: &[i64], seconds: usize) -> bool {
    let n = nums.len();

    // last[j] will hold the last second (index) at which index j can be marked
    // within the first `seconds` seconds; `seconds` means "never appears".
    let mut last: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        last.push(seconds);
        i += 1;
    }

    i = 0;
    while i < seconds {
        let idx = (change_indices[i] - 1) as usize;
        last[idx] = i;
        i += 1;
    }

    let mut ok: bool = true;

    // Every index must appear at least once within the window.
    let mut j: usize = 0;
    while j < n {
        if last[j] == seconds {
            ok = false;
        }
        j += 1;
    }

    // Greedy scan: accumulate free decrement "seconds"; on the last occurrence
    // of an index spend nums[idx] of them to be able to mark it.
    let mut available: i64 = 0;
    i = 0;
    while i < seconds {
        if ok {
            let idx = (change_indices[i] - 1) as usize;
            if last[idx] == i {
                let need = nums[idx];
                if available < need {
                    ok = false;
                } else {
                    available -= need;
                }
            } else {
                available += 1;
            }
        }
        i += 1;
    }

    ok
}
