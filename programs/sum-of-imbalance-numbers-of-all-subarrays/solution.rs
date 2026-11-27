fn binary_find(vals: &[i64], target: i64) -> i64 {
    let mut lo: usize = 0;
    let mut hi: usize = vals.len();
    let mut res: i64 = -1;
    let mut searching: bool = true;

    while lo < hi && searching {
        let mid: usize = (lo + hi) / 2;
        if vals[mid] == target {
            res = mid as i64;
            searching = false;
        } else if vals[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    res
}

pub fn sum_imbalance_numbers(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }

    let mut sorted: Vec<i64> = Vec::new();
    for i in 0..n {
        sorted.push(nums[i]);
    }

    for i in 1..n {
        let key: i64 = sorted[i];
        let mut j: usize = i;
        let mut shifting: bool = true;

        while j > 0 && shifting {
            if sorted[j - 1] > key {
                sorted[j] = sorted[j - 1];
                j -= 1;
            } else {
                shifting = false;
            }
        }

        sorted[j] = key;
    }

    let mut uniq: Vec<i64> = Vec::new();
    for i in 0..n {
        if i == 0 || sorted[i] != sorted[i - 1] {
            uniq.push(sorted[i]);
        }
    }

    let m: usize = uniq.len();

    let mut ranks: Vec<i64> = Vec::new();
    let mut left_rank: Vec<i64> = Vec::new();
    let mut right_rank: Vec<i64> = Vec::new();

    for i in 0..n {
        let x: i64 = nums[i];
        ranks.push(binary_find(&uniq, x));
        left_rank.push(binary_find(&uniq, x - 1));
        right_rank.push(binary_find(&uniq, x + 1));
    }

    let mut total: i64 = 0;

    for l in 0..n {
        let mut seen: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < m {
            seen.push(0);
            k += 1;
        }

        let mut groups: i64 = 0;

        for r in l..n {
            let idx: usize = ranks[r] as usize;

            if seen[idx] == 0 {
                seen[idx] = 1;

                let mut left_present: bool = false;
                let li: i64 = left_rank[r];
                if li >= 0 {
                    let lix: usize = li as usize;
                    if seen[lix] == 1 {
                        left_present = true;
                    }
                }

                let mut right_present: bool = false;
                let ri: i64 = right_rank[r];
                if ri >= 0 {
                    let rix: usize = ri as usize;
                    if seen[rix] == 1 {
                        right_present = true;
                    }
                }

                if left_present && right_present {
                    groups -= 1;
                } else if !left_present && !right_present {
                    groups += 1;
                }
            }

            total += groups - 1;
        }
    }

    total
}
