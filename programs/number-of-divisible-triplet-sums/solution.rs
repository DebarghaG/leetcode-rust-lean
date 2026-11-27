pub fn divisible_triplet_count(nums: &[i64], d: i64) -> i64 {
    let n = nums.len();
    let mut residues: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();
    let mut ans: i64 = 0;
    let mut k: usize = 0;

    while k < n {
        let rk = nums[k] % d;
        let target = (d - rk) % d;

        ans += count_pairs_exact_sum(&residues, &counts, target);
        ans += count_pairs_exact_sum(&residues, &counts, target + d);

        let m = residues.len();
        let mut pos: usize = 0;
        let mut found: bool = false;

        while pos < m {
            if residues[pos] == rk {
                found = true;
                break;
            }
            if residues[pos] > rk {
                break;
            }
            pos += 1;
        }

        if found {
            counts[pos] += 1;
        } else {
            residues.push(rk);
            counts.push(1);

            let mut j = residues.len() - 1;
            while j > pos {
                residues[j] = residues[j - 1];
                counts[j] = counts[j - 1];
                j -= 1;
            }

            residues[pos] = rk;
            counts[pos] = 1;
        }

        k += 1;
    }

    ans
}

fn count_pairs_exact_sum(residues: &[i64], counts: &[i64], s: i64) -> i64 {
    let m = residues.len();
    if m == 0 {
        return 0;
    }

    let mut left: usize = 0;
    let mut right: usize = m - 1;
    let mut total: i64 = 0;

    while left < right {
        let sum = residues[left] + residues[right];

        if sum < s {
            left += 1;
        } else if sum > s {
            right -= 1;
        } else {
            total += counts[left] * counts[right];
            left += 1;
            right -= 1;
        }
    }

    if s % 2 == 0 {
        let half = s / 2;
        let mut p: usize = 0;

        while p < m {
            if residues[p] == half {
                let c = counts[p];
                total += c * (c - 1) / 2;
                break;
            }
            if residues[p] > half {
                break;
            }
            p += 1;
        }
    }

    total
}
