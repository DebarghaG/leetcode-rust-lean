pub fn closest_cost(baseCosts: &[i64], toppingCosts: &[i64], target: i64) -> i64 {
    let mut sums: Vec<i64> = Vec::new();
    sums.push(0);

    let m = toppingCosts.len();
    let mut i = 0;
    while i < m {
        let t = toppingCosts[i];
        let old_len = sums.len();
        let mut additions: Vec<i64> = Vec::new();

        let mut j = 0;
        while j < old_len {
            additions.push(sums[j] + t);
            additions.push(sums[j] + 2 * t);
            j += 1;
        }

        let mut k = 0;
        while k < additions.len() {
            sums.push(additions[k]);
            k += 1;
        }

        i += 1;
    }

    let mut best = baseCosts[0];
    let mut bi = 0;
    while bi < baseCosts.len() {
        let mut si = 0;
        while si < sums.len() {
            let total = baseCosts[bi] + sums[si];
            let diff = total - target;
            let abs_diff = if diff < 0 { -diff } else { diff };

            let best_diff = best - target;
            let best_abs_diff = if best_diff < 0 { -best_diff } else { best_diff };

            if abs_diff < best_abs_diff || (abs_diff == best_abs_diff && total < best) {
                best = total;
            }

            si += 1;
        }
        bi += 1;
    }

    best
}
