pub fn count_routes(locations: &[i64], start: i64, finish: i64, fuel: i64) -> i64 {
    const MOD: i64 = 1000000007;

    let n = locations.len();
    let max_fuel = fuel as usize;
    let start_idx = start as usize;
    let finish_idx = finish as usize;

    // Sorted copy of positions, used only to canonically index diagonal sums.
    let mut pos: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        pos.push(locations[i]);
        i += 1;
    }

    // Insertion sort; n <= 100.
    let mut a: usize = 1;
    while a < n {
        let key = pos[a];
        let mut b = a;
        while b > 0 && pos[b - 1] > key {
            pos[b] = pos[b - 1];
            b -= 1;
        }
        pos[b] = key;
        a += 1;
    }

    let total_slots = (max_fuel + 1) * n;

    let mut agg_left: Vec<i64> = Vec::new();
    let mut agg_right: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < total_slots {
        agg_left.push(0);
        agg_right.push(0);
        z += 1;
    }

    let mut cur: Vec<i64> = Vec::new();
    let mut cur_left: Vec<usize> = Vec::new();
    let mut cur_right: Vec<usize> = Vec::new();

    let mut q: usize = 0;
    while q < n {
        cur.push(0);
        cur_left.push(0);
        cur_right.push(0);
        q += 1;
    }

    let mut answer: i64 = 0;
    let mut spent: usize = 0;

    while spent <= max_fuel {
        let spent_i64 = spent as i64;

        let mut j: usize = 0;
        while j < n {
            let xj = locations[j];

            // Canonical index for key = spent - xj.
            let lower_left = xj - spent_i64;
            let k_left = lower_bound(&pos, lower_left);
            let canonical_spent_left = spent_i64 - xj + pos[k_left];
            let idx_left = (canonical_spent_left as usize) * n + k_left;

            // Canonical index for key = spent + xj.
            let lower_right = spent_i64 + xj - fuel;
            let k_right = lower_bound(&pos, lower_right);
            let canonical_spent_right = spent_i64 + xj - pos[k_right];
            let idx_right = (canonical_spent_right as usize) * n + k_right;

            let mut value = agg_left[idx_left] + agg_right[idx_right];
            if value >= MOD {
                value -= MOD;
            }

            if spent == 0 && j == start_idx {
                value += 1;
                if value >= MOD {
                    value -= MOD;
                }
            }

            cur[j] = value;
            cur_left[j] = idx_left;
            cur_right[j] = idx_right;

            j += 1;
        }

        let mut j2: usize = 0;
        while j2 < n {
            let value = cur[j2];

            if j2 == finish_idx {
                answer += value;
                if answer >= MOD {
                    answer -= MOD;
                }
            }

            let idx_left = cur_left[j2];
            let idx_right = cur_right[j2];

            let mut left_sum = agg_left[idx_left] + value;
            if left_sum >= MOD {
                left_sum -= MOD;
            }
            agg_left[idx_left] = left_sum;

            let mut right_sum = agg_right[idx_right] + value;
            if right_sum >= MOD {
                right_sum -= MOD;
            }
            agg_right[idx_right] = right_sum;

            j2 += 1;
        }

        spent += 1;
    }

    answer
}

fn lower_bound(a: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = a.len();

    while lo < hi {
        let mid = (lo + hi) / 2;
        if a[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}
