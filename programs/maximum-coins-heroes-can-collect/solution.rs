pub fn maximum_coins(heroes: &[i64], monsters: &[i64], coins: &[i64]) -> Vec<i64> {
    let m = monsters.len();

    // Build an order array of monster indices, then sort it by monster power.
    let mut order: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        order.push(i);
        i += 1;
    }

    // Allocate the temporary array used by iterative merge sort.
    let mut temp: Vec<usize> = Vec::new();
    let mut t: usize = 0;
    while t < m {
        temp.push(0);
        t += 1;
    }

    let mut width: usize = 1;
    while width < m {
        let mut left: usize = 0;
        while left < m {
            let mut mid = left + width;
            if mid > m {
                mid = m;
            }

            let mut right = left + width * 2;
            if right > m {
                right = m;
            }

            let mut a = left;
            let mut b = mid;
            let mut k = left;

            while a < mid && b < right {
                if monsters[order[a]] <= monsters[order[b]] {
                    temp[k] = order[a];
                    a += 1;
                } else {
                    temp[k] = order[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                temp[k] = order[a];
                a += 1;
                k += 1;
            }

            while b < right {
                temp[k] = order[b];
                b += 1;
                k += 1;
            }

            left = right;
        }

        let mut q: usize = 0;
        while q < m {
            order[q] = temp[q];
            q += 1;
        }

        width = width * 2;
    }

    // Build sorted monster powers and prefix sums of their coins.
    let mut powers: Vec<i64> = Vec::new();
    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);

    let mut sum: i64 = 0;
    let mut j: usize = 0;
    while j < m {
        let original_index = order[j];
        powers.push(monsters[original_index]);
        sum += coins[original_index];
        prefix.push(sum);
        j += 1;
    }

    // For each hero, find how many monsters have power <= hero power.
    let mut ans: Vec<i64> = Vec::new();
    let mut h: usize = 0;
    while h < heroes.len() {
        let target = heroes[h];

        let mut lo: usize = 0;
        let mut hi: usize = m;

        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if powers[mid] <= target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        ans.push(prefix[lo]);
        h += 1;
    }

    ans
}
