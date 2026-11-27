pub fn max_profit(prices: &[i64], profits: &[i64]) -> i64 {
    let n = prices.len();
    if n < 3 {
        return -1;
    }

    let mut ans: i64 = -1;
    let mut j: usize = 1;

    while j < n - 1 {
        let mut best_left: i64 = -1;
        let mut i: usize = 0;

        while i < j {
            if prices[i] < prices[j] && profits[i] > best_left {
                best_left = profits[i];
            }
            i += 1;
        }

        let mut best_right: i64 = -1;
        let mut k: usize = j + 1;

        while k < n {
            if prices[k] > prices[j] && profits[k] > best_right {
                best_right = profits[k];
            }
            k += 1;
        }

        if best_left >= 0 && best_right >= 0 {
            let total = best_left + profits[j] + best_right;
            if total > ans {
                ans = total;
            }
        }

        j += 1;
    }

    ans
}
