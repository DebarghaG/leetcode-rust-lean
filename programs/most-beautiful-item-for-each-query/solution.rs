pub fn maximum_beauty(items: &[Vec<i64>], queries: &[i64]) -> Vec<i64> {
    let n = items.len();

    let mut prices: Vec<i64> = Vec::new();
    let mut beauties: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        prices.push(items[i][0]);
        beauties.push(items[i][1]);
        i += 1;
    }

    // Bottom-up merge sort by price, carrying beauty along with price.
    let mut width: usize = 1;
    while width < n {
        let mut tmp_prices: Vec<i64> = Vec::new();
        let mut tmp_beauties: Vec<i64> = Vec::new();

        let mut left: usize = 0;
        while left < n {
            let mid = if left + width < n { left + width } else { n };
            let right = if left + width + width < n {
                left + width + width
            } else {
                n
            };

            let mut i1 = left;
            let mut i2 = mid;

            while i1 < mid && i2 < right {
                if prices[i1] <= prices[i2] {
                    tmp_prices.push(prices[i1]);
                    tmp_beauties.push(beauties[i1]);
                    i1 += 1;
                } else {
                    tmp_prices.push(prices[i2]);
                    tmp_beauties.push(beauties[i2]);
                    i2 += 1;
                }
            }

            while i1 < mid {
                tmp_prices.push(prices[i1]);
                tmp_beauties.push(beauties[i1]);
                i1 += 1;
            }

            while i2 < right {
                tmp_prices.push(prices[i2]);
                tmp_beauties.push(beauties[i2]);
                i2 += 1;
            }

            left = right;
        }

        let mut k = 0;
        while k < n {
            prices[k] = tmp_prices[k];
            beauties[k] = tmp_beauties[k];
            k += 1;
        }

        width = width * 2;
    }

    // Prefix maximum beauty in increasing price order.
    let mut k = 1;
    while k < n {
        if beauties[k] < beauties[k - 1] {
            beauties[k] = beauties[k - 1];
        }
        k += 1;
    }

    let mut answer: Vec<i64> = Vec::new();
    let m = queries.len();

    let mut qi = 0;
    while qi < m {
        let q = queries[qi];

        // Find the number of items with price <= q.
        let mut lo: usize = 0;
        let mut hi: usize = n;

        while lo < hi {
            let mid = (lo + hi) / 2;
            if prices[mid] <= q {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        if lo == 0 {
            answer.push(0);
        } else {
            answer.push(beauties[lo - 1]);
        }

        qi += 1;
    }

    answer
}
