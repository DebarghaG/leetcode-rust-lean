fn find_index(vals: &[i64], x: i64) -> usize {
    let n = vals.len();
    let mut lo: usize = 0;
    let mut hi: usize = n;

    while lo < hi {
        let mid = (lo + hi) / 2;
        if vals[mid] == x {
            return mid;
        }
        if vals[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    n
}

pub fn num_factored_binary_trees(arr: &[i64]) -> i64 {
    let n = arr.len();
    let md: i64 = 1000000007;

    let mut vals: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        vals.push(arr[i]);
        i += 1;
    }

    let mut a = 0;
    while a < n {
        let mut best = a;
        let mut b = a + 1;
        while b < n {
            if vals[b] < vals[best] {
                best = b;
            }
            b += 1;
        }
        if best != a {
            let tmp = vals[a];
            vals[a] = vals[best];
            vals[best] = tmp;
        }
        a += 1;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        dp.push(1);
        i += 1;
    }

    let mut i = 0;
    while i < n {
        let target = vals[i];
        let mut ways: i64 = 1;

        let mut j = 0;
        while j < i {
            let factor = vals[j];

            if target % factor == 0 {
                let other = target / factor;
                let k = find_index(&vals, other);

                if k < n {
                    let add = (dp[j] * dp[k]) % md;
                    ways = (ways + add) % md;
                }
            }

            j += 1;
        }

        dp[i] = ways;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut i = 0;
    while i < n {
        ans = (ans + dp[i]) % md;
        i += 1;
    }

    ans
}
