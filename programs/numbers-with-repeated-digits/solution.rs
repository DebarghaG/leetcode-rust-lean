pub fn num_dup_digits_at_most_n(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    // Extract the decimal digits of n into most-significant-first order.
    let mut temp: i64 = n;
    let mut rev: Vec<i64> = Vec::new();
    while temp > 0 {
        rev.push(temp % 10);
        temp = temp / 10;
    }

    let len: usize = rev.len();
    let mut digits: Vec<i64> = Vec::new();
    let mut idx: usize = len;
    while idx > 0 {
        idx = idx - 1;
        digits.push(rev[idx]);
    }

    // Count positive integers <= n with all distinct digits.
    let mut unique: i64 = 0;

    // Count all valid numbers with fewer digits than n.
    let mut k: usize = 1;
    while k < len {
        // First digit: 9 choices. Remaining k - 1 digits:
        // choose ordered from 9 available digits.
        let mut prod: i64 = 1;
        let mut j: usize = 0;
        while j < k - 1 {
            prod = prod * (9 - (j as i64));
            j = j + 1;
        }
        unique = unique + 9 * prod;
        k = k + 1;
    }

    // Count valid numbers with the same length as n and <= n.
    let mut used: Vec<bool> = Vec::new();
    let mut z: usize = 0;
    while z < 10 {
        used.push(false);
        z = z + 1;
    }

    let mut i: usize = 0;
    let mut valid_prefix: bool = true;

    while i < len && valid_prefix {
        let cur: i64 = digits[i];

        // Try placing a smaller digit at position i.
        let mut d: i64 = 0;
        while d < cur {
            let mut ok: bool = true;

            if i == 0 && d == 0 {
                ok = false;
            }

            let du: usize = d as usize;
            if ok && used[du] {
                ok = false;
            }

            if ok {
                let mut used_count: i64 = 1; // include candidate d
                let mut u: usize = 0;
                while u < 10 {
                    if used[u] {
                        used_count = used_count + 1;
                    }
                    u = u + 1;
                }

                let available: i64 = 10 - used_count;
                let rem: i64 = (len - i - 1) as i64;

                let mut ways: i64 = 0;
                if rem <= available {
                    ways = 1;
                    let mut t: i64 = 0;
                    while t < rem {
                        ways = ways * (available - t);
                        t = t + 1;
                    }
                }

                unique = unique + ways;
            }

            d = d + 1;
        }

        // Continue with the actual digit of n.
        let cu: usize = cur as usize;
        if i == 0 && cur == 0 {
            valid_prefix = false;
        } else if used[cu] {
            valid_prefix = false;
        } else {
            used[cu] = true;
            i = i + 1;
        }
    }

    // n itself has all distinct digits.
    if valid_prefix {
        unique = unique + 1;
    }

    n - unique
}
