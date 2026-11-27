pub fn num_ways(s: &[u8]) -> i64 {
    let modulo: i64 = 1000000007;
    let n: usize = s.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if s[i] == b'1' {
            total += 1;
        }
        i += 1;
    }

    if total == 0 {
        let m: i64 = n as i64;
        let ans: i64 = ((m - 1) * (m - 2) / 2) % modulo;
        return ans;
    }

    if total % 3 != 0 {
        return 0;
    }

    let part: i64 = total / 3;
    let mut seen: i64 = 0;
    let mut zeros: i64 = 0;
    let mut ways1: i64 = 0;
    let mut ways2: i64 = 0;

    i = 0;
    while i < n {
        if s[i] == b'1' {
            seen += 1;

            if seen == part + 1 {
                ways1 = zeros + 1;
            }

            if seen == 2 * part + 1 {
                ways2 = zeros + 1;
                break;
            }

            zeros = 0;
        } else {
            zeros += 1;
        }

        i += 1;
    }

    let ans: i64 = (ways1 * ways2) % modulo;
    ans
}
