pub fn count_of_arrays(n: i64, m: i64, k: i64) -> i64 {
    let modulo: i64 = 1000000007;

    let even_count: i64 = m / 2;
    let odd_count: i64 = m - even_count;

    let mut dp_even: Vec<i64> = Vec::new();
    let mut dp_odd: Vec<i64> = Vec::new();

    dp_even.push(even_count % modulo);
    dp_odd.push(odd_count % modulo);

    let mut c: i64 = 1;
    while c <= k {
        dp_even.push(0);
        dp_odd.push(0);
        c += 1;
    }

    let mut len: i64 = 1;
    while len < n {
        let mut next_even: Vec<i64> = Vec::new();
        let mut next_odd: Vec<i64> = Vec::new();

        let dp_len: usize = dp_even.len();

        let ne0: i64 = (dp_odd[0] * even_count) % modulo;
        let no0: i64 = (((dp_even[0] + dp_odd[0]) % modulo) * odd_count) % modulo;

        next_even.push(ne0);
        next_odd.push(no0);

        let mut prev: usize = 0;
        let mut curr: usize = 1;

        while curr < dp_len {
            let ne: i64 =
                (((dp_even[prev] + dp_odd[curr]) % modulo) * even_count) % modulo;
            let no: i64 =
                (((dp_even[curr] + dp_odd[curr]) % modulo) * odd_count) % modulo;

            next_even.push(ne);
            next_odd.push(no);

            prev += 1;
            curr += 1;
        }

        dp_even = next_even;
        dp_odd = next_odd;

        len += 1;
    }

    let mut idx: usize = 0;
    let mut cnt: i64 = 0;

    while cnt < k {
        idx += 1;
        cnt += 1;
    }

    (dp_even[idx] + dp_odd[idx]) % modulo
}
