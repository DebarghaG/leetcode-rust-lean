pub fn max_weight(pizzas: &[i64]) -> i64 {
    let n: usize = pizzas.len();
    let days: usize = n / 4;
    let odd_days: usize = (days + 1) / 2;
    let even_days: usize = days / 2;

    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(pizzas[i]);
        i += 1;
    }
    v.sort();

    let mut ans: i64 = 0;

    let mut k: usize = 0;
    while k < odd_days {
        ans += v[n - 1 - k];
        k += 1;
    }

    let mut j: usize = 0;
    while j < even_days {
        let desc_index: usize = odd_days + 1 + 2 * j;
        let idx: usize = n - 1 - desc_index;
        ans += v[idx];
        j += 1;
    }

    ans
}
