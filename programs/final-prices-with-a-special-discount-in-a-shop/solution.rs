pub fn final_prices(prices: &[i64]) -> Vec<i64> {
    let n = prices.len();
    let mut answer: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        let mut discount: i64 = 0;
        let mut j: usize = i + 1;

        while j < n {
            if prices[j] <= prices[i] {
                discount = prices[j];
                j = n;
            } else {
                j += 1;
            }
        }

        answer.push(prices[i] - discount);
        i += 1;
    }

    answer
}
