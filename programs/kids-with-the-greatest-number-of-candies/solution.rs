pub fn kids_with_candies(candies: &[i64], extraCandies: i64) -> Vec<bool> {
    let n = candies.len();
    if n == 0 {
        return Vec::new();
    }

    let mut max_candies: i64 = candies[0];
    let mut i: usize = 0;
    while i < n {
        if candies[i] > max_candies {
            max_candies = candies[i];
        }
        i += 1;
    }

    let mut result: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        if candies[j] + extraCandies >= max_candies {
            result.push(true);
        } else {
            result.push(false);
        }
        j += 1;
    }

    result
}
