pub fn sum_of_three(num: i64) -> Vec<i64> {
    if num % 3 != 0 {
        return Vec::new();
    }

    let mid = num / 3;
    let mut result: Vec<i64> = Vec::new();
    result.push(mid - 1);
    result.push(mid);
    result.push(mid + 1);
    result
}
