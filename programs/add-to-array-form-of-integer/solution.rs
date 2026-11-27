pub fn add_to_array_form(num: &[i64], k: i64) -> Vec<i64> {
    let mut res: Vec<i64> = Vec::new();
    let mut i: usize = num.len();
    let mut carry: i64 = k;

    while i > 0 || carry > 0 {
        let mut sum: i64 = carry;
        if i > 0 {
            i = i - 1;
            sum = sum + num[i];
        }
        res.push(sum % 10);
        carry = sum / 10;
    }

    let mut left: usize = 0;
    let mut right: usize = res.len();
    while left < right {
        right = right - 1;
        if left < right {
            let tmp: i64 = res[left];
            res[left] = res[right];
            res[right] = tmp;
        }
        left = left + 1;
    }

    res
}
