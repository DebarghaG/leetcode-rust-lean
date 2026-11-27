pub fn can_three_parts_equal_sum(arr: &[i64]) -> bool {
    let n = arr.len();
    if n < 3 {
        return false;
    }

    let mut total: i64 = 0;
    let mut idx: usize = 0;
    while idx < n {
        total = total + arr[idx];
        idx = idx + 1;
    }

    if total % 3 != 0 {
        return false;
    }

    let target: i64 = total / 3;

    let mut first_sum: i64 = 0;
    let mut i: usize = 0;
    let mut first_cut: usize = n;

    while i + 2 < n {
        first_sum = first_sum + arr[i];
        if first_sum == target {
            first_cut = i;
            break;
        }
        i = i + 1;
    }

    if first_cut == n {
        return false;
    }

    let mut second_sum: i64 = 0;
    let mut j: usize = first_cut + 1;

    while j + 1 < n {
        second_sum = second_sum + arr[j];
        if second_sum == target {
            return true;
        }
        j = j + 1;
    }

    false
}
