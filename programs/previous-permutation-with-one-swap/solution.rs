fn find_pivot(arr: &[i64]) -> usize {
    let n = arr.len();
    let mut k: usize = n - 1;
    while k > 0 {
        if arr[k - 1] > arr[k] {
            return k - 1;
        }
        k -= 1;
    }
    n
}

fn find_j0(arr: &[i64], i: usize) -> usize {
    let n = arr.len();
    let mut j: usize = n - 1;
    while j > i {
        if arr[j] < arr[i] {
            return j;
        }
        j -= 1;
    }
    i
}

fn adjust_for_dups(arr: &[i64], i: usize, j0: usize) -> usize {
    let mut j: usize = j0;
    while j > i + 1 && arr[j - 1] == arr[j] {
        j -= 1;
    }
    j
}

pub fn prev_perm_opt1(arr: &[i64]) -> Vec<i64> {
    let n = arr.len();
    let mut res: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        res.push(arr[t]);
        t += 1;
    }

    if n < 2 {
        return res;
    }

    let i = find_pivot(arr);
    if i == n {
        return res;
    }

    let j0 = find_j0(arr, i);
    let j = adjust_for_dups(arr, i, j0);

    let tmp: i64 = res[i];
    res[i] = res[j];
    res[j] = tmp;

    res
}
