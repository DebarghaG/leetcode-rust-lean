pub fn get_min_swaps(num: &[u8], k: i64) -> i64 {
    let n = num.len();
    if n < 2 {
        return 0;
    }

    let mut target: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        target.push(num[i]);
        i += 1;
    }

    let mut done: i64 = 0;
    while done < k {
        let mut pivot: usize = n;
        let mut idx: usize = n - 1;

        while idx > 0 {
            idx -= 1;
            if target[idx] < target[idx + 1] {
                pivot = idx;
                break;
            }
        }

        if pivot == n {
            break;
        }

        let mut j: usize = n - 1;
        while target[j] <= target[pivot] {
            j -= 1;
        }

        let tmp = target[pivot];
        target[pivot] = target[j];
        target[j] = tmp;

        let mut left: usize = pivot + 1;
        let mut right: usize = n - 1;
        while left < right {
            let tmp2 = target[left];
            target[left] = target[right];
            target[right] = tmp2;
            left += 1;
            right -= 1;
        }

        done += 1;
    }

    let mut current: Vec<u8> = Vec::new();
    i = 0;
    while i < n {
        current.push(num[i]);
        i += 1;
    }

    let mut swaps: i64 = 0;
    let mut pos: usize = 0;
    while pos < n {
        let mut j: usize = pos;
        while j < n && current[j] != target[pos] {
            j += 1;
        }

        if j < n {
            swaps += (j - pos) as i64;

            while j > pos {
                let tmp = current[j];
                current[j] = current[j - 1];
                current[j - 1] = tmp;
                j -= 1;
            }
        }

        pos += 1;
    }

    swaps
}
