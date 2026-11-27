pub fn find_least_num_of_unique_ints(arr: &[i64], k: i64) -> i64 {
    let n = arr.len();
    let mut vals: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i < n {
        vals.push(arr[i]);
        i += 1;
    }

    vals.sort();

    let mut freqs: Vec<i64> = Vec::new();
    let mut j = 0usize;

    while j < n {
        let cur = vals[j];
        let mut cnt: i64 = 0;

        while j < n && vals[j] == cur {
            cnt += 1;
            j += 1;
        }

        freqs.push(cnt);
    }

    freqs.sort();

    let m = freqs.len();
    let mut unique: i64 = 0;
    let mut idx = 0usize;

    while idx < m {
        unique += 1;
        idx += 1;
    }

    let mut rem = k;
    idx = 0;

    while idx < m {
        let f = freqs[idx];

        if rem >= f {
            rem -= f;
            unique -= 1;
            idx += 1;
        } else {
            break;
        }
    }

    unique
}
