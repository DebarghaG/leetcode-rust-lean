pub fn count_quadruples(first_string: &[u8], second_string: &[u8]) -> i64 {
    let mut first: Vec<i64> = Vec::new();
    let mut last: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < 26 {
        first.push(-1);
        last.push(-1);
        k += 1;
    }

    let n = first_string.len();
    let mut i: usize = 0;
    while i < n {
        let c = (first_string[i] - b'a') as usize;
        if first[c] == -1 {
            first[c] = i as i64;
        }
        i += 1;
    }

    let m = second_string.len();
    let mut j: usize = 0;
    while j < m {
        let c = (second_string[j] - b'a') as usize;
        last[c] = j as i64;
        j += 1;
    }

    let mut min_diff: i64 = 1000000000;
    let mut count: i64 = 0;

    let mut c: usize = 0;
    while c < 26 {
        if first[c] != -1 && last[c] != -1 {
            let diff = first[c] - last[c];
            if diff < min_diff {
                min_diff = diff;
                count = 1;
            } else if diff == min_diff {
                count += 1;
            }
        }
        c += 1;
    }

    count
}
