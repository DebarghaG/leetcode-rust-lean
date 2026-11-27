pub fn find_longest_chain(pairs: &[Vec<i64>]) -> i64 {
    let n = pairs.len();
    if n == 0 {
        return 0;
    }

    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        starts.push(pairs[i][0]);
        ends.push(pairs[i][1]);
        i += 1;
    }

    // Stable insertion sort by the right endpoint.
    let mut i = 1;
    while i < n {
        let key_start = starts[i];
        let key_end = ends[i];
        let mut j = i;

        while j > 0 && ends[j - 1] > key_end {
            starts[j] = starts[j - 1];
            ends[j] = ends[j - 1];
            j -= 1;
        }

        starts[j] = key_start;
        ends[j] = key_end;
        i += 1;
    }

    let mut count: i64 = 0;
    let mut last_end: i64 = 0;
    let mut have_last: bool = false;

    let mut k = 0;
    while k < n {
        let left = starts[k];
        if !have_last || left > last_end {
            last_end = ends[k];
            have_last = true;
            count += 1;
        }
        k += 1;
    }

    count
}
