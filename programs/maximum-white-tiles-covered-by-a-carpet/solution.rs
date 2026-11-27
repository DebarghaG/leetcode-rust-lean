pub fn maximum_white_tiles(tiles: &[Vec<i64>], carpetLen: i64) -> i64 {
    let n = tiles.len();

    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();
    let mut idx = 0;
    while idx < n {
        starts.push(tiles[idx][0]);
        ends.push(tiles[idx][1]);
        idx += 1;
    }

    let mut tmp_s: Vec<i64> = Vec::new();
    let mut tmp_e: Vec<i64> = Vec::new();
    let mut t = 0;
    while t < n {
        tmp_s.push(0);
        tmp_e.push(0);
        t += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mut mid = left + width;
            if mid > n {
                mid = n;
            }
            let mut right = left + width + width;
            if right > n {
                right = n;
            }

            let mut i = left;
            let mut j = mid;
            let mut k = left;

            while i < mid && j < right {
                if starts[i] <= starts[j] {
                    tmp_s[k] = starts[i];
                    tmp_e[k] = ends[i];
                    i += 1;
                } else {
                    tmp_s[k] = starts[j];
                    tmp_e[k] = ends[j];
                    j += 1;
                }
                k += 1;
            }

            while i < mid {
                tmp_s[k] = starts[i];
                tmp_e[k] = ends[i];
                i += 1;
                k += 1;
            }

            while j < right {
                tmp_s[k] = starts[j];
                tmp_e[k] = ends[j];
                j += 1;
                k += 1;
            }

            left = right;
        }

        let mut c = 0;
        while c < n {
            starts[c] = tmp_s[c];
            ends[c] = tmp_e[c];
            c += 1;
        }

        width = width * 2;
    }

    let m = starts.len();
    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);

    let mut i = 0;
    while i < m {
        let length = ends[i] - starts[i] + 1;
        let prev = prefix[i];
        prefix.push(prev + length);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut j: usize = 0;
    let mut left_i: usize = 0;

    while left_i < m {
        if j < left_i {
            j = left_i;
        }

        let end_pos = starts[left_i] + carpetLen - 1;

        while j + 1 < m && starts[j + 1] <= end_pos {
            j += 1;
        }

        let mut count = prefix[j + 1] - prefix[left_i];
        if ends[j] > end_pos {
            count -= ends[j] - end_pos;
        }

        if count > ans {
            ans = count;
        }

        left_i += 1;
    }

    ans
}
