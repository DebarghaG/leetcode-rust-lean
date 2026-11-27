pub fn visible_mountains(peaks: &[Vec<i64>]) -> i64 {
    let n = peaks.len();
    if n == 0 {
        return 0;
    }

    let base: i64 = 300000;
    let offset: i64 = 200000;
    let max_r_const: i64 = 200000;

    let mut keys: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let x = peaks[i][0];
        let y = peaks[i][1];
        let l = x - y;
        let r = x + y;

        // Sort primarily by l ascending, then by r descending.
        let key = (l + offset) * base + (max_r_const - r);
        keys.push(key);
        i += 1;
    }

    // Manual heapsort of keys in ascending order.
    let m = keys.len();
    if m > 1 {
        let mut start: usize = m / 2;
        while start > 0 {
            start -= 1;

            let mut root: usize = start;
            while root < m {
                let child = root * 2 + 1;
                if child >= m {
                    break;
                }

                let mut largest: usize = root;
                if keys[child] > keys[largest] {
                    largest = child;
                }

                let right = child + 1;
                if right < m && keys[right] > keys[largest] {
                    largest = right;
                }

                if largest == root {
                    break;
                }

                let tmp_build = keys[root];
                keys[root] = keys[largest];
                keys[largest] = tmp_build;
                root = largest;
            }
        }

        let mut end: usize = m;
        while end > 1 {
            let tmp_extract = keys[0];
            keys[0] = keys[end - 1];
            keys[end - 1] = tmp_extract;
            end -= 1;

            let mut root: usize = 0;
            while root < end {
                let child = root * 2 + 1;
                if child >= end {
                    break;
                }

                let mut largest: usize = root;
                if keys[child] > keys[largest] {
                    largest = child;
                }

                let right = child + 1;
                if right < end && keys[right] > keys[largest] {
                    largest = right;
                }

                if largest == root {
                    break;
                }

                let tmp_sift = keys[root];
                keys[root] = keys[largest];
                keys[largest] = tmp_sift;
                root = largest;
            }
        }
    }

    let mut ans: i64 = 0;
    let mut max_r: i64 = -1;
    let mut idx: usize = 0;

    while idx < m {
        let key = keys[idx];
        let rem = key % base;
        let r = max_r_const - rem;

        let mut j: usize = idx + 1;
        while j < m && keys[j] == key {
            j += 1;
        }

        // A unique interval is visible exactly when its right endpoint
        // is strictly larger than every previously seen right endpoint.
        if j - idx == 1 && r > max_r {
            ans += 1;
        }

        if r > max_r {
            max_r = r;
        }

        idx = j;
    }

    ans
}
