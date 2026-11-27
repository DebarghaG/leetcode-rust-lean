pub fn find_shortest_sub_array(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }

    let base: i64 = (n as i64) + 1;
    let mut a: Vec<i64> = Vec::new();
    let mut max_key: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let key: i64 = nums[i] * base + (i as i64);
        a.push(key);
        if key > max_key {
            max_key = key;
        }
        i += 1;
    }

    let mut passes: usize = 0;
    let mut m: i64 = max_key;
    while m > 0 {
        passes += 1;
        m = m >> 8;
    }
    if passes == 0 {
        passes = 1;
    }

    let mut tmp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        tmp.push(0);
        i += 1;
    }

    let mut shift: usize = 0;
    let mut pass: usize = 0;
    while pass < passes {
        let mut count: Vec<i64> = Vec::new();
        let mut d: usize = 0;
        while d < 256 {
            count.push(0);
            d += 1;
        }

        i = 0;
        while i < n {
            let digit: usize = ((a[i] >> shift) & 255) as usize;
            count[digit] = count[digit] + 1;
            i += 1;
        }

        let mut sum: i64 = 0;
        d = 0;
        while d < 256 {
            let c: i64 = count[d];
            count[d] = sum;
            sum += c;
            d += 1;
        }

        i = 0;
        while i < n {
            let digit: usize = ((a[i] >> shift) & 255) as usize;
            let pos: usize = count[digit] as usize;
            tmp[pos] = a[i];
            count[digit] = count[digit] + 1;
            i += 1;
        }

        i = 0;
        while i < n {
            a[i] = tmp[i];
            i += 1;
        }

        shift += 8;
        pass += 1;
    }

    let mut degree: i64 = 0;
    let mut answer: i64 = n as i64;
    let mut p: usize = 0;
    while p < n {
        let group_val: i64 = a[p] / base;
        let mut q: usize = p;
        let mut min_idx: i64 = a[p] % base;
        let mut max_idx: i64 = min_idx;
        let mut scanning: bool = true;

        while q < n && scanning {
            let cur_val: i64 = a[q] / base;
            if cur_val == group_val {
                let idx: i64 = a[q] % base;
                if idx < min_idx {
                    min_idx = idx;
                }
                if idx > max_idx {
                    max_idx = idx;
                }
                q += 1;
            } else {
                scanning = false;
            }
        }

        let group_count: i64 = (q - p) as i64;
        let length: i64 = max_idx - min_idx + 1;

        if group_count > degree {
            degree = group_count;
            answer = length;
        } else if group_count == degree {
            if length < answer {
                answer = length;
            }
        }

        p = q;
    }

    answer
}
