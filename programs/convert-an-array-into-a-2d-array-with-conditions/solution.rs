pub fn find_matrix(nums: &[i64]) -> Vec<Vec<i64>> {
    let n = nums.len();

    let mut maxv: i64 = 0;
    let mut i = 0usize;
    while i < n {
        if nums[i] > maxv {
            maxv = nums[i];
        }
        i += 1;
    }

    let size = (maxv as usize) + 2;
    let mut freq: Vec<i64> = Vec::new();
    let mut used: Vec<bool> = Vec::new();
    i = 0usize;
    while i < size {
        freq.push(0);
        used.push(false);
        i += 1;
    }

    i = 0usize;
    while i < n {
        let v = nums[i] as usize;
        freq[v] = freq[v] + 1;
        i += 1;
    }

    let mut maxfreq: i64 = 0;
    i = 0usize;
    while i < size {
        if freq[i] > maxfreq {
            maxfreq = freq[i];
        }
        i += 1;
    }

    let mut rows: Vec<Vec<i64>> = Vec::new();
    i = 0usize;
    while i < maxfreq as usize {
        rows.push(Vec::new());
        i += 1;
    }

    i = 0usize;
    while i < n {
        let v = nums[i] as usize;
        if !used[v] {
            used[v] = true;
            let count = freq[v] as usize;
            let mut r = 0usize;
            while r < count {
                rows[r].push(nums[i]);
                r += 1;
            }
        }
        i += 1;
    }

    rows
}
