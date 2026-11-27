pub fn intersection(nums: &[Vec<i64>]) -> Vec<i64> {
    let m: usize = nums.len();
    let mut out: Vec<i64> = Vec::new();

    if m == 0 {
        return out;
    }

    let mut count: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 1001 {
        count.push(0);
        k += 1;
    }

    let mut i: usize = 0;
    while i < m {
        let row = &nums[i];
        let i64_i: i64 = i as i64;
        let mut j: usize = 0;

        while j < row.len() {
            let v: i64 = row[j];
            if v >= 1 && v <= 1000 {
                let idx: usize = v as usize;
                if count[idx] == i64_i {
                    count[idx] = count[idx] + 1;
                }
            }
            j += 1;
        }

        i += 1;
    }

    let m_i64: i64 = m as i64;
    let mut v: usize = 1;
    while v <= 1000 {
        if count[v] == m_i64 {
            out.push(v as i64);
        }
        v += 1;
    }

    out
}
