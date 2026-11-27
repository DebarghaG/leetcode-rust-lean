pub fn number_of_arithmetic_slices(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 3 {
        return 0;
    }

    let mut diffs: Vec<Vec<i64>> = Vec::new();
    let mut counts: Vec<Vec<i64>> = Vec::new();

    diffs.push(Vec::new());
    counts.push(Vec::new());

    let mut ans: i64 = 0;
    let mut i: usize = 1;

    while i < n {
        let mut temp_d: Vec<i64> = Vec::new();
        let mut temp_inc: Vec<i64> = Vec::new();

        let mut j: usize = 0;
        while j < i {
            let d = nums[i] - nums[j];

            let row_d = &diffs[j];
            let row_c = &counts[j];

            let mut lo: usize = 0;
            let mut hi: usize = row_d.len();

            while lo < hi {
                let mid = (lo + hi) / 2;
                if row_d[mid] < d {
                    lo = mid + 1;
                } else {
                    hi = mid;
                }
            }

            let mut cj: i64 = 0;
            if lo < row_d.len() && row_d[lo] == d {
                cj = row_c[lo];
            }

            ans += cj;
            temp_d.push(d);
            temp_inc.push(cj + 1);

            j += 1;
        }

        let mut sorted_d: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < temp_d.len() {
            sorted_d.push(temp_d[k]);
            k += 1;
        }
        sorted_d.sort();

        let mut uniq_d: Vec<i64> = Vec::new();
        k = 0;
        while k < sorted_d.len() {
            if uniq_d.len() == 0 || uniq_d[uniq_d.len() - 1] != sorted_d[k] {
                uniq_d.push(sorted_d[k]);
            }
            k += 1;
        }

        let mut uniq_c: Vec<i64> = Vec::new();
        k = 0;
        while k < uniq_d.len() {
            uniq_c.push(0);
            k += 1;
        }

        k = 0;
        while k < temp_d.len() {
            let d = temp_d[k];
            let inc = temp_inc[k];

            let mut lo: usize = 0;
            let mut hi: usize = uniq_d.len();

            while lo < hi {
                let mid = (lo + hi) / 2;
                if uniq_d[mid] < d {
                    lo = mid + 1;
                } else {
                    hi = mid;
                }
            }

            uniq_c[lo] += inc;
            k += 1;
        }

        diffs.push(uniq_d);
        counts.push(uniq_c);

        i += 1;
    }

    ans
}
