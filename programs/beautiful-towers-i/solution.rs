pub fn maximum_sum_of_heights(heights: &[i64]) -> i64 {
    let n = heights.len();
    let mut ans: i64 = 0;
    let mut p: usize = 0;

    while p < n {
        let peak = heights[p];
        let mut total = peak;

        let mut prev = peak;
        let mut i = p;
        while i > 0 {
            i -= 1;
            let mut v = heights[i];
            if v > prev {
                v = prev;
            }
            total += v;
            prev = v;
        }

        prev = peak;
        let mut j = p + 1;
        while j < n {
            let mut v = heights[j];
            if v > prev {
                v = prev;
            }
            total += v;
            prev = v;
            j += 1;
        }

        if total > ans {
            ans = total;
        }

        p += 1;
    }

    ans
}
