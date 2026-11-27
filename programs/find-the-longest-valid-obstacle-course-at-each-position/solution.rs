pub fn longest_obstacle_course_at_each_position(obstacles: &[i64]) -> Vec<i64> {
    let n = obstacles.len();
    let mut ans: Vec<i64> = Vec::new();
    let mut tails: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let x: i64 = obstacles[i];

        let mut lo: usize = 0;
        let mut hi: usize = tails.len();

        // Find the first index whose value is strictly greater than x.
        while lo < hi {
            let mid: usize = lo + (hi - lo) / 2;
            if tails[mid] <= x {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        let pos: usize = lo;

        if pos == tails.len() {
            tails.push(x);
        } else {
            tails[pos] = x;
        }

        ans.push((pos as i64) + 1);
        i += 1;
    }

    ans
}
