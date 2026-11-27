pub fn find_max_value_of_equation(points: &[Vec<i64>], k: i64) -> i64 {
    let n = points.len();
    let mut dq: Vec<usize> = Vec::new();
    let mut head: usize = 0;
    let mut ans: i64 = -1000000000000000000;

    let mut j: usize = 0;
    while j < n {
        while head < dq.len() {
            let i = dq[head];
            if points[j][0] - points[i][0] > k {
                head += 1;
            } else {
                break;
            }
        }

        if head < dq.len() {
            let i = dq[head];
            let value = points[j][1] + points[j][0] + points[i][1] - points[i][0];
            if value > ans {
                ans = value;
            }
        }

        let cur_value = points[j][1] - points[j][0];
        while dq.len() > head {
            let last = dq[dq.len() - 1];
            let last_value = points[last][1] - points[last][0];
            if last_value <= cur_value {
                dq.pop();
            } else {
                break;
            }
        }

        dq.push(j);
        j += 1;
    }

    ans
}
