pub fn cal_points(operations: &[Vec<u8>]) -> i64 {
    let mut scores: Vec<i64> = Vec::new();
    let n_ops = operations.len();
    let mut i: usize = 0;

    while i < n_ops {
        let op = &operations[i];

        if op.len() == 1 && op[0] == b'C' {
            if scores.len() > 0 {
                scores.pop();
            }
        } else if op.len() == 1 && op[0] == b'D' {
            let n = scores.len();
            if n > 0 {
                let value = scores[n - 1] * 2;
                scores.push(value);
            }
        } else if op.len() == 1 && op[0] == b'+' {
            let n = scores.len();
            if n >= 2 {
                let value = scores[n - 1] + scores[n - 2];
                scores.push(value);
            }
        } else {
            let mut value: i64 = 0;
            let mut j: usize = 0;
            let mut negative: bool = false;

            if op.len() > 0 && op[0] == b'-' {
                negative = true;
                j = 1;
            }

            while j < op.len() {
                value = value * 10 + ((op[j] - b'0') as i64);
                j += 1;
            }

            if negative {
                value = -value;
            }

            scores.push(value);
        }

        i += 1;
    }

    let mut total: i64 = 0;
    let mut k: usize = 0;
    while k < scores.len() {
        total += scores[k];
        k += 1;
    }

    total
}
