pub fn min_operations(boxes: &[u8]) -> Vec<i64> {
    let n = boxes.len();
    let mut ans: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        ans.push(0);
        i += 1;
    }

    let mut count: i64 = 0;
    let mut cost: i64 = 0;
    let mut idx: usize = 0;
    while idx < n {
        ans[idx] = ans[idx] + cost;
        if boxes[idx] == b'1' {
            count += 1;
        }
        cost = cost + count;
        idx += 1;
    }

    count = 0;
    cost = 0;
    idx = n;
    while idx > 0 {
        idx -= 1;
        ans[idx] = ans[idx] + cost;
        if boxes[idx] == b'1' {
            count += 1;
        }
        cost = cost + count;
    }

    ans
}
