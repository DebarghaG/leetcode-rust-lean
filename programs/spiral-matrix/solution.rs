pub fn spiral_order(matrix: &[Vec<i64>]) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();

    let m = matrix.len();
    if m == 0 {
        return out;
    }

    let n = matrix[0].len();
    if n == 0 {
        return out;
    }

    let mut top: i64 = 0;
    let mut bottom: i64 = m as i64 - 1;
    let mut left: i64 = 0;
    let mut right: i64 = n as i64 - 1;

    while top <= bottom && left <= right {
        let mut j = left;
        while j <= right {
            out.push(matrix[top as usize][j as usize]);
            j += 1;
        }
        top += 1;

        if top > bottom {
            break;
        }

        let mut i = top;
        while i <= bottom {
            out.push(matrix[i as usize][right as usize]);
            i += 1;
        }
        right -= 1;

        if left > right {
            break;
        }

        let mut j = right;
        while j >= left {
            out.push(matrix[bottom as usize][j as usize]);
            j -= 1;
        }
        bottom -= 1;

        if top > bottom {
            break;
        }

        let mut i = bottom;
        while i >= top {
            out.push(matrix[i as usize][left as usize]);
            i -= 1;
        }
        left += 1;
    }

    out
}
