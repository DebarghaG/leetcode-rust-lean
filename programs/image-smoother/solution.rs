pub fn image_smoother(img: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = img.len();
    if m == 0 {
        return Vec::new();
    }
    let n = img[0].len();
    if n == 0 {
        return Vec::new();
    }

    let mut out: Vec<Vec<i64>> = Vec::new();

    let mut i: usize = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();

        let r0 = if i == 0 { 0 } else { i - 1 };
        let r1 = if i + 1 < m { i + 1 } else { i };

        let mut j: usize = 0;
        while j < n {
            let c0 = if j == 0 { 0 } else { j - 1 };
            let c1 = if j + 1 < n { j + 1 } else { j };

            let mut sum: i64 = 0;
            let mut count: i64 = 0;

            let mut r: usize = r0;
            while r <= r1 {
                let mut c: usize = c0;
                while c <= c1 {
                    sum = sum + img[r][c];
                    count = count + 1;
                    c = c + 1;
                }
                r = r + 1;
            }

            row.push(sum / count);
            j = j + 1;
        }

        out.push(row);
        i = i + 1;
    }

    out
}
