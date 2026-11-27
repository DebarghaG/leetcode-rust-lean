pub fn find_rle_array(encoded1: &[Vec<i64>], encoded2: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n1 = encoded1.len();
    let n2 = encoded2.len();

    let mut out: Vec<Vec<i64>> = Vec::new();

    let mut i: usize = 0;
    let mut j: usize = 0;

    let mut rem1: i64 = 0;
    let mut rem2: i64 = 0;

    if n1 > 0 {
        rem1 = encoded1[0][1];
    }
    if n2 > 0 {
        rem2 = encoded2[0][1];
    }

    let mut pending_val: i64 = 0;
    let mut pending_freq: i64 = 0;

    while i < n1 && j < n2 {
        let v1 = encoded1[i][0];
        let v2 = encoded2[j][0];
        let prod = v1 * v2;

        let mut take: i64 = rem1;
        if rem2 < rem1 {
            take = rem2;
        }

        if pending_freq == 0 {
            pending_val = prod;
            pending_freq = take;
        } else if pending_val == prod {
            pending_freq = pending_freq + take;
        } else {
            let mut row: Vec<i64> = Vec::new();
            row.push(pending_val);
            row.push(pending_freq);
            out.push(row);

            pending_val = prod;
            pending_freq = take;
        }

        rem1 = rem1 - take;
        rem2 = rem2 - take;

        if rem1 == 0 {
            i = i + 1;
            if i < n1 {
                rem1 = encoded1[i][1];
            }
        }

        if rem2 == 0 {
            j = j + 1;
            if j < n2 {
                rem2 = encoded2[j][1];
            }
        }
    }

    if pending_freq > 0 {
        let mut row: Vec<i64> = Vec::new();
        row.push(pending_val);
        row.push(pending_freq);
        out.push(row);
    }

    out
}
