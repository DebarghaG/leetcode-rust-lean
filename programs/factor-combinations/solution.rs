pub fn get_factors(n: i64) -> Vec<Vec<i64>> {
    let mut res: Vec<Vec<i64>> = Vec::new();

    if n < 4 {
        return res;
    }

    let mut q_rem: Vec<i64> = Vec::new();
    let mut q_start: Vec<i64> = Vec::new();
    let mut q_path: Vec<Vec<i64>> = Vec::new();

    q_rem.push(n);
    q_start.push(2);
    q_path.push(Vec::new());

    let mut head: usize = 0;

    while head < q_rem.len() {
        let rem = q_rem[head];
        let start = q_start[head];
        let path_len = q_path[head].len();

        let mut i = start;
        while i * i <= rem {
            if rem % i == 0 {
                let mut combo: Vec<i64> = Vec::new();
                let mut k: usize = 0;
                while k < path_len {
                    combo.push(q_path[head][k]);
                    k += 1;
                }
                combo.push(i);
                combo.push(rem / i);
                res.push(combo);

                let child_rem = rem / i;
                if child_rem >= i * i {
                    let mut child: Vec<i64> = Vec::new();
                    let mut k2: usize = 0;
                    while k2 < path_len {
                        child.push(q_path[head][k2]);
                        k2 += 1;
                    }
                    child.push(i);

                    q_rem.push(child_rem);
                    q_start.push(i);
                    q_path.push(child);
                }
            }

            i += 1;
        }

        head += 1;
    }

    res
}
