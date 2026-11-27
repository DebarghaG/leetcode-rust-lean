pub fn count_good_triplets(arr: &[i64], a: i64, b: i64, c: i64) -> i64 {
    let n: usize = arr.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;

        while j < n {
            let d_ij = arr[i] - arr[j];
            let abs_ij = if d_ij < 0 { -d_ij } else { d_ij };

            if abs_ij <= a {
                let mut k: usize = j + 1;

                while k < n {
                    let d_jk = arr[j] - arr[k];
                    let abs_jk = if d_jk < 0 { -d_jk } else { d_jk };

                    if abs_jk <= b {
                        let d_ik = arr[i] - arr[k];
                        let abs_ik = if d_ik < 0 { -d_ik } else { d_ik };

                        if abs_ik <= c {
                            count = count + 1;
                        }
                    }

                    k = k + 1;
                }
            }

            j = j + 1;
        }

        i = i + 1;
    }

    count
}
