pub fn invalid_transactions(transactions: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let n = transactions.len();
    let mut out: Vec<Vec<u8>> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let len_i = transactions[i].len();

        let mut c1: usize = 0;
        while c1 < len_i && transactions[i][c1] != b',' {
            c1 += 1;
        }

        let mut c2: usize = c1 + 1;
        while c2 < len_i && transactions[i][c2] != b',' {
            c2 += 1;
        }

        let mut c3: usize = c2 + 1;
        while c3 < len_i && transactions[i][c3] != b',' {
            c3 += 1;
        }

        let mut time_i: i64 = 0;
        let mut k: usize = c1 + 1;
        while k < c2 {
            let d: i64 = (transactions[i][k] as i64) - 48;
            time_i = time_i * 10 + d;
            k += 1;
        }

        let mut amount_i: i64 = 0;
        k = c2 + 1;
        while k < c3 {
            let d: i64 = (transactions[i][k] as i64) - 48;
            amount_i = amount_i * 10 + d;
            k += 1;
        }

        let mut invalid: bool = amount_i > 1000;

        if !invalid {
            let mut j: usize = 0;
            while j < n {
                if i != j {
                    let len_j = transactions[j].len();

                    let mut d1: usize = 0;
                    while d1 < len_j && transactions[j][d1] != b',' {
                        d1 += 1;
                    }

                    let mut same_name: bool = true;
                    if c1 != d1 {
                        same_name = false;
                    } else {
                        let mut p: usize = 0;
                        while p < c1 {
                            if transactions[i][p] != transactions[j][p] {
                                same_name = false;
                                break;
                            }
                            p += 1;
                        }
                    }

                    if same_name {
                        let mut d2: usize = d1 + 1;
                        while d2 < len_j && transactions[j][d2] != b',' {
                            d2 += 1;
                        }

                        let mut d3: usize = d2 + 1;
                        while d3 < len_j && transactions[j][d3] != b',' {
                            d3 += 1;
                        }

                        let city_len_i = len_i - (c3 + 1);
                        let city_len_j = len_j - (d3 + 1);

                        let mut same_city: bool = true;
                        if city_len_i != city_len_j {
                            same_city = false;
                        } else {
                            let mut p: usize = 0;
                            while p < city_len_i {
                                if transactions[i][c3 + 1 + p] != transactions[j][d3 + 1 + p] {
                                    same_city = false;
                                    break;
                                }
                                p += 1;
                            }
                        }

                        if !same_city {
                            let mut time_j: i64 = 0;
                            let mut q: usize = d1 + 1;
                            while q < d2 {
                                let d: i64 = (transactions[j][q] as i64) - 48;
                                time_j = time_j * 10 + d;
                                q += 1;
                            }

                            let mut diff_time = time_i - time_j;
                            if diff_time < 0 {
                                diff_time = -diff_time;
                            }

                            if diff_time <= 60 {
                                invalid = true;
                            }
                        }
                    }
                }

                if invalid {
                    break;
                }

                j += 1;
            }
        }

        if invalid {
            let mut row: Vec<u8> = Vec::new();
            let mut p: usize = 0;
            while p < len_i {
                row.push(transactions[i][p]);
                p += 1;
            }
            out.push(row);
        }

        i += 1;
    }

    out
}
