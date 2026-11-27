pub fn flip_lights(n: i64, presses: i64) -> i64 {
    let k: i64 = if n < 6 { n } else { 6 };
    let mut seen: Vec<i64> = Vec::new();
    let mut unique_count: i64 = 0;

    let mut code: i64 = 0;
    while code < 16 {
        let mut bits: i64 = 0;
        let mut temp: i64 = code;
        while temp > 0 {
            if temp % 2 == 1 {
                bits += 1;
            }
            temp = temp / 2;
        }

        let mut reachable: bool = false;
        if bits <= presses {
            if (presses - bits) % 2 == 0 {
                reachable = true;
            }
        }

        if reachable {
            let mut mask: i64 = 0;
            let mut pos: i64 = 1;
            let mut power: i64 = 1;

            while pos <= k {
                let mut on: bool = true;
                let mut b: i64 = 0;

                while b < 4 {
                    let mut p: i64 = 1;
                    let mut t: i64 = 0;
                    while t < b {
                        p = p * 2;
                        t += 1;
                    }

                    let selected: bool = (code / p) % 2 == 1;
                    if selected {
                        if b == 0 {
                            on = !on;
                        } else if b == 1 {
                            if pos % 2 == 0 {
                                on = !on;
                            }
                        } else if b == 2 {
                            if pos % 2 == 1 {
                                on = !on;
                            }
                        } else {
                            if pos % 3 == 1 {
                                on = !on;
                            }
                        }
                    }
                    b += 1;
                }

                if on {
                    mask += power;
                }
                power = power * 2;
                pos += 1;
            }

            let mut found: bool = false;
            let mut idx: usize = 0;
            while idx < seen.len() {
                if seen[idx] == mask {
                    found = true;
                }
                idx += 1;
            }

            if !found {
                seen.push(mask);
                unique_count += 1;
            }
        }

        code += 1;
    }

    unique_count
}
