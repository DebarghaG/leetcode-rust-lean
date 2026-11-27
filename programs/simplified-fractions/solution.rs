pub fn simplified_fractions(n: i64) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut num: i64 = 1;

    while num < n {
        // --- Precompute the (at most two) digit bytes of the numerator once. ---
        let num_two: bool = num >= 10;
        let nt: i64 = num / 10;
        let nu: i64 = num - nt * 10;

        // --- Distinct prime factors of num (at most three, since num <= 99). ---
        let mut m: i64 = num;
        let mut f: i64 = 2;
        let mut p0: i64 = 0;
        let mut p1: i64 = 0;
        let mut p2: i64 = 0;

        while f * f <= m {
            if m % f == 0 {
                if p0 == 0 {
                    p0 = f;
                } else if p1 == 0 {
                    p1 = f;
                } else {
                    p2 = f;
                }
                while m % f == 0 {
                    m = m / f;
                }
            }
            f += 1;
        }
        if m > 1 {
            if p0 == 0 {
                p0 = m;
            } else if p1 == 0 {
                p1 = m;
            } else {
                p2 = m;
            }
        }

        // --- Den_ominator digits maintained incrementally (no divisions in the loop). ---
        let mut den: i64 = num + 1;
        let mut dt: i64 = den / 10;
        let mut du: i64 = den - dt * 10;

        while den <= n {
            // Coprime test: den shares no prime factor with num.
            let mut cop: bool = true;
            if p0 != 0 {
                if den % p0 == 0 {
                    cop = false;
                }
            }
            if cop && p1 != 0 {
                if den % p1 == 0 {
                    cop = false;
                }
            }
            if cop && p2 != 0 {
                if den % p2 == 0 {
                    cop = false;
                }
            }

            if cop {
                let mut s: Vec<u8> = Vec::new();

                if num_two {
                    s.push(48u8 + nt as u8);
                    s.push(48u8 + nu as u8);
                } else {
                    s.push(48u8 + num as u8);
                }

                s.push(b'/');

                if den == 100 {
                    s.push(b'1');
                    s.push(b'0');
                    s.push(b'0');
                } else if den >= 10 {
                    s.push(48u8 + dt as u8);
                    s.push(48u8 + du as u8);
                } else {
                    s.push(48u8 + du as u8);
                }

                out.push(s);
            }

            den += 1;
            du += 1;
            if du == 10 {
                du = 0;
                dt += 1;
            }
        }

        num += 1;
    }

    out
}
