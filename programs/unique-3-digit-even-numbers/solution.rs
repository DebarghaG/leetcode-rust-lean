pub fn total_numbers(digits: &[i64]) -> i64 {
    let n = digits.len();

    let mut seen: Vec<bool> = Vec::new();
    let mut t: usize = 0;
    while t < 1000 {
        seen.push(false);
        t += 1;
    }

    let mut count: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let a = digits[i];
        if a != 0 {
            let mut j: usize = 0;
            while j < n {
                if j != i {
                    let b = digits[j];

                    let mut k: usize = 0;
                    while k < n {
                        if k != i && k != j {
                            let c = digits[k];
                            if c % 2 == 0 {
                                let num = a * 100 + b * 10 + c;
                                let idx = num as usize;

                                if !seen[idx] {
                                    seen[idx] = true;
                                    count += 1;
                                }
                            }
                        }
                        k += 1;
                    }
                }
                j += 1;
            }
        }
        i += 1;
    }

    count
}
