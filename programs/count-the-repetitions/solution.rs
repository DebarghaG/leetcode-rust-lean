pub fn get_max_repetitions(s1: &[u8], n1: i64, s2: &[u8], n2: i64) -> i64 {
    let len2: usize = s2.len();
    if len2 == 0 {
        return 0;
    }
    if n1 <= 0 {
        return 0;
    }
    if n2 <= 0 {
        return 0;
    }

    let mut seen: Vec<i64> = Vec::new();
    let mut seen_reps: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < len2 {
        seen.push(-1);
        seen_reps.push(0);
        k += 1;
    }

    let len1: usize = s1.len();
    let mut i: i64 = 0;
    let mut j: usize = 0;
    let mut reps: i64 = 0;

    while i < n1 {
        if seen[j] >= 0 {
            let prev_i: i64 = seen[j];
            let prev_reps: i64 = seen_reps[j];
            let cycle_len: i64 = i - prev_i;

            if cycle_len > 0 {
                let cycle_reps: i64 = reps - prev_reps;
                let remaining: i64 = n1 - i;
                let cycles: i64 = remaining / cycle_len;

                if cycles > 0 {
                    reps = reps + cycles * cycle_reps;
                    i = i + cycles * cycle_len;

                    let mut c: usize = 0;
                    while c < len2 {
                        seen[c] = -1;
                        c += 1;
                    }
                }
            }
        }

        if i < n1 {
            if seen[j] < 0 {
                seen[j] = i;
                seen_reps[j] = reps;
            }

            let mut p: usize = 0;
            while p < len1 {
                if s1[p] == s2[j] {
                    j += 1;
                    if j == len2 {
                        reps += 1;
                        j = 0;
                    }
                }
                p += 1;
            }

            i += 1;
        }
    }

    reps / n2
}
