fn bytes_eq(a: &Vec<u8>, b: &Vec<u8>) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn bytes_less(a: &Vec<u8>, b: &Vec<u8>) -> bool {
    let mut i = 0;
    while i < a.len() && i < b.len() {
        if a[i] < b[i] {
            return true;
        }
        if a[i] > b[i] {
            return false;
        }
        i += 1;
    }
    a.len() < b.len()
}

pub fn before_and_after_puzzles(phrases: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let n = phrases.len();
    let mut out: Vec<Vec<u8>> = Vec::new();

    let mut i = 0;
    while i < n {
        let p1 = &phrases[i];
        let len1 = p1.len();

        // Find the start of the last word of p1.
        let mut last_start = 0;
        let mut k = 0;
        while k < len1 {
            if p1[k] == b' ' {
                last_start = k + 1;
            }
            k += 1;
        }

        let mut j = 0;
        while j < n {
            if i != j {
                let p2 = &phrases[j];
                let len2 = p2.len();

                // Find the end of the first word of p2.
                let mut first_end = len2;
                let mut k2 = 0;
                while k2 < len2 {
                    if p2[k2] == b' ' {
                        first_end = k2;
                        break;
                    }
                    k2 += 1;
                }

                // Compare the last word of p1 with the first word of p2.
                let l1 = len1 - last_start;
                let l2 = first_end;
                let mut eq = true;
                if l1 != l2 {
                    eq = false;
                } else {
                    let mut t = 0;
                    while t < l1 {
                        if p1[last_start + t] != p2[t] {
                            eq = false;
                            break;
                        }
                        t += 1;
                    }
                }

                if eq {
                    let mut cand: Vec<u8> = Vec::new();

                    // Append the entire first phrase.
                    let mut a = 0;
                    while a < len1 {
                        cand.push(p1[a]);
                        a += 1;
                    }

                    // Append the remainder of the second phrase after its first word.
                    if first_end < len2 {
                        cand.push(b' ');
                        let mut b = first_end + 1;
                        while b < len2 {
                            cand.push(p2[b]);
                            b += 1;
                        }
                    }

                    // Insert only if this candidate is not already present.
                    let mut exists = false;
                    let mut q = 0;
                    while q < out.len() {
                        if bytes_eq(&out[q], &cand) {
                            exists = true;
                            break;
                        }
                        q += 1;
                    }
                    if !exists {
                        out.push(cand);
                    }
                }
            }
            j += 1;
        }
        i += 1;
    }

    // Lexicographic selection sort.
    let m = out.len();
    let mut a = 0;
    while a < m {
        let mut min = a;
        let mut b = a + 1;
        while b < m {
            if bytes_less(&out[b], &out[min]) {
                min = b;
            }
            b += 1;
        }
        if min != a {
            out.swap(a, min);
        }
        a += 1;
    }

    out
}
