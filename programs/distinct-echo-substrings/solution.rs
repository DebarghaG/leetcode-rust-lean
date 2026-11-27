fn suffix_less(i: usize, j: usize, text: &[u8], lcp: &[Vec<usize>]) -> bool {
    if i == j {
        return false;
    }

    let n = text.len();
    let common = lcp[i][j];
    let ii = i + common;
    let jj = j + common;

    if ii == n {
        return true;
    }
    if jj == n {
        return false;
    }

    text[ii] < text[jj]
}

pub fn distinct_echo_substrings(text: &[u8]) -> i64 {
    let n = text.len();

    // lcp[i][j] = length of the longest common prefix of text[i..] and text[j..].
    let mut lcp: Vec<Vec<usize>> = Vec::new();
    let mut i = 0;
    while i <= n {
        let mut row: Vec<usize> = Vec::new();
        let mut j = 0;
        while j <= n {
            row.push(0);
            j += 1;
        }
        lcp.push(row);
        i += 1;
    }

    let mut a = n;
    while a > 0 {
        a -= 1;
        let mut b = n;
        while b > 0 {
            b -= 1;
            let mut val: usize = 0;
            if text[a] == text[b] {
                val = lcp[a + 1][b + 1] + 1;
            }
            lcp[a][b] = val;
        }
    }

    // Build the suffix array using iterative bottom-up merge sort.
    let mut sa: Vec<usize> = Vec::new();
    let mut k = 0;
    while k < n {
        sa.push(k);
        k += 1;
    }

    let mut width = 1;
    while width < n {
        let mut merged: Vec<usize> = Vec::new();
        let mut left = 0;

        while left < n {
            let mid_raw = left + width;
            let mid = if mid_raw < n { mid_raw } else { n };

            let right_raw = left + width * 2;
            let right = if right_raw < n { right_raw } else { n };

            let mut x = left;
            let mut y = mid;

            while x < mid && y < right {
                if suffix_less(sa[x], sa[y], text, &lcp) {
                    merged.push(sa[x]);
                    x += 1;
                } else {
                    merged.push(sa[y]);
                    y += 1;
                }
            }

            while x < mid {
                merged.push(sa[x]);
                x += 1;
            }

            while y < right {
                merged.push(sa[y]);
                y += 1;
            }

            left = right;
        }

        sa = merged;
        width = width * 2;
    }

    let mut ans: i64 = 0;
    let mut half: usize = 1;

    while half * 2 <= n {
        let len = half * 2;

        let mut have_prev = false;
        let mut prev: usize = 0;
        let mut idx = 0;

        while idx < n {
            let pos = sa[idx];

            if pos + len <= n {
                // Check text[pos..pos+half] == text[pos+half..pos+2*half].
                if lcp[pos][pos + half] >= half {
                    if !have_prev {
                        ans += 1;
                        have_prev = true;
                        prev = pos;
                    } else {
                        if lcp[prev][pos] < len {
                            ans += 1;
                        }
                        prev = pos;
                    }
                }
            }

            idx += 1;
        }

        half += 1;
    }

    ans
}
