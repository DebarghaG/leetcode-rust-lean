fn digit_byte(d: i64) -> u8 {
    if d == 0 {
        b'0'
    } else if d == 1 {
        b'1'
    } else if d == 2 {
        b'2'
    } else if d == 3 {
        b'3'
    } else if d == 4 {
        b'4'
    } else if d == 5 {
        b'5'
    } else if d == 6 {
        b'6'
    } else if d == 7 {
        b'7'
    } else if d == 8 {
        b'8'
    } else {
        b'9'
    }
}

fn make_rank(place: i64) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();

    if place == 1 {
        out.push(b'G');
        out.push(b'o');
        out.push(b'l');
        out.push(b'd');
        out.push(b' ');
        out.push(b'M');
        out.push(b'e');
        out.push(b'd');
        out.push(b'a');
        out.push(b'l');
    } else if place == 2 {
        out.push(b'S');
        out.push(b'i');
        out.push(b'l');
        out.push(b'v');
        out.push(b'e');
        out.push(b'r');
        out.push(b' ');
        out.push(b'M');
        out.push(b'e');
        out.push(b'd');
        out.push(b'a');
        out.push(b'l');
    } else if place == 3 {
        out.push(b'B');
        out.push(b'r');
        out.push(b'o');
        out.push(b'n');
        out.push(b'z');
        out.push(b'e');
        out.push(b' ');
        out.push(b'M');
        out.push(b'e');
        out.push(b'd');
        out.push(b'a');
        out.push(b'l');
    } else {
        let mut digits: Vec<u8> = Vec::new();
        let mut x = place;

        while x > 0 {
            let d = x % 10;
            digits.push(digit_byte(d));
            x = x / 10;
        }

        let mut i = digits.len();
        while i > 0 {
            i -= 1;
            out.push(digits[i]);
        }
    }

    out
}

pub fn find_relative_ranks(score: &[i64]) -> Vec<Vec<u8>> {
    let n = score.len();
    let mut ans: Vec<Vec<u8>> = Vec::new();

    if n == 0 {
        return ans;
    }

    let mut order: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        order.push(i as i64);
        i += 1;
    }

    let mut buf: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        buf.push(0);
        i += 1;
    }

    // Bottom-up merge sort of indices, descending by score.
    let mut width = 1usize;
    while width < n {
        let mut left = 0usize;

        while left < n {
            let mid = if left + width < n {
                left + width
            } else {
                n
            };

            let right = if left + 2 * width < n {
                left + 2 * width
            } else {
                n
            };

            let mut a = left;
            let mut b = mid;
            let mut pos = left;

            while a < mid && b < right {
                let ia = order[a] as usize;
                let ib = order[b] as usize;

                if score[ia] >= score[ib] {
                    buf[pos] = order[a];
                    a += 1;
                } else {
                    buf[pos] = order[b];
                    b += 1;
                }

                pos += 1;
            }

            while a < mid {
                buf[pos] = order[a];
                a += 1;
                pos += 1;
            }

            while b < right {
                buf[pos] = order[b];
                b += 1;
                pos += 1;
            }

            left += 2 * width;
        }

        let mut t = 0usize;
        while t < n {
            order[t] = buf[t];
            t += 1;
        }

        width = 2 * width;
    }

    let mut rank: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        rank.push(0);
        i += 1;
    }

    let mut place: i64 = 1;
    let mut p = 0usize;
    while p < n {
        let idx = order[p] as usize;
        rank[idx] = place;
        place += 1;
        p += 1;
    }

    let mut j = 0usize;
    while j < n {
        ans.push(make_rank(rank[j]));
        j += 1;
    }

    ans
}
