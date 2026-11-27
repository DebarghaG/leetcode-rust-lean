pub fn longest_palindrome(words: &[Vec<u8>]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 676 {
        counts.push(0);
        k += 1;
    }

    let mut i: usize = 0;
    while i < words.len() {
        let w = &words[i];
        let a: usize = (w[0] as usize) - 97;
        let b: usize = (w[1] as usize) - 97;
        let idx: usize = a * 26 + b;
        counts[idx] = counts[idx] + 1;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut has_odd: bool = false;

    let mut a: usize = 0;
    while a < 26 {
        let mut b: usize = 0;
        while b < 26 {
            if a < b {
                let ab = counts[a * 26 + b];
                let ba = counts[b * 26 + a];
                let m = if ab < ba { ab } else { ba };
                ans = ans + 4 * m;
            } else if a == b {
                let c = counts[a * 26 + a];
                ans = ans + 4 * (c / 2);
                if c % 2 == 1 {
                    has_odd = true;
                }
            }
            b += 1;
        }
        a += 1;
    }

    if has_odd {
        ans = ans + 2;
    }

    ans
}
