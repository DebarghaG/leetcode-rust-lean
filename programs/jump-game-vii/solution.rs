pub fn can_reach(s: &[u8], minJump: i64, maxJump: i64) -> bool {
    let n = s.len();
    if n == 0 {
        return false;
    }
    if n == 1 {
        return true;
    }

    let min_j = minJump as usize;
    let max_j = maxJump as usize;

    let mut reach: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        reach.push(false);
        k += 1;
    }
    reach[0] = true;

    let mut count: i64 = 0;
    let mut i: usize = 1;

    while i < n {
        if i >= min_j {
            let add = i - min_j;
            if reach[add] {
                count += 1;
            }
        }

        if i > max_j {
            let rem = i - max_j - 1;
            if reach[rem] {
                count -= 1;
            }
        }

        if s[i] == b'0' && count > 0 {
            reach[i] = true;
        }

        i += 1;
    }

    reach[n - 1]
}
