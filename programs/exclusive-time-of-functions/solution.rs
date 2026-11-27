pub fn exclusive_time(n: i64, logs: &[Vec<u8>]) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i < n {
        ans.push(0);
        i += 1;
    }

    let mut stack: Vec<usize> = Vec::new();
    let mut prev: i64 = 0;
    let mut k: usize = 0;

    while k < logs.len() {
        let s = &logs[k];

        let mut p: usize = 0;
        let mut id: usize = 0;
        while p < s.len() && s[p] != b':' {
            id = id * 10 + ((s[p] - b'0') as usize);
            p += 1;
        }

        let is_start: bool = s[p + 1] == b's';

        p += 1;
        while p < s.len() && s[p] != b':' {
            p += 1;
        }
        p += 1;

        let mut ts: i64 = 0;
        while p < s.len() {
            ts = ts * 10 + ((s[p] - b'0') as i64);
            p += 1;
        }

        if is_start {
            if stack.len() > 0 {
                let parent = stack[stack.len() - 1];
                ans[parent] += ts - prev;
            }
            stack.push(id);
            prev = ts;
        } else {
            let top = stack[stack.len() - 1];
            let _ = stack.pop();
            ans[top] += ts - prev + 1;
            prev = ts + 1;
        }

        k += 1;
    }

    ans
}
