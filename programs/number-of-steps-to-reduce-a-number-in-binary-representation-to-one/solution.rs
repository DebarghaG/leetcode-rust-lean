pub fn num_steps(s: &[u8]) -> i64 {
    let n = s.len();
    let mut bits: Vec<u8> = Vec::new();

    let mut idx = n;
    while idx > 0 {
        idx -= 1;
        if s[idx] == b'1' {
            bits.push(1);
        } else {
            bits.push(0);
        }
    }

    let mut start: usize = 0;
    let mut steps: i64 = 0;

    while !(bits.len() == start + 1 && bits[start] == 1) {
        if bits[start] == 0 {
            start += 1;
            steps += 1;
        } else {
            let mut i = start;
            while i < bits.len() && bits[i] == 1 {
                bits[i] = 0;
                i += 1;
            }
            if i < bits.len() {
                bits[i] = 1;
            } else {
                bits.push(1);
            }
            steps += 1;
        }
    }

    steps
}
