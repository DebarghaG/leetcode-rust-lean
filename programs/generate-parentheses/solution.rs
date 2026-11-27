pub fn generate_parenthesis(n: i64) -> Vec<Vec<u8>> {
    let target: usize = (2 * n) as usize;

    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut cur: Vec<u8> = Vec::new();

    let mut opens: Vec<i64> = Vec::new();
    let mut closes: Vec<i64> = Vec::new();
    let mut states: Vec<i64> = Vec::new();

    opens.push(0);
    closes.push(0);
    states.push(0);

    while opens.len() > 0 {
        let idx: usize = opens.len() - 1;
        let oc: i64 = opens[idx];
        let cc: i64 = closes[idx];
        let st: i64 = states[idx];

        if cur.len() == target {
            let mut s: Vec<u8> = Vec::new();
            let mut j: usize = 0;
            while j < cur.len() {
                s.push(cur[j]);
                j = j + 1;
            }
            result.push(s);

            opens.pop();
            closes.pop();
            states.pop();
            if cur.len() > 0 {
                cur.pop();
            }
        } else if st == 0 {
            states[idx] = 1;
            if oc < n {
                opens.push(oc + 1);
                closes.push(cc);
                states.push(0);
                cur.push(b'(');
            }
        } else if st == 1 {
            states[idx] = 2;
            if cc < oc {
                opens.push(oc);
                closes.push(cc + 1);
                states.push(0);
                cur.push(b')');
            }
        } else {
            opens.pop();
            closes.pop();
            states.pop();
            if cur.len() > 0 {
                cur.pop();
            }
        }
    }

    result
}
