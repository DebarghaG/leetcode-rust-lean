pub fn get_max_function_value(receiver: &[i64], k: i64) -> i64 {
    let n = receiver.len();

    let mut jump: Vec<i64> = Vec::new();
    let mut val: Vec<i64> = Vec::new();
    let mut ans: Vec<i64> = Vec::new();
    let mut cur: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        let r = receiver[i];
        jump.push(r);
        val.push(r);
        ans.push(i as i64);
        cur.push(i as i64);
        i += 1;
    }

    let mut rem = k;
    while rem > 0 {
        if rem % 2 == 1 {
            let mut j = 0;
            while j < n {
                let c = cur[j] as usize;
                ans[j] = ans[j] + val[c];
                cur[j] = jump[c];
                j += 1;
            }
        }

        rem = rem / 2;

        if rem > 0 {
            let mut next_jump: Vec<i64> = Vec::new();
            let mut next_val: Vec<i64> = Vec::new();

            let mut j = 0;
            while j < n {
                let a = jump[j] as usize;
                next_jump.push(jump[a]);
                next_val.push(val[j] + val[a]);
                j += 1;
            }

            jump = next_jump;
            val = next_val;
        }
    }

    let mut best = ans[0];
    let mut idx = 1;
    while idx < n {
        if ans[idx] > best {
            best = ans[idx];
        }
        idx += 1;
    }

    best
}
