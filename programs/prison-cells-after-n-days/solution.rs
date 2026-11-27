fn advance(state: &[i64]) -> Vec<i64> {
    let len = state.len();
    let mut next: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < len {
        if i == 0 {
            next.push(0);
        } else if i + 1 == len {
            next.push(0);
        } else if state[i - 1] == state[i + 1] {
            next.push(1);
        } else {
            next.push(0);
        }
        i += 1;
    }

    next
}

fn encode(state: &[i64]) -> i64 {
    let mut code: i64 = 0;
    let mut i: usize = 0;

    while i < state.len() {
        code = code * 2 + state[i];
        i += 1;
    }

    code
}

pub fn prison_after_n_days(cells: &[i64], n: i64) -> Vec<i64> {
    let mut cur: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < cells.len() {
        cur.push(cells[i]);
        i += 1;
    }

    let mut seen: Vec<i64> = Vec::new();
    let mut day: i64 = 0;

    while day < n {
        let code = encode(&cur);

        let mut found_idx: i64 = -1;
        let mut j: usize = 0;
        let mut idx: i64 = 0;

        while j < seen.len() {
            if seen[j] == code {
                found_idx = idx;
                j = seen.len();
            } else {
                j += 1;
                idx += 1;
            }
        }

        if found_idx >= 0 {
            let cycle: i64 = day - found_idx;
            let rem: i64 = (n - day) % cycle;

            let mut k: i64 = 0;
            while k < rem {
                let next_state = advance(&cur);
                cur = next_state;
                k += 1;
            }

            return cur;
        }

        seen.push(code);
        let next_state = advance(&cur);
        cur = next_state;
        day += 1;
    }

    cur
}
