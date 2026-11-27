pub fn subarray_bitwise_o_rs(arr: &[i64]) -> i64 {
    let mut cap: usize = 8;
    let mut table: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < cap {
        table.push(-1);
        z += 1;
    }

    let mut used: usize = 0;
    let mut count: i64 = 0;

    let mut prev: Vec<i64> = Vec::new();
    let mut idx: usize = 0;

    while idx < arr.len() {
        let a = arr[idx];

        let mut next: Vec<i64> = Vec::new();
        next.push(a);

        let mut p: usize = 0;
        while p < prev.len() {
            let v = prev[p] | a;

            let mut dup = false;
            let mut q: usize = 0;
            while q < next.len() && !dup {
                if next[q] == v {
                    dup = true;
                }
                q += 1;
            }

            if !dup {
                next.push(v);
            }

            p += 1;
        }

        let mut t: usize = 0;
        while t < next.len() {
            let val = next[t];

            if (used + 1) * 10 > cap * 7 {
                let new_cap = cap * 2;

                let mut new_table: Vec<i64> = Vec::new();
                let mut i: usize = 0;
                while i < new_cap {
                    new_table.push(-1);
                    i += 1;
                }

                let mut j: usize = 0;
                while j < table.len() {
                    let old = table[j];
                    if old != -1 {
                        let mut h = (old as usize) & (new_cap - 1);
                        while new_table[h] != -1 {
                            h = (h + 1) & (new_cap - 1);
                        }
                        new_table[h] = old;
                    }
                    j += 1;
                }

                table = new_table;
                cap = new_cap;
            }

            let mask = cap - 1;
            let mut h = (val as usize) & mask;

            while table[h] != -1 && table[h] != val {
                h = (h + 1) & mask;
            }

            if table[h] == -1 {
                table[h] = val;
                used += 1;
                count += 1;
            }

            t += 1;
        }

        prev = next;
        idx += 1;
    }

    count
}
