fn hash_index(x: i64, mask: usize) -> usize {
    (x as usize) & mask
}

pub fn array_change(nums: &[i64], operations: &[Vec<i64>]) -> Vec<i64> {
    let mut cap: usize = 1;
    let target: usize = operations.len() * 2 + 2;
    while cap < target {
        cap = cap * 2;
    }
    let mask: usize = cap - 1;

    let mut keys: Vec<i64> = Vec::new();
    let mut vals: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < cap {
        keys.push(0);
        vals.push(0);
        i += 1;
    }

    let mut op_i: usize = operations.len();
    while op_i > 0 {
        op_i -= 1;

        let a = operations[op_i][0];
        let b = operations[op_i][1];

        let mut hb: usize = hash_index(b, mask);
        while keys[hb] != 0 && keys[hb] != b {
            hb = (hb + 1) & mask;
        }

        let resolved: i64 = if keys[hb] == b { vals[hb] } else { b };

        let mut ha: usize = hash_index(a, mask);
        while keys[ha] != 0 && keys[ha] != a {
            ha = (ha + 1) & mask;
        }

        if keys[ha] == 0 {
            keys[ha] = a;
        }
        vals[ha] = resolved;
    }

    let mut out: Vec<i64> = Vec::new();
    let mut j: usize = 0;

    while j < nums.len() {
        let x = nums[j];

        let mut h: usize = hash_index(x, mask);
        while keys[h] != 0 && keys[h] != x {
            h = (h + 1) & mask;
        }

        let y: i64 = if keys[h] == x { vals[h] } else { x };
        out.push(y);

        j += 1;
    }

    out
}
