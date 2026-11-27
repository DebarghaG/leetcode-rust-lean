pub fn closest_to_target(arr: &[i64], target: i64) -> i64 {
    let n = arr.len();
    let mut ans: i64 = 1000000000;
    let mut vals: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let a = arr[i];
        let mut new_vals: Vec<i64> = Vec::new();
        new_vals.push(a);

        let mut j: usize = 0;
        while j < vals.len() {
            let x = vals[j] & a;
            let mut found = false;
            let mut k: usize = 0;
            while k < new_vals.len() {
                if new_vals[k] == x {
                    found = true;
                    break;
                }
                k += 1;
            }
            if !found {
                new_vals.push(x);
            }
            j += 1;
        }

        let mut t: usize = 0;
        while t < new_vals.len() {
            let v = new_vals[t];
            let mut d: i64 = 0;
            if v >= target {
                d = v - target;
            } else {
                d = target - v;
            }
            if d < ans {
                ans = d;
            }
            t += 1;
        }

        vals = new_vals;
        i += 1;
    }

    ans
}
