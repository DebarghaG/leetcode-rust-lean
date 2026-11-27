pub fn sort_even_odd(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut evens: Vec<i64> = Vec::new();
    let mut odds: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        if i % 2 == 0 {
            evens.push(nums[i]);
        } else {
            odds.push(nums[i]);
        }
        i += 1;
    }

    let en = evens.len();
    let mut a: usize = 1;
    while a < en {
        let key = evens[a];
        let mut b: usize = a;
        while b > 0 && evens[b - 1] > key {
            evens[b] = evens[b - 1];
            b -= 1;
        }
        evens[b] = key;
        a += 1;
    }

    let on = odds.len();
    let mut c: usize = 1;
    while c < on {
        let key = odds[c];
        let mut d: usize = c;
        while d > 0 && odds[d - 1] < key {
            odds[d] = odds[d - 1];
            d -= 1;
        }
        odds[d] = key;
        c += 1;
    }

    let mut out: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    let mut q: usize = 0;
    let mut idx: usize = 0;

    while idx < n {
        if idx % 2 == 0 {
            out.push(evens[p]);
            p += 1;
        } else {
            out.push(odds[q]);
            q += 1;
        }
        idx += 1;
    }

    out
}
