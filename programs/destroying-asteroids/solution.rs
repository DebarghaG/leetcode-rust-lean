pub fn asteroids_destroyed(mass: i64, asteroids: &[i64]) -> bool {
    let n: usize = asteroids.len();
    if n == 0 {
        return true;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut b: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut minv: i64 = asteroids[0];
    let mut maxv: i64 = asteroids[0];

    while i < n {
        let x: i64 = asteroids[i];
        a.push(x);
        b.push(0);
        if x < minv {
            minv = x;
        }
        if x > maxv {
            maxv = x;
        }
        i += 1;
    }

    if mass < minv {
        return false;
    }
    if mass >= maxv {
        return true;
    }

    let mut from_a: bool = true;
    let mut width: usize = 1;

    while width < n {
        let dbl: usize = width + width;
        let mut start: usize = 0;

        while start < n {
            let mid: usize = if start + width < n { start + width } else { n };
            let end: usize = if start + dbl < n { start + dbl } else { n };
            let mut l: usize = start;
            let mut r: usize = mid;
            let mut k: usize = start;

            if from_a {
                while l < mid && r < end {
                    if a[l] <= a[r] {
                        b[k] = a[l];
                        l += 1;
                    } else {
                        b[k] = a[r];
                        r += 1;
                    }
                    k += 1;
                }
                while l < mid {
                    b[k] = a[l];
                    l += 1;
                    k += 1;
                }
                while r < end {
                    b[k] = a[r];
                    r += 1;
                    k += 1;
                }
            } else {
                while l < mid && r < end {
                    if b[l] <= b[r] {
                        a[k] = b[l];
                        l += 1;
                    } else {
                        a[k] = b[r];
                        r += 1;
                    }
                    k += 1;
                }
                while l < mid {
                    a[k] = b[l];
                    l += 1;
                    k += 1;
                }
                while r < end {
                    a[k] = b[r];
                    r += 1;
                    k += 1;
                }
            }

            start = start + dbl;
        }

        from_a = !from_a;
        width = width + width;
    }

    let mut m: i64 = mass;
    i = 0;

    if from_a {
        while i < n {
            if m < a[i] {
                return false;
            }
            m = m + a[i];
            i += 1;
        }
    } else {
        while i < n {
            if m < b[i] {
                return false;
            }
            m = m + b[i];
            i += 1;
        }
    }

    true
}
