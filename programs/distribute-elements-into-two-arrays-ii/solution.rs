fn lower_bound(arr: &[i64], val: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = arr.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if arr[mid] < val {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

pub fn result_array(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }

    if n >= 2 {
        let mut temp: Vec<i64> = Vec::new();
        let mut z: usize = 0;
        while z < n {
            temp.push(0);
            z += 1;
        }

        let mut width: usize = 1;
        while width < n {
            let mut lo: usize = 0;
            while lo < n {
                let mid = if lo + width < n { lo + width } else { n };
                let hi = if lo + width + width < n { lo + width + width } else { n };

                let mut a = lo;
                let mut b = mid;
                let mut k = lo;

                while a < mid && b < hi {
                    if sorted[a] <= sorted[b] {
                        temp[k] = sorted[a];
                        a += 1;
                    } else {
                        temp[k] = sorted[b];
                        b += 1;
                    }
                    k += 1;
                }

                while a < mid {
                    temp[k] = sorted[a];
                    a += 1;
                    k += 1;
                }

                while b < hi {
                    temp[k] = sorted[b];
                    b += 1;
                    k += 1;
                }

                lo += width + width;
            }

            let mut c: usize = 0;
            while c < n {
                sorted[c] = temp[c];
                c += 1;
            }

            width += width;
        }
    }

    let mut bit1: Vec<i64> = Vec::new();
    let mut bit2: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z <= n {
        bit1.push(0);
        bit2.push(0);
        z += 1;
    }

    let mut arr1: Vec<i64> = Vec::new();
    let mut arr2: Vec<i64> = Vec::new();

    if n == 0 {
        return arr1;
    }

    let v0 = nums[0];
    arr1.push(v0);
    let p0 = lower_bound(&sorted, v0) + 1;
    let mut u0 = p0;
    while u0 <= n {
        bit1[u0] += 1;
        u0 += u0 & (u0 ^ (u0 - 1));
    }

    if n >= 2 {
        let v1 = nums[1];
        arr2.push(v1);
        let p1 = lower_bound(&sorted, v1) + 1;
        let mut u1 = p1;
        while u1 <= n {
            bit2[u1] += 1;
            u1 += u1 & (u1 ^ (u1 - 1));
        }
    }

    let mut idx: usize = 2;
    while idx < n {
        let val = nums[idx];
        let pos = lower_bound(&sorted, val) + 1;

        let len1 = arr1.len() as i64;
        let len2 = arr2.len() as i64;

        let mut q1 = pos;
        let mut le1: i64 = 0;
        while q1 > 0 {
            le1 += bit1[q1];
            q1 = q1 & (q1 - 1);
        }

        let mut q2 = pos;
        let mut le2: i64 = 0;
        while q2 > 0 {
            le2 += bit2[q2];
            q2 = q2 & (q2 - 1);
        }

        let gc1 = len1 - le1;
        let gc2 = len2 - le2;

        let mut to_first = false;
        if gc1 > gc2 {
            to_first = true;
        } else if gc1 < gc2 {
            to_first = false;
        } else {
            if len1 <= len2 {
                to_first = true;
            } else {
                to_first = false;
            }
        }

        if to_first {
            arr1.push(val);
            let mut u = pos;
            while u <= n {
                bit1[u] += 1;
                u += u & (u ^ (u - 1));
            }
        } else {
            arr2.push(val);
            let mut u = pos;
            while u <= n {
                bit2[u] += 1;
                u += u & (u ^ (u - 1));
            }
        }

        idx += 1;
    }

    let mut result: Vec<i64> = Vec::new();

    let mut a: usize = 0;
    while a < arr1.len() {
        result.push(arr1[a]);
        a += 1;
    }

    let mut b: usize = 0;
    while b < arr2.len() {
        result.push(arr2[b]);
        b += 1;
    }

    result
}
