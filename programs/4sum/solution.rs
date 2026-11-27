pub fn four_sum(nums: &[i64], target: i64) -> Vec<Vec<i64>> {
    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n {
        a.push(nums[idx]);
        idx += 1;
    }

    // Selection sort the copied array.
    let mut i: usize = 0;
    while i < n {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < n {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        if min_idx != i {
            let tmp = a[i];
            a[i] = a[min_idx];
            a[min_idx] = tmp;
        }
        i += 1;
    }

    let mut res: Vec<Vec<i64>> = Vec::new();
    if n < 4 {
        return res;
    }

    let mut p: usize = 0;
    while p + 3 < n {
        let mut skip_p: bool = false;
        if p > 0 {
            if a[p] == a[p - 1] {
                skip_p = true;
            }
        }

        if !skip_p {
            let mut q: usize = p + 1;
            while q + 2 < n {
                let mut skip_q: bool = false;
                if q > p + 1 {
                    if a[q] == a[q - 1] {
                        skip_q = true;
                    }
                }

                if !skip_q {
                    let mut l: usize = q + 1;
                    let mut r: usize = n - 1;

                    while l < r {
                        let sum = a[p] + a[q] + a[l] + a[r];

                        if sum == target {
                            let mut quad: Vec<i64> = Vec::new();
                            quad.push(a[p]);
                            quad.push(a[q]);
                            quad.push(a[l]);
                            quad.push(a[r]);
                            res.push(quad);

                            l += 1;
                            r -= 1;

                            let mut cont_l = l < r;
                            while cont_l {
                                if a[l] == a[l - 1] {
                                    l += 1;
                                    cont_l = l < r;
                                } else {
                                    cont_l = false;
                                }
                            }

                            let mut cont_r = l < r;
                            while cont_r {
                                if a[r] == a[r + 1] {
                                    r -= 1;
                                    cont_r = l < r;
                                } else {
                                    cont_r = false;
                                }
                            }
                        } else if sum < target {
                            l += 1;
                        } else {
                            r -= 1;
                        }
                    }
                }

                q += 1;
            }
        }

        p += 1;
    }

    res
}
