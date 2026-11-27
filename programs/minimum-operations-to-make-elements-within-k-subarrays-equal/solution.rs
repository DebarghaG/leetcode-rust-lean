fn heap_push_max(heap: &mut Vec<i64>, len: usize, idx: i64, nums: &[i64]) -> usize {
    let mut i = len;
    heap[i] = idx;
    while i > 0 {
        let p = (i - 1) / 2;
        let a = heap[i];
        let b = heap[p];
        let va = nums[a as usize];
        let vb = nums[b as usize];
        let mut do_swap = false;
        if va > vb {
            do_swap = true;
        } else {
            if va == vb {
                if a > b {
                    do_swap = true;
                }
            }
        }
        if do_swap {
            let tmp = heap[i];
            heap[i] = heap[p];
            heap[p] = tmp;
            i = p;
        } else {
            break;
        }
    }
    len + 1
}

fn heap_push_min(heap: &mut Vec<i64>, len: usize, idx: i64, nums: &[i64]) -> usize {
    let mut i = len;
    heap[i] = idx;
    while i > 0 {
        let p = (i - 1) / 2;
        let a = heap[i];
        let b = heap[p];
        let va = nums[a as usize];
        let vb = nums[b as usize];
        let mut do_swap = false;
        if va < vb {
            do_swap = true;
        } else {
            if va == vb {
                if a < b {
                    do_swap = true;
                }
            }
        }
        if do_swap {
            let tmp = heap[i];
            heap[i] = heap[p];
            heap[p] = tmp;
            i = p;
        } else {
            break;
        }
    }
    len + 1
}

fn heap_pop_max(heap: &mut Vec<i64>, len: usize, nums: &[i64]) -> usize {
    let new_len = len - 1;
    if new_len == 0 {
        return 0;
    }
    heap[0] = heap[new_len];
    let mut i = 0usize;
    let mut go = true;
    while go {
        let left = 2 * i + 1;
        if left >= new_len {
            go = false;
        } else {
            let right = left + 1;
            let mut largest = left;
            if right < new_len {
                let a = heap[right];
                let b = heap[left];
                let va = nums[a as usize];
                let vb = nums[b as usize];
                let mut right_bigger = false;
                if va > vb {
                    right_bigger = true;
                } else {
                    if va == vb {
                        if a > b {
                            right_bigger = true;
                        }
                    }
                }
                if right_bigger {
                    largest = right;
                }
            }
            let a = heap[largest];
            let b = heap[i];
            let va = nums[a as usize];
            let vb = nums[b as usize];
            let mut do_swap = false;
            if va > vb {
                do_swap = true;
            } else {
                if va == vb {
                    if a > b {
                        do_swap = true;
                    }
                }
            }
            if do_swap {
                let tmp = heap[i];
                heap[i] = heap[largest];
                heap[largest] = tmp;
                i = largest;
            } else {
                go = false;
            }
        }
    }
    new_len
}

fn heap_pop_min(heap: &mut Vec<i64>, len: usize, nums: &[i64]) -> usize {
    let new_len = len - 1;
    if new_len == 0 {
        return 0;
    }
    heap[0] = heap[new_len];
    let mut i = 0usize;
    let mut go = true;
    while go {
        let left = 2 * i + 1;
        if left >= new_len {
            go = false;
        } else {
            let right = left + 1;
            let mut smallest = left;
            if right < new_len {
                let a = heap[right];
                let b = heap[left];
                let va = nums[a as usize];
                let vb = nums[b as usize];
                let mut right_smaller = false;
                if va < vb {
                    right_smaller = true;
                } else {
                    if va == vb {
                        if a < b {
                            right_smaller = true;
                        }
                    }
                }
                if right_smaller {
                    smallest = right;
                }
            }
            let a = heap[smallest];
            let b = heap[i];
            let va = nums[a as usize];
            let vb = nums[b as usize];
            let mut do_swap = false;
            if va < vb {
                do_swap = true;
            } else {
                if va == vb {
                    if a < b {
                        do_swap = true;
                    }
                }
            }
            if do_swap {
                let tmp = heap[i];
                heap[i] = heap[smallest];
                heap[smallest] = tmp;
                i = smallest;
            } else {
                go = false;
            }
        }
    }
    new_len
}

pub fn min_operations(nums: &[i64], x: i64, k: i64) -> i64 {
    let n = nums.len();
    let x_us = x as usize;
    let k_us = k as usize;
    let desired = (x_us + 1) / 2;
    let desired_i64 = desired as i64;

    let mut heap_low: Vec<i64> = Vec::new();
    let mut heap_high: Vec<i64> = Vec::new();
    let mut pos: Vec<i64> = Vec::new();
    let mut z = 0usize;
    while z < n {
        heap_low.push(0);
        heap_high.push(0);
        pos.push(0);
        z += 1;
    }

    let mut low_len = 0usize;
    let mut high_len = 0usize;
    let mut sum_low: i64 = 0;
    let mut sum_high: i64 = 0;
    let mut cnt_low: i64 = 0;
    let mut cnt_high: i64 = 0;

    let mut i = 0usize;
    while i < x_us {
        let v = nums[i];
        low_len = heap_push_max(&mut heap_low, low_len, i as i64, nums);
        sum_low += v;
        cnt_low += 1;
        pos[i] = 1;
        i += 1;
    }

    while cnt_low > desired_i64 {
        let top = heap_low[0];
        let v = nums[top as usize];
        low_len = heap_pop_max(&mut heap_low, low_len, nums);
        sum_low -= v;
        cnt_low -= 1;
        pos[top as usize] = 2;
        high_len = heap_push_min(&mut heap_high, high_len, top, nums);
        sum_high += v;
        cnt_high += 1;
    }

    let max_start = n - x_us;
    let mut costs: Vec<i64> = Vec::new();
    let mut s = 0usize;
    while s <= max_start {
        while low_len > 0 {
            let top_idx = heap_low[0] as usize;
            if pos[top_idx] == 1 {
                break;
            }
            low_len = heap_pop_max(&mut heap_low, low_len, nums);
        }

        let med_idx = heap_low[0] as usize;
        let med = nums[med_idx];
        let cost = med * cnt_low - sum_low + sum_high - med * cnt_high;
        costs.push(cost);

        if s == max_start {
            break;
        }

        let out_idx = s;
        let p_out = pos[out_idx];
        let v_out = nums[out_idx];
        if p_out == 1 {
            sum_low -= v_out;
            cnt_low -= 1;
        } else {
            if p_out == 2 {
                sum_high -= v_out;
                cnt_high -= 1;
            }
        }
        pos[out_idx] = 0;

        let in_idx = s + x_us;
        let v_in = nums[in_idx];

        while low_len > 0 {
            let top_idx = heap_low[0] as usize;
            if pos[top_idx] == 1 {
                break;
            }
            low_len = heap_pop_max(&mut heap_low, low_len, nums);
        }

        if low_len == 0 {
            if high_len > 0 {
                high_len = heap_push_min(&mut heap_high, high_len, in_idx as i64, nums);
                sum_high += v_in;
                cnt_high += 1;
                pos[in_idx] = 2;
            } else {
                low_len = heap_push_max(&mut heap_low, low_len, in_idx as i64, nums);
                sum_low += v_in;
                cnt_low += 1;
                pos[in_idx] = 1;
            }
        } else {
            let med = nums[heap_low[0] as usize];
            if v_in <= med {
                low_len = heap_push_max(&mut heap_low, low_len, in_idx as i64, nums);
                sum_low += v_in;
                cnt_low += 1;
                pos[in_idx] = 1;
            } else {
                high_len = heap_push_min(&mut heap_high, high_len, in_idx as i64, nums);
                sum_high += v_in;
                cnt_high += 1;
                pos[in_idx] = 2;
            }
        }

        while cnt_low > desired_i64 {
            while low_len > 0 {
                let top_idx = heap_low[0] as usize;
                if pos[top_idx] == 1 {
                    break;
                }
                low_len = heap_pop_max(&mut heap_low, low_len, nums);
            }
            let top = heap_low[0];
            let v = nums[top as usize];
            low_len = heap_pop_max(&mut heap_low, low_len, nums);
            sum_low -= v;
            cnt_low -= 1;
            pos[top as usize] = 2;
            high_len = heap_push_min(&mut heap_high, high_len, top, nums);
            sum_high += v;
            cnt_high += 1;
        }

        while cnt_low < desired_i64 {
            while high_len > 0 {
                let top_idx = heap_high[0] as usize;
                if pos[top_idx] == 2 {
                    break;
                }
                high_len = heap_pop_min(&mut heap_high, high_len, nums);
            }
            let top = heap_high[0];
            let v = nums[top as usize];
            high_len = heap_pop_min(&mut heap_high, high_len, nums);
            sum_high -= v;
            cnt_high -= 1;
            pos[top as usize] = 1;
            low_len = heap_push_max(&mut heap_low, low_len, top, nums);
            sum_low += v;
            cnt_low += 1;
        }

        s += 1;
    }

    let w = costs.len();
    let inf: i64 = 1_000_000_000_000_000_000;

    let mut prev: Vec<i64> = Vec::new();
    let mut best = inf;
    let mut j = 0usize;
    while j < w {
        let c = costs[j];
        if c < best {
            best = c;
        }
        prev.push(best);
        j += 1;
    }

    let mut i_dp = 2usize;
    while i_dp <= k_us {
        let mut cur: Vec<i64> = Vec::new();
        cur.push(inf);
        let mut jj = 1usize;
        while jj < w {
            let mut val = cur[jj - 1];
            if jj >= x_us {
                let p = prev[jj - x_us];
                if p < inf {
                    let cand = p + costs[jj];
                    if cand < val {
                        val = cand;
                    }
                }
            }
            cur.push(val);
            jj += 1;
        }
        prev = cur;
        i_dp += 1;
    }

    prev[w - 1]
}
