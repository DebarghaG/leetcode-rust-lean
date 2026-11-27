pub fn max_partitions_after_operations(s: &[u8], k: i64) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    // Prefix greedy states: before position i.
    let mut pre_parts: Vec<i64> = Vec::new();
    let mut pre_mask: Vec<i64> = Vec::new();
    let mut pre_cnt: Vec<i64> = Vec::new();

    pre_parts.push(0);
    pre_mask.push(0);
    pre_cnt.push(0);

    let mut i: usize = 0;
    while i < n {
        let c = (s[i] as i64) - 97;
        let bit = 1_i64 << (c as usize);

        let mut p = pre_parts[i];
        let mut m = pre_mask[i];
        let mut cnt = pre_cnt[i];

        if (m & bit) == 0 {
            if cnt < k {
                m = m | bit;
                cnt = cnt + 1;
            } else {
                p = p + 1;
                m = bit;
                cnt = 1;
            }
        }

        pre_parts.push(p);
        pre_mask.push(m);
        pre_cnt.push(cnt);
        i += 1;
    }

    // Answer with no change.
    let mut ans = pre_parts[n] + 1;

    // sufp[t] = greedy partition count of suffix s[t..], starting fresh.
    let mut sufp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        sufp.push(0);
        z += 1;
    }

    // Current suffix first-occurrence order, for suffix s[i+1..].
    let mut ord_chars: Vec<i64> = Vec::new();
    let mut ord_pos: Vec<usize> = Vec::new();
    let mut ord_len: usize = 0;

    // Small fixed-size work arrays, indexed by letter 0..25.
    let mut rank_o: Vec<i64> = Vec::new();
    let mut rank_l: Vec<i64> = Vec::new();
    let mut l_pos: Vec<usize> = Vec::new();

    let mut init: usize = 0;
    while init < 26 {
        rank_o.push(-1);
        rank_l.push(-1);
        l_pos.push(0);
        init += 1;
    }

    let mut ii: usize = n;
    while ii > 0 {
        ii -= 1;

        let base_parts = pre_parts[ii];
        let base_mask = pre_mask[ii];
        let base_cnt = pre_cnt[ii];

        // Reset ranks.
        let mut r: usize = 0;
        while r < 26 {
            rank_o[r] = -1;
            rank_l[r] = -1;
            r += 1;
        }

        // Build:
        // rank_o[ch] = 1-based position of ch in current suffix first-occurrence order.
        // L = chars in current suffix that are not in base_mask, with l_pos positions.
        let mut l_len: usize = 0;
        let mut j: usize = 0;
        while j < ord_len {
            let ch = ord_chars[j];
            let chi = ch as usize;

            rank_o[chi] = (j as i64) + 1;

            let bit = 1_i64 << chi;
            if (base_mask & bit) == 0 {
                l_pos[l_len] = ord_pos[j];
                rank_l[chi] = (l_len as i64) + 1;
                l_len += 1;
            }

            j += 1;
        }

        // Case 1: changed character is already in the current segment.
        if base_cnt > 0 {
            let qa_i = k + 1 - base_cnt;
            let qa = qa_i as usize;

            if qa <= l_len {
                let u = l_pos[qa - 1];
                let total = base_parts + 1 + sufp[u];
                if total > ans {
                    ans = total;
                }
            } else {
                let total = base_parts + 1;
                if total > ans {
                    ans = total;
                }
            }
        }

        // Case 2: changed character is not in the current segment.
        let mut c: i64 = 0;
        while c < 26 {
            let bit = 1_i64 << (c as usize);

            if (base_mask & bit) == 0 {
                if base_cnt < k {
                    let q_i = k - base_cnt;
                    let q_us = q_i as usize;
                    let rr = rank_l[c as usize];

                    let mut take: usize = 0;
                    if rr > 0 && rr <= q_i {
                        take = q_us;
                    } else {
                        take = q_us - 1;
                    }

                    if take < l_len {
                        let u = l_pos[take];
                        let total = base_parts + 1 + sufp[u];
                        if total > ans {
                            ans = total;
                        }
                    } else {
                        let total = base_parts + 1;
                        if total > ans {
                            ans = total;
                        }
                    }
                } else {
                    // base_cnt == k
                    let kk = k;
                    let k_us = kk as usize;
                    let rr = rank_o[c as usize];

                    let mut take: usize = 0;
                    if rr > 0 && rr <= kk {
                        take = k_us;
                    } else {
                        take = k_us - 1;
                    }

                    if take < ord_len {
                        let u = ord_pos[take];
                        let total = base_parts + 2 + sufp[u];
                        if total > ans {
                            ans = total;
                        }
                    } else {
                        let total = base_parts + 2;
                        if total > ans {
                            ans = total;
                        }
                    }
                }
            }

            c += 1;
        }

        // Compute sufp[ii].
        let ci = (s[ii] as i64) - 97;
        let rr_i = rank_o[ci as usize];
        let kk_i = k;
        let k_us_i = kk_i as usize;

        let mut take_i: usize = 0;
        if rr_i > 0 && rr_i <= kk_i {
            take_i = k_us_i;
        } else {
            take_i = k_us_i - 1;
        }

        if take_i < ord_len {
            let u = ord_pos[take_i];
            sufp[ii] = 1 + sufp[u];
        } else {
            sufp[ii] = 1;
        }

        // Update suffix first-occurrence order by inserting s[ii] at the front.
        if rr_i > 0 {
            let idx = (rr_i - 1) as usize;
            let mut jj = idx;
            while jj > 0 {
                ord_chars[jj] = ord_chars[jj - 1];
                ord_pos[jj] = ord_pos[jj - 1];
                jj -= 1;
            }
            ord_chars[0] = ci;
            ord_pos[0] = ii;
        } else {
            ord_chars.push(0);
            ord_pos.push(0);

            let mut jj = ord_len;
            while jj > 0 {
                ord_chars[jj] = ord_chars[jj - 1];
                ord_pos[jj] = ord_pos[jj - 1];
                jj -= 1;
            }

            ord_chars[0] = ci;
            ord_pos[0] = ii;
            ord_len += 1;
        }
    }

    ans
}
