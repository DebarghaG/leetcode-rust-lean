fn sort_i64s(v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    if n <= 1 {
        return v;
    }

    let mut src = v;
    let mut dst: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        dst.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mid0 = left + width;
            let mid = if mid0 < n { mid0 } else { n };
            let right0 = left + width * 2;
            let right = if right0 < n { right0 } else { n };

            let mut p = left;
            let mut q = mid;
            let mut k = left;

            while p < mid && q < right {
                if src[p] <= src[q] {
                    dst[k] = src[p];
                    p += 1;
                } else {
                    dst[k] = src[q];
                    q += 1;
                }
                k += 1;
            }

            while p < mid {
                dst[k] = src[p];
                p += 1;
                k += 1;
            }

            while q < right {
                dst[k] = src[q];
                q += 1;
                k += 1;
            }

            left = right;
        }

        let mut tmp = src;
        src = dst;
        dst = tmp;
        width = width * 2;
    }

    src
}

pub fn find_num_of_valid_words(words: &[Vec<u8>], puzzles: &[Vec<u8>]) -> Vec<i64> {
    let mut raw: Vec<i64> = Vec::new();

    let mut wi: usize = 0;
    while wi < words.len() {
        let word = &words[wi];
        let mut mask: i64 = 0;
        let mut j: usize = 0;
        while j < word.len() {
            let b: u8 = word[j];
            let d: usize = (b - b'a') as usize;
            mask = mask | (1_i64 << d);
            j += 1;
        }
        raw.push(mask);
        wi += 1;
    }

    let sorted = sort_i64s(raw);

    let mut uniq: Vec<i64> = Vec::new();
    let mut freq: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < sorted.len() {
        let cur = sorted[i];
        let mut j = i + 1;
        while j < sorted.len() && sorted[j] == cur {
            j += 1;
        }
        uniq.push(cur);
        freq.push((j - i) as i64);
        i = j;
    }

    let mut first_masks: Vec<Vec<i64>> = Vec::new();
    let mut first_freqs: Vec<Vec<i64>> = Vec::new();
    let mut first_totals: Vec<i64> = Vec::new();

    let mut d: usize = 0;
    while d < 26 {
        first_masks.push(Vec::new());
        first_freqs.push(Vec::new());
        first_totals.push(0);
        d += 1;
    }

    let mut u: usize = 0;
    while u < uniq.len() {
        let m = uniq[u];
        let f = freq[u];

        let mut bit_index: usize = 0;
        while bit_index < 26 {
            let bit = 1_i64 << bit_index;
            if (m & bit) != 0 {
                first_masks[bit_index].push(m);
                first_freqs[bit_index].push(f);
                first_totals[bit_index] = first_totals[bit_index] + f;
            }
            bit_index += 1;
        }

        u += 1;
    }

    let all_mask: i64 = (1_i64 << 26) - 1;
    let mut ans: Vec<i64> = Vec::new();

    let mut pi: usize = 0;
    while pi < puzzles.len() {
        let puz = &puzzles[pi];

        if puz.len() == 0 {
            ans.push(0);
        } else {
            let first_byte = puz[0];
            let first_d: usize = (first_byte - b'a') as usize;
            let first_bit: i64 = 1_i64 << first_d;

            let mut pmask: i64 = 0;
            let mut j: usize = 0;
            while j < puz.len() {
                let b = puz[j];
                let d2: usize = (b - b'a') as usize;
                pmask = pmask | (1_i64 << d2);
                j += 1;
            }

            let others: i64 = pmask - first_bit;
            let mut total: i64 = 0;

            if pmask == all_mask {
                total = first_totals[first_d];
            } else {
                let mut subset_cost: i64 = 1;
                let mut e: usize = 1;
                while e < puz.len() {
                    if subset_cost <= 1000000000 {
                        subset_cost = subset_cost * 2;
                    }
                    e += 1;
                }

                let fallback_cost: i64 = first_masks[first_d].len() as i64;

                if subset_cost <= fallback_cost {
                    let mut sub: i64 = others;
                    loop {
                        let target: i64 = sub | first_bit;

                        let mut lo: usize = 0;
                        let mut hi: usize = uniq.len();
                        while lo < hi {
                            let mid = lo + (hi - lo) / 2;
                            if uniq[mid] < target {
                                lo = mid + 1;
                            } else {
                                hi = mid;
                            }
                        }

                        if lo < uniq.len() {
                            if uniq[lo] == target {
                                total = total + freq[lo];
                            }
                        }

                        if sub == 0 {
                            break;
                        }
                        sub = (sub - 1) & others;
                    }
                } else {
                    let list_masks = &first_masks[first_d];
                    let list_freqs = &first_freqs[first_d];

                    let mut q: usize = 0;
                    while q < list_masks.len() {
                        let m = list_masks[q];
                        if (m & pmask) == m {
                            total = total + list_freqs[q];
                        }
                        q += 1;
                    }
                }
            }

            ans.push(total);
        }

        pi += 1;
    }

    ans
}
