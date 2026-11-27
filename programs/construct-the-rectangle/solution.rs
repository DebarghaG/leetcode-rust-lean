pub fn construct_rectangle(area: i64) -> Vec<i64> {
    // Phase 1: compute s = floor(sqrt(area)) and rem = area - s*s
    // using only subtraction of consecutive odd numbers (purely affine loop).
    let mut s: i64 = 0;
    let mut odd: i64 = 1;
    let mut rem: i64 = area;
    while rem >= odd {
        rem = rem - odd;
        odd = odd + 2;
        s = s + 1;
    }

    // Phase 2: start = ceil(sqrt(area)).
    // rem == 0  => area is a perfect square, ceil == floor == s.
    // rem != 0  => ceil == s + 1.
    let mut start: i64 = s;
    if rem != 0 {
        start = s + 1;
    }

    // Phase 3: smallest divisor `l` of `area` with l >= start.
    // `area` itself is always such a divisor, so we always find one.
    // The loop variable is updated unconditionally (l = l + 1); we never
    // accumulate a conditionally-overwritten integer, we just return early.
    let mut l: i64 = start;
    while l <= area {
        if area % l == 0 {
            let w: i64 = area / l;
            let mut out: Vec<i64> = Vec::new();
            out.push(l);
            out.push(w);
            return out;
        }
        l = l + 1;
    }

    // Fallback (unreachable for area >= 1).
    let mut out: Vec<i64> = Vec::new();
    out.push(area);
    out.push(1);
    out
}
