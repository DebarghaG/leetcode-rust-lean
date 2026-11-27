// One DP transition per recursive call. No loops => no loop-fixed-point needed.
// State = (absences in {0,1}) x (trailing lates in {0,1,2}), stored flat.
fn step(remaining: usize,
        a0l0: i64, a0l1: i64, a0l2: i64,
        a1l0: i64, a1l1: i64, a1l2: i64) -> i64 {
    let m: i64 = 1000000007;
    if remaining == 0 {
        return (a0l0 + a0l1 + a0l2 + a1l0 + a1l1 + a1l2) % m;
    }
    // Totals of the previous state, split by absence count.
    let s0 = (a0l0 + a0l1 + a0l2) % m;
    let s1 = (a1l0 + a1l1 + a1l2) % m;
    // Append 'P' -> trailing lates reset to 0 (and 'A' promotes a0* -> a1l0).
    // Append 'L' -> trailing lates shift up by 1.
    step(remaining - 1,
         s0,                          // new a0l0  (P on zero-absence)
         a0l0,                        // new a0l1  (L on a0l0)
         a0l1,                        // new a0l2  (L on a0l1)
         (s0 + s1) % m,               // new a1l0  (P on one-absence OR A on zero-absence)
         a1l0,                        // new a1l1  (L on a1l0)
         a1l1)                        // new a1l2  (L on a1l1)
}

pub fn check_record(n: i64) -> i64 {
    if n <= 0 {
        return 1;
    }
    // Start from the empty record: one way, 0 absences, 0 trailing lates.
    step(n as usize, 1, 0, 0, 0, 0, 0)
}
