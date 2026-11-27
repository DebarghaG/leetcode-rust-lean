pub fn number_of_ways(s: &[u8]) -> i64 {
    let mut count0: i64 = 0;
    let mut count1: i64 = 0;
    let mut seq01: i64 = 0;
    let mut seq10: i64 = 0;
    let mut ans: i64 = 0;

    let n = s.len();
    let mut i: usize = 0;

    while i < n {
        if s[i] == 48u8 {
            // Append this '0' to every previous "01" subsequence to form "010".
            ans += seq01;
            // Append this '0' to every previous '1' to form "10".
            seq10 += count1;
            count0 += 1;
        } else {
            // Append this '1' to every previous "10" subsequence to form "101".
            ans += seq10;
            // Append this '1' to every previous '0' to form "01".
            seq01 += count0;
            count1 += 1;
        }

        i += 1;
    }

    ans
}
