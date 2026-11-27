pub fn compare_version(version1: &[u8], version2: &[u8]) -> i64 {
    let n1: usize = version1.len();
    let n2: usize = version2.len();

    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < n1 || j < n2 {
        let mut v1: i64 = 0;
        while i < n1 && version1[i] != b'.' {
            let d1: i64 = (version1[i] - b'0') as i64;
            v1 = v1 * 10 + d1;
            i += 1;
        }
        if i < n1 {
            i += 1;
        }

        let mut v2: i64 = 0;
        while j < n2 && version2[j] != b'.' {
            let d2: i64 = (version2[j] - b'0') as i64;
            v2 = v2 * 10 + d2;
            j += 1;
        }
        if j < n2 {
            j += 1;
        }

        if v1 < v2 {
            return -1;
        }
        if v1 > v2 {
            return 1;
        }
    }

    0
}
