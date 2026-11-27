pub fn compress(chars: &[Vec<u8>]) -> i64 {
    let n = chars.len();
    if n == 0 {
        return 0;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let first = &chars[i];
        let c = first[0];

        let mut count: i64 = 0;
        let mut j: usize = i;

        while j < n {
            let current = &chars[j];
            if current[0] != c {
                break;
            }
            count += 1;
            j += 1;
        }

        total += 1;

        if count > 1 {
            let mut x = count;
            while x > 0 {
                total += 1;
                x = x / 10;
            }
        }

        i = j;
    }

    total
}
