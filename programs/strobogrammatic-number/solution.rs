pub fn is_strobogrammatic(num: &[u8]) -> bool {
    let n: usize = num.len();
    let mut result: bool = true;

    if n == 0 {
        result = true;
    } else {
        let mut left: usize = 0;
        let mut right: usize = n - 1;

        while left < right {
            let a: u8 = num[left];
            let b: u8 = num[right];

            let ok: bool =
                (a == b'0' && b == b'0') ||
                (a == b'1' && b == b'1') ||
                (a == b'8' && b == b'8') ||
                (a == b'6' && b == b'9') ||
                (a == b'9' && b == b'6');

            if !ok {
                result = false;
                left = right;
            } else {
                left += 1;
                right -= 1;
            }
        }

        if result && n % 2 == 1 {
            let mid: u8 = num[n / 2];
            if mid != b'0' && mid != b'1' && mid != b'8' {
                result = false;
            }
        }
    }

    result
}
