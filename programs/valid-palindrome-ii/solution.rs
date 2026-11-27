fn is_palindrome_range(s: &[u8], mut left: usize, mut right: usize) -> bool {
    while left < right {
        if s[left] != s[right] {
            return false;
        }
        left += 1;
        right -= 1;
    }
    true
}

pub fn valid_palindrome(s: &[u8]) -> bool {
    let n = s.len();
    if n <= 2 {
        return true;
    }

    let mut left: usize = 0;
    let mut right: usize = n - 1;

    while left < right {
        if s[left] == s[right] {
            left += 1;
            right -= 1;
        } else {
            return is_palindrome_range(s, left + 1, right)
                || is_palindrome_range(s, left, right - 1);
        }
    }

    true
}
