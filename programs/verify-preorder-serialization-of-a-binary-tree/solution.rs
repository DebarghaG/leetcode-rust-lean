pub fn is_valid_serialization(preorder: &[u8]) -> bool {
    let n = preorder.len();

    let mut valid: bool = n > 0;
    let mut slots: i64 = 1;
    let mut i: usize = 0;

    while i < n && valid {
        if slots <= 0 {
            valid = false;
        } else {
            let mut j = i;
            while j < n && preorder[j] != b',' {
                j += 1;
            }

            if j == i {
                valid = false;
            } else {
                let is_null = (j - i == 1) && preorder[i] == b'#';

                slots -= 1;
                if !is_null {
                    slots += 2;
                }

                if j == n {
                    i = n;
                } else {
                    i = j + 1;
                }
            }
        }
    }

    valid && slots == 0
}
