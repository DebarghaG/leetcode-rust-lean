pub fn valid_utf8(data: &[i64]) -> bool {
    let n = data.len();
    let mut i: usize = 0;
    let mut need: i64 = 0;
    let mut valid: bool = true;

    while i < n && valid {
        let b = data[i] & 255;

        if need > 0 {
            if b & 192 != 128 {
                valid = false;
            } else {
                need = need - 1;
            }
        } else {
            if b & 128 == 0 {
                need = 0;
            } else if b & 224 == 192 {
                need = 1;
            } else if b & 240 == 224 {
                need = 2;
            } else if b & 248 == 240 {
                need = 3;
            } else {
                valid = false;
            }
        }

        i = i + 1;
    }

    if need != 0 {
        valid = false;
    }

    valid
}
