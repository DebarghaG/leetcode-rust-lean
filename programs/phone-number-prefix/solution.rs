fn is_prefix(numbers: &[Vec<u8>], i: usize, j: usize) -> bool {
    let li = numbers[i].len();
    let lj = numbers[j].len();
    let mut result: bool = true;

    if li > lj {
        result = false;
    } else {
        let mut k: usize = 0;
        while k < li {
            if numbers[i][k] != numbers[j][k] {
                result = false;
            }
            k += 1;
        }
    }

    result
}

pub fn phone_prefix(numbers: &[Vec<u8>]) -> bool {
    let n = numbers.len();
    let mut ok: bool = true;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = 0;

        while j < n {
            if ok && j > i {
                if is_prefix(numbers, i, j) {
                    ok = false;
                }
                if is_prefix(numbers, j, i) {
                    ok = false;
                }
            }
            j += 1;
        }

        i += 1;
    }

    ok
}
