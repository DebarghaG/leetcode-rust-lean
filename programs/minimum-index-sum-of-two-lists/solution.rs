fn strings_equal(a: &[Vec<u8>], i: usize, b: &[Vec<u8>], j: usize) -> bool {
    if a[i].len() != b[j].len() {
        return false;
    }

    let mut k: usize = 0;
    while k < a[i].len() {
        if a[i][k] != b[j][k] {
            return false;
        }
        k += 1;
    }

    true
}

pub fn find_restaurant(list1: &[Vec<u8>], list2: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let n = list1.len();
    let m = list2.len();

    let mut best: i64 = 1000000;

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < m {
            if strings_equal(list1, i, list2, j) {
                let sum = i as i64 + j as i64;
                if sum < best {
                    best = sum;
                }
            }
            j += 1;
        }
        i += 1;
    }

    let mut out: Vec<Vec<u8>> = Vec::new();

    let mut i2: usize = 0;
    while i2 < n {
        let mut j2: usize = 0;
        while j2 < m {
            if strings_equal(list1, i2, list2, j2) {
                let sum = i2 as i64 + j2 as i64;
                if sum == best {
                    let mut row: Vec<u8> = Vec::new();
                    let mut k: usize = 0;
                    while k < list1[i2].len() {
                        row.push(list1[i2][k]);
                        k += 1;
                    }
                    out.push(row);
                }
            }
            j2 += 1;
        }
        i2 += 1;
    }

    out
}
