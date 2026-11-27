pub fn count_words(words1: &[Vec<u8>], words2: &[Vec<u8>]) -> i64 {
    let n1 = words1.len();
    let n2 = words2.len();
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n1 {
        let mut count1: i64 = 0;
        let mut j: usize = 0;

        while j < n1 {
            let mut equal: bool = true;

            if words1[i].len() != words1[j].len() {
                equal = false;
            } else {
                let mut k: usize = 0;
                while k < words1[i].len() {
                    if words1[i][k] != words1[j][k] {
                        equal = false;
                        k = words1[i].len();
                    } else {
                        k += 1;
                    }
                }
            }

            if equal {
                count1 += 1;
            }

            j += 1;
        }

        if count1 == 1 {
            let mut count2: i64 = 0;
            let mut j2: usize = 0;

            while j2 < n2 {
                let mut equal2: bool = true;

                if words1[i].len() != words2[j2].len() {
                    equal2 = false;
                } else {
                    let mut k2: usize = 0;
                    while k2 < words1[i].len() {
                        if words1[i][k2] != words2[j2][k2] {
                            equal2 = false;
                            k2 = words1[i].len();
                        } else {
                            k2 += 1;
                        }
                    }
                }

                if equal2 {
                    count2 += 1;
                }

                j2 += 1;
            }

            if count2 == 1 {
                ans += 1;
            }
        }

        i += 1;
    }

    ans
}
