pub fn get_xor_sum(arr1: &[i64], arr2: &[i64]) -> i64 {
    let mut xor1: i64 = 0;
    let mut xor2: i64 = 0;

    let mut i: usize = 0;
    while i < arr1.len() {
        xor1 ^= arr1[i];
        i += 1;
    }

    let mut j: usize = 0;
    while j < arr2.len() {
        xor2 ^= arr2[j];
        j += 1;
    }

    xor1 & xor2
}
