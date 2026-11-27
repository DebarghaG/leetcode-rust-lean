pub fn find_the_distance_value(arr1: &[i64], arr2: &[i64], d: i64) -> i64 {
    let mut count: i64 = 0;
    let n1 = arr1.len();
    let n2 = arr2.len();

    let mut i: usize = 0;
    while i < n1 {
        let a = arr1[i];
        let mut valid = true;

        let mut j: usize = 0;
        while j < n2 {
            let diff = a - arr2[j];
            if diff <= d && diff >= -d {
                valid = false;
            }
            j += 1;
        }

        if valid {
            count += 1;
        }

        i += 1;
    }

    count
}
