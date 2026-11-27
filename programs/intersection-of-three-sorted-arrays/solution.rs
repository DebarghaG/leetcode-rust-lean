pub fn arrays_intersection(arr1: &[i64], arr2: &[i64], arr3: &[i64]) -> Vec<i64> {
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut k: usize = 0;

    let mut result: Vec<i64> = Vec::new();

    while i < arr1.len() && j < arr2.len() && k < arr3.len() {
        let x = arr1[i];
        let y = arr2[j];
        let z = arr3[k];

        if x == y && y == z {
            result.push(x);
            i = i + 1;
            j = j + 1;
            k = k + 1;
        } else if x <= y && x <= z {
            i = i + 1;
        } else if y <= x && y <= z {
            j = j + 1;
        } else {
            k = k + 1;
        }
    }

    result
}
