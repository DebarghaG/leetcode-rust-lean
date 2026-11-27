pub fn result_array(nums: &[i64]) -> Vec<i64> {
    let mut arr1: Vec<i64> = Vec::new();
    let mut arr2: Vec<i64> = Vec::new();

    arr1.push(nums[0]);
    arr2.push(nums[1]);

    let mut i: usize = 2;
    while i < nums.len() {
        let last1 = arr1[arr1.len() - 1];
        let last2 = arr2[arr2.len() - 1];

        if last1 > last2 {
            arr1.push(nums[i]);
        } else {
            arr2.push(nums[i]);
        }

        i += 1;
    }

    let mut result: Vec<i64> = Vec::new();

    let mut j: usize = 0;
    while j < arr1.len() {
        result.push(arr1[j]);
        j += 1;
    }

    let mut k: usize = 0;
    while k < arr2.len() {
        result.push(arr2[k]);
        k += 1;
    }

    result
}
