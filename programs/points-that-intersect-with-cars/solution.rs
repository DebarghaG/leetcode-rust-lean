pub fn number_of_points(nums: &[Vec<i64>]) -> i64 {
    let mut covered: Vec<bool> = Vec::new();

    let mut i: usize = 0;
    while i <= 100 {
        covered.push(false);
        i += 1;
    }

    let mut j: usize = 0;
    while j < nums.len() {
        let start = nums[j][0];
        let end = nums[j][1];

        let mut p = start;
        while p <= end {
            covered[p as usize] = true;
            p += 1;
        }

        j += 1;
    }

    let mut count: i64 = 0;
    let mut k: usize = 1;
    while k <= 100 {
        if covered[k] {
            count += 1;
        }
        k += 1;
    }

    count
}
