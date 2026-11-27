pub fn min_subsequence(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut total: i64 = 0;
    let mut copy: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        total += nums[i];
        copy.push(nums[i]);
        i += 1;
    }

    // Sort copy in non-increasing order using a manual selection sort.
    let mut a = 0;
    while a < n {
        let mut b = a + 1;
        while b < n {
            if copy[b] > copy[a] {
                let tmp = copy[a];
                copy[a] = copy[b];
                copy[b] = tmp;
            }
            b += 1;
        }
        a += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut chosen_sum: i64 = 0;
    let mut j = 0;
    let mut done = false;

    while j < n && !done {
        chosen_sum += copy[j];
        result.push(copy[j]);

        if chosen_sum > total - chosen_sum {
            done = true;
        }

        j += 1;
    }

    result
}
