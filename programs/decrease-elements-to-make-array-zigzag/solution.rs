pub fn moves_to_make_zigzag(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut cost_even: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let mut min_neighbor: i64 = 1_000_000_000;

        if i > 0 {
            let v = nums[i - 1];
            if v < min_neighbor {
                min_neighbor = v;
            }
        }

        if i + 1 < n {
            let v = nums[i + 1];
            if v < min_neighbor {
                min_neighbor = v;
            }
        }

        let target = min_neighbor - 1;
        if nums[i] > target {
            cost_even = cost_even + (nums[i] - target);
        }

        i = i + 2;
    }

    let mut cost_odd: i64 = 0;
    let mut j: usize = 1;
    while j < n {
        let mut min_neighbor: i64 = 1_000_000_000;

        if j > 0 {
            let v = nums[j - 1];
            if v < min_neighbor {
                min_neighbor = v;
            }
        }

        if j + 1 < n {
            let v = nums[j + 1];
            if v < min_neighbor {
                min_neighbor = v;
            }
        }

        let target = min_neighbor - 1;
        if nums[j] > target {
            cost_odd = cost_odd + (nums[j] - target);
        }

        j = j + 2;
    }

    if cost_even < cost_odd {
        cost_even
    } else {
        cost_odd
    }
}
