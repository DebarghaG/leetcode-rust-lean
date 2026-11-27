pub fn find_indices(nums: &[i64], indexDifference: i64, valueDifference: i64) -> Vec<i64> {
    let n = nums.len() as i64;
    let mut min_index: i64 = 0;
    let mut max_index: i64 = 0;
    let mut i: i64 = indexDifference;

    while i < n {
        let j: i64 = i - indexDifference;
        let nv = nums[j as usize];

        if nv < nums[min_index as usize] {
            min_index = j;
        }
        if nv > nums[max_index as usize] {
            max_index = j;
        }

        if nums[i as usize] - nums[min_index as usize] >= valueDifference {
            let mut answer: Vec<i64> = Vec::new();
            answer.push(min_index);
            answer.push(i);
            return answer;
        }

        if nums[max_index as usize] - nums[i as usize] >= valueDifference {
            let mut answer: Vec<i64> = Vec::new();
            answer.push(max_index);
            answer.push(i);
            return answer;
        }

        i += 1;
    }

    let mut answer: Vec<i64> = Vec::new();
    answer.push(-1);
    answer.push(-1);
    answer
}
