pub fn second_greater_element(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut ans: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        ans.push(-1);
        i += 1;
    }

    let mut s1: Vec<usize> = Vec::new();
    let mut s2: Vec<usize> = Vec::new();
    let mut tmp: Vec<usize> = Vec::new();

    i = 0;
    while i < n {
        let x = nums[i];

        while s2.len() > 0 {
            let top = s2[s2.len() - 1];
            if nums[top] < x {
                ans[top] = x;
                s2.pop();
            } else {
                break;
            }
        }

        while s1.len() > 0 {
            let top = s1[s1.len() - 1];
            if nums[top] < x {
                s1.pop();
                tmp.push(top);
            } else {
                break;
            }
        }

        while tmp.len() > 0 {
            let top = tmp[tmp.len() - 1];
            tmp.pop();
            s2.push(top);
        }

        s1.push(i);
        i += 1;
    }

    ans
}
