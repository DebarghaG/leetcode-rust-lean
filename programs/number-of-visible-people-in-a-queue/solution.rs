pub fn can_see_persons_count(heights: &[i64]) -> Vec<i64> {
    let n = heights.len();
    let mut ans: Vec<i64> = Vec::new();

    let mut k = 0;
    while k < n {
        ans.push(0);
        k += 1;
    }

    let mut stack: Vec<i64> = Vec::new();
    let mut i = n;

    while i > 0 {
        i -= 1;
        let h = heights[i];
        let mut count: i64 = 0;

        while stack.len() > 0 {
            let top_index = stack.len() - 1;
            let top = stack[top_index];

            if top < h {
                stack.pop();
                count += 1;
            } else {
                break;
            }
        }

        if stack.len() > 0 {
            count += 1;
        }

        ans[i] = count;
        stack.push(h);
    }

    ans
}
