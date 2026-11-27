pub fn largest_rectangle_area(heights: &[i64]) -> i64 {
    let n = heights.len();
    let mut best: i64 = 0;
    let mut stack: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let cur = heights[i];

        while stack.len() > 0 {
            let top_i64 = stack[stack.len() - 1];
            let top = top_i64 as usize;

            if heights[top] > cur {
                stack.pop();

                let height = heights[top];

                let left: usize;
                if stack.len() == 0 {
                    left = 0;
                } else {
                    left = stack[stack.len() - 1] as usize + 1;
                }

                let width = (i - left) as i64;
                let area = height * width;
                if area > best {
                    best = area;
                }
            } else {
                break;
            }
        }

        stack.push(i as i64);
        i += 1;
    }

    while stack.len() > 0 {
        let top_i64 = stack[stack.len() - 1];
        let top = top_i64 as usize;
        stack.pop();

        let height = heights[top];

        let left: usize;
        if stack.len() == 0 {
            left = 0;
        } else {
            left = stack[stack.len() - 1] as usize + 1;
        }

        let width = (n - left) as i64;
        let area = height * width;
        if area > best {
            best = area;
        }
    }

    best
}
