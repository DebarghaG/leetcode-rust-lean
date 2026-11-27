pub fn asteroid_collision(asteroids: &[i64]) -> Vec<i64> {
    let mut stack: Vec<i64> = Vec::new();
    let n: usize = asteroids.len();
    let mut i: usize = 0;

    while i < n {
        let a: i64 = asteroids[i];

        if a > 0 {
            stack.push(a);
        } else {
            let mut alive: bool = true;
            let abs_a: i64 = -a;

            while alive && stack.len() > 0 && stack[stack.len() - 1] > 0 {
                let top_index: usize = stack.len() - 1;
                let top: i64 = stack[top_index];

                if top < abs_a {
                    let _ = stack.pop();
                } else if top == abs_a {
                    let _ = stack.pop();
                    alive = false;
                } else {
                    alive = false;
                }
            }

            if alive {
                stack.push(a);
            }
        }

        i += 1;
    }

    stack
}
