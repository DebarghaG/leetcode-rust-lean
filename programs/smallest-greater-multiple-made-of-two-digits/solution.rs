pub fn find_integer(k: i64, digit1: i64, digit2: i64) -> i64 {
    let limit: i64 = 2147483647;

    let small = if digit1 < digit2 { digit1 } else { digit2 };
    let large = if digit1 < digit2 { digit2 } else { digit1 };

    if small == 0 && large == 0 {
        return -1;
    }

    let mut queue: Vec<i64> = Vec::new();

    // Start with one-digit numbers, but never start with 0.
    if small != 0 {
        queue.push(small);
    }
    if large != 0 && large != small {
        queue.push(large);
    }

    let mut head: usize = 0;

    while head < queue.len() {
        let n = queue[head];
        head = head + 1;

        if n > k && n % k == 0 {
            return n;
        }

        let next1 = n * 10 + small;
        if next1 <= limit {
            queue.push(next1);
        }

        if large != small {
            let next2 = n * 10 + large;
            if next2 <= limit {
                queue.push(next2);
            }
        }
    }

    -1
}
