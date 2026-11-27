pub fn can_be_equal(target: &[i64], arr: &[i64]) -> bool {
    let n: usize = target.len();
    if n != arr.len() {
        return false;
    }

    let mut used: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        used.push(false);
        i += 1;
    }

    i = 0;
    while i < n {
        let x: i64 = target[i];
        let mut found: bool = false;
        let mut j: usize = 0;

        while j < n {
            if found == false {
                if used[j] == false {
                    if arr[j] == x {
                        used[j] = true;
                        found = true;
                    }
                }
            }
            j += 1;
        }

        if found == false {
            return false;
        }

        i += 1;
    }

    true
}
