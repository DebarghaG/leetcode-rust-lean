pub fn largest_perimeter(nums: &[i64]) -> i64 {
    let n = nums.len();

    // Copy into an owned Vec so we can sort it.
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    // Manual bubble sort (ascending).
    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j + 1 < n - i {
            if a[j] > a[j + 1] {
                let t = a[j];
                a[j] = a[j + 1];
                a[j + 1] = t;
            }
            j += 1;
        }
        i += 1;
    }

    // Scan consecutive triples from the largest downward.
    let mut result: i64 = 0;
    let mut idx: usize = n;
    let mut found: bool = false;
    while idx >= 3 && found == false {
        let c = a[idx - 1];
        let b = a[idx - 2];
        let d = a[idx - 3];
        if d + b > c {
            result = d + b + c;
            found = true;
        } else {
            idx -= 1;
        }
    }

    result
}
