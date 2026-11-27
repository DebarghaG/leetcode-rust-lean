fn reverse_number(mut x: i64) -> i64 {
    let mut rev: i64 = 0;
    while x > 0 {
        rev = rev * 10 + (x % 10);
        x = x / 10;
    }
    rev
}

pub fn count_distinct_integers(nums: &[i64]) -> i64 {
    let n = nums.len();
    let m = n * 2;

    let mut arr: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let x = nums[i];
        arr.push(x);
        arr.push(reverse_number(x));
        i += 1;
    }

    if m == 0 {
        return 0;
    }

    let radix: usize = 1024;

    let mut tmp: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < m {
        tmp.push(0);
        j += 1;
    }

    let mut counts: Vec<i64> = Vec::new();
    j = 0;
    while j < radix {
        counts.push(0);
        j += 1;
    }

    // First radix pass: low 10 bits, arr -> tmp.
    j = 0;
    while j < radix {
        counts[j] = 0;
        j += 1;
    }

    i = 0;
    while i < m {
        let key = (arr[i] % 1024) as usize;
        counts[key] = counts[key] + 1;
        i += 1;
    }

    let mut sum: i64 = 0;
    j = 0;
    while j < radix {
        let c = counts[j];
        counts[j] = sum;
        sum = sum + c;
        j += 1;
    }

    i = 0;
    while i < m {
        let v = arr[i];
        let key = (v % 1024) as usize;
        let pos = counts[key] as usize;
        tmp[pos] = v;
        counts[key] = counts[key] + 1;
        i += 1;
    }

    // Second radix pass: high 10 bits, tmp -> arr.
    j = 0;
    while j < radix {
        counts[j] = 0;
        j += 1;
    }

    i = 0;
    while i < m {
        let v = tmp[i];
        let key = ((v / 1024) % 1024) as usize;
        counts[key] = counts[key] + 1;
        i += 1;
    }

    sum = 0;
    j = 0;
    while j < radix {
        let c = counts[j];
        counts[j] = sum;
        sum = sum + c;
        j += 1;
    }

    i = 0;
    while i < m {
        let v = tmp[i];
        let key = ((v / 1024) % 1024) as usize;
        let pos = counts[key] as usize;
        arr[pos] = v;
        counts[key] = counts[key] + 1;
        i += 1;
    }

    let mut distinct: i64 = 1;
    i = 1;
    while i < m {
        if arr[i] != arr[i - 1] {
            distinct += 1;
        }
        i += 1;
    }

    distinct
}
