fn bit_len(mut x: i64) -> i64 {
    let mut len: i64 = 0;
    while x > 0 {
        len += 1;
        x = x >> 1;
    }
    len
}

fn concat3(a: i64, b: i64, c: i64) -> i64 {
    let mut res: i64 = 0;
    res = (res << bit_len(a)) + a;
    res = (res << bit_len(b)) + b;
    res = (res << bit_len(c)) + c;
    res
}

pub fn max_good_number(nums: &[i64]) -> i64 {
    if nums.len() < 3 {
        return 0;
    }

    let a = nums[0];
    let b = nums[1];
    let c = nums[2];

    let mut best = concat3(a, b, c);

    let v1 = concat3(a, c, b);
    if v1 > best {
        best = v1;
    }

    let v2 = concat3(b, a, c);
    if v2 > best {
        best = v2;
    }

    let v3 = concat3(b, c, a);
    if v3 > best {
        best = v3;
    }

    let v4 = concat3(c, a, b);
    if v4 > best {
        best = v4;
    }

    let v5 = concat3(c, b, a);
    if v5 > best {
        best = v5;
    }

    best
}
