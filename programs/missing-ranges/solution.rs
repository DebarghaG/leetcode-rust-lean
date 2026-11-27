#[allow(unused_macros)]
macro_rules! vec {
    () => {
        ::std::vec::Vec::<::std::vec::Vec<i64>>::new()
    };
    ($($item:expr),+ $(,)?) => {{
        let mut v = ::std::vec::Vec::new();
        $(
            v.push($item);
        )+
        v
    }};
}

pub fn find_missing_ranges(nums: &[i64], lower: i64, upper: i64) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut next: i64 = lower;
    let mut i: usize = 0;
    let n: usize = nums.len();

    while i < n {
        let x: i64 = nums[i];
        if x > next {
            let mut range: Vec<i64> = Vec::new();
            range.push(next);
            range.push(x - 1);
            out.push(range);
        }
        next = x + 1;
        i += 1;
    }

    if next <= upper {
        let mut range: Vec<i64> = Vec::new();
        range.push(next);
        range.push(upper);
        out.push(range);
    }

    out
}
