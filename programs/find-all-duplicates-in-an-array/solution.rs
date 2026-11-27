pub fn find_duplicates(nums: &[i64]) -> Vec<i64> {
    let n: usize = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i = i + 1;
    }

    i = 0;
    while i < n {
        let mut active: bool = true;
        while active {
            let value: i64 = a[i];
            let wanted: i64 = (i as i64) + 1;

            if value == wanted {
                active = false;
            } else {
                let correct: usize = (value - 1) as usize;

                if a[correct] == value {
                    active = false;
                } else {
                    let tmp: i64 = a[i];
                    a[i] = a[correct];
                    a[correct] = tmp;
                }
            }
        }
        i = i + 1;
    }

    let mut out: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        if a[i] != (i as i64) + 1 {
            out.push(a[i]);
        }
        i = i + 1;
    }

    out
}
