pub fn pivot_array(nums: &[i64], pivot: i64) -> Vec<i64> {
    let n = nums.len();

    let mut less: Vec<i64> = Vec::new();
    let mut equal: Vec<i64> = Vec::new();
    let mut greater: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let x = nums[i];
        if x < pivot {
            less.push(x);
        } else if x > pivot {
            greater.push(x);
        } else {
            equal.push(x);
        }
        i += 1;
    }

    let mut out: Vec<i64> = Vec::new();

    let mut j: usize = 0;
    while j < less.len() {
        out.push(less[j]);
        j += 1;
    }

    let mut k: usize = 0;
    while k < equal.len() {
        out.push(equal[k]);
        k += 1;
    }

    let mut m: usize = 0;
    while m < greater.len() {
        out.push(greater[m]);
        m += 1;
    }

    out
}
