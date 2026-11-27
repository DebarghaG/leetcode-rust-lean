pub fn sum_even_after_queries(nums: &[i64], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = nums.len();
    let mut arr: Vec<i64> = Vec::new();
    let mut even_sum: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let x = nums[i];
        arr.push(x);
        if x % 2 == 0 {
            even_sum = even_sum + x;
        }
        i = i + 1;
    }

    let mut answer: Vec<i64> = Vec::new();
    let q = queries.len();
    let mut j: usize = 0;

    while j < q {
        let val = queries[j][0];
        let idx = queries[j][1] as usize;

        let old = arr[idx];
        if old % 2 == 0 {
            even_sum = even_sum - old;
        }

        let new_value = old + val;
        if new_value % 2 == 0 {
            even_sum = even_sum + new_value;
        }

        arr[idx] = new_value;
        answer.push(even_sum);

        j = j + 1;
    }

    answer
}
