pub fn answer_queries(nums: &[i64], queries: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut sorted: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }

    let mut i = 1;
    while i < n {
        let key = sorted[i];
        let mut j = i;

        while j > 0 {
            if sorted[j - 1] > key {
                sorted[j] = sorted[j - 1];
                j -= 1;
            } else {
                break;
            }
        }

        sorted[j] = key;
        i += 1;
    }

    let mut prefix: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    let mut i = 0;
    while i < n {
        sum += sorted[i];
        prefix.push(sum);
        i += 1;
    }

    let m = queries.len();
    let mut answer: Vec<i64> = Vec::new();
    let mut qi = 0;

    while qi < m {
        let q = queries[qi];
        let mut count: i64 = 0;
        let mut k = 0;

        while k < n {
            if prefix[k] <= q {
                count += 1;
                k += 1;
            } else {
                break;
            }
        }

        answer.push(count);
        qi += 1;
    }

    answer
}
