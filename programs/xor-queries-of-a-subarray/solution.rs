pub fn xor_queries(arr: &[i64], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = arr.len();

    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);

    let mut i: usize = 0;
    while i < n {
        let prev = prefix[i];
        prefix.push(prev ^ arr[i]);
        i += 1;
    }

    let m = queries.len();
    let mut answer: Vec<i64> = Vec::new();

    let mut j: usize = 0;
    while j < m {
        let left = queries[j][0] as usize;
        let right = queries[j][1] as usize;
        let value = prefix[right + 1] ^ prefix[left];
        answer.push(value);
        j += 1;
    }

    answer
}
