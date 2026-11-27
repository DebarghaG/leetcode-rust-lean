pub fn can_complete_circuit(gas: &[i64], cost: &[i64]) -> i64 {
    let n = gas.len();
    if n == 0 {
        return -1;
    }

    let mut start = n - 1;
    let mut end = 0usize;
    let mut tank = gas[start] - cost[start];

    while start > end {
        if tank >= 0 {
            tank += gas[end] - cost[end];
            end += 1;
        } else {
            start -= 1;
            tank += gas[start] - cost[start];
        }
    }

    if tank >= 0 {
        start as i64
    } else {
        -1
    }
}
