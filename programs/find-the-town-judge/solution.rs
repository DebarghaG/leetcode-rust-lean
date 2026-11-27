pub fn find_judge(n: i64, trust: &[Vec<i64>]) -> i64 {
    let size = n as usize;

    let mut indegree: Vec<i64> = Vec::new();
    let mut outdegree: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i <= size {
        indegree.push(0);
        outdegree.push(0);
        i += 1;
    }

    let m = trust.len();
    let mut k = 0usize;
    while k < m {
        let a = trust[k][0] as usize;
        let b = trust[k][1] as usize;
        outdegree[a] += 1;
        indegree[b] += 1;
        k += 1;
    }

    let mut judge: i64 = -1;
    let mut count: i64 = 0;

    let mut person = 1usize;
    while person <= size {
        if outdegree[person] == 0 && indegree[person] == n - 1 {
            judge = person as i64;
            count += 1;
        }
        person += 1;
    }

    if count == 1 {
        judge
    } else {
        -1
    }
}
