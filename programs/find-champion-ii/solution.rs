pub fn find_champion(n: i64, edges: &[Vec<i64>]) -> i64 {
    let nn: usize = n as usize;

    let mut indegree: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < nn {
        indegree.push(0);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let to: usize = edges[e][1] as usize;
        indegree[to] = indegree[to] + 1;
        e += 1;
    }

    let mut champion: i64 = -1;
    let mut count: i64 = 0;
    let mut j: usize = 0;
    while j < nn {
        if indegree[j] == 0 {
            count += 1;
            champion = j as i64;
        }
        j += 1;
    }

    if count == 1 {
        champion
    } else {
        -1
    }
}
