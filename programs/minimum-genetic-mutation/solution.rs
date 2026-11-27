fn gene_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }

    let mut i: usize = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }

    true
}

fn gene_diff_one(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }

    let mut i: usize = 0;
    let mut count: i64 = 0;

    while i < a.len() {
        if a[i] != b[i] {
            count += 1;
        }
        i += 1;
    }

    count == 1
}

pub fn min_mutation(startGene: &[u8], endGene: &[u8], bank: &[Vec<u8>]) -> i64 {
    if gene_eq(startGene, endGene) {
        return 0;
    }

    let n: usize = bank.len();
    let n_id: i64 = n as i64;

    let mut visited: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        visited.push(false);
        i += 1;
    }

    let mut queue_node: Vec<i64> = Vec::new();
    let mut queue_dist: Vec<i64> = Vec::new();

    queue_node.push(n_id);
    queue_dist.push(0);

    let mut head: usize = 0;
    let mut result: i64 = -1;
    let mut done: bool = false;

    while head < queue_node.len() && !done {
        let cur: i64 = queue_node[head];
        let d: i64 = queue_dist[head];
        head += 1;

        let cur_is_start: bool = cur == n_id;
        let cur_idx: usize = if cur == n_id { 0 } else { cur as usize };

        let mut j: usize = 0;
        while j < n && !done {
            if !visited[j] {
                let is_neighbor: bool = if cur_is_start {
                    gene_diff_one(startGene, &bank[j])
                } else {
                    gene_diff_one(&bank[cur_idx], &bank[j])
                };

                if is_neighbor {
                    if gene_eq(&bank[j], endGene) {
                        result = d + 1;
                        done = true;
                    } else {
                        visited[j] = true;
                        queue_node.push(j as i64);
                        queue_dist.push(d + 1);
                    }
                }
            }

            j += 1;
        }
    }

    result
}
