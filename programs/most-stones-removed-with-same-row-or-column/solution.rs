pub fn remove_stones(stones: &[Vec<i64>]) -> i64 {
    let n: usize = stones.len();
    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        parent.push(i as i64);
        size.push(1);
        i += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            if stones[i][0] == stones[j][0] || stones[i][1] == stones[j][1] {
                let mut ri: i64 = i as i64;
                while parent[ri as usize] != ri {
                    ri = parent[ri as usize];
                }

                let mut rj: i64 = j as i64;
                while parent[rj as usize] != rj {
                    rj = parent[rj as usize];
                }

                if ri != rj {
                    if size[ri as usize] < size[rj as usize] {
                        parent[ri as usize] = rj;
                        size[rj as usize] = size[rj as usize] + size[ri as usize];
                    } else {
                        parent[rj as usize] = ri;
                        size[ri as usize] = size[ri as usize] + size[rj as usize];
                    }
                }
            }
            j += 1;
        }
        i += 1;
    }

    let mut components: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if parent[i] == i as i64 {
            components += 1;
        }
        i += 1;
    }

    n as i64 - components
}
