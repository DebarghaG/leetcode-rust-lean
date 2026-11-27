pub fn maximum_score(scores: &[i64], edges: &[Vec<i64>]) -> i64 {
    let n = scores.len();
    if n < 4 {
        return -1;
    }

    let mut best1: Vec<i64> = Vec::new();
    let mut best2: Vec<i64> = Vec::new();
    let mut best3: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        best1.push(-1);
        best2.push(-1);
        best3.push(-1);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let a_i = edges[e][0];
        let b_i = edges[e][1];
        let a = a_i as usize;
        let b = b_i as usize;

        if best1[a] == -1 {
            best1[a] = b_i;
        } else if scores[b] > scores[best1[a] as usize] {
            best3[a] = best2[a];
            best2[a] = best1[a];
            best1[a] = b_i;
        } else if best2[a] == -1 {
            best2[a] = b_i;
        } else if scores[b] > scores[best2[a] as usize] {
            best3[a] = best2[a];
            best2[a] = b_i;
        } else if best3[a] == -1 {
            best3[a] = b_i;
        } else if scores[b] > scores[best3[a] as usize] {
            best3[a] = b_i;
        }

        if best1[b] == -1 {
            best1[b] = a_i;
        } else if scores[a] > scores[best1[b] as usize] {
            best3[b] = best2[b];
            best2[b] = best1[b];
            best1[b] = a_i;
        } else if best2[b] == -1 {
            best2[b] = a_i;
        } else if scores[a] > scores[best2[b] as usize] {
            best3[b] = best2[b];
            best2[b] = a_i;
        } else if best3[b] == -1 {
            best3[b] = a_i;
        } else if scores[a] > scores[best3[b] as usize] {
            best3[b] = a_i;
        }

        e += 1;
    }

    let mut ans: i64 = -1;
    e = 0;
    while e < edges.len() {
        let u_i = edges[e][0];
        let v_i = edges[e][1];
        let u = u_i as usize;
        let v = v_i as usize;

        let mut ii: i64 = 0;
        while ii < 3 {
            let mut x: i64 = -1;
            if ii == 0 {
                x = best1[u];
            } else if ii == 1 {
                x = best2[u];
            } else {
                x = best3[u];
            }

            if x != -1 {
                let mut jj: i64 = 0;
                while jj < 3 {
                    let mut y: i64 = -1;
                    if jj == 0 {
                        y = best1[v];
                    } else if jj == 1 {
                        y = best2[v];
                    } else {
                        y = best3[v];
                    }

                    if y != -1 && x != y && x != v_i && y != u_i {
                        let s = scores[x as usize] + scores[u] + scores[v] + scores[y as usize];
                        if s > ans {
                            ans = s;
                        }
                    }

                    jj += 1;
                }
            }

            ii += 1;
        }

        e += 1;
    }

    ans
}
