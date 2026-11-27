pub fn find_circle_num(isConnected: &[Vec<i64>]) -> i64 {
    let n = isConnected.len();

    let mut parent: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        parent.push(i as i64);
        i += 1;
    }

    let mut count: i64 = n as i64;
    let mut a: usize = 0;

    while a < n {
        let mut b: usize = a + 1;

        while b < n {
            if isConnected[a][b] == 1 {
                let mut ra: i64 = a as i64;
                while parent[ra as usize] != ra {
                    ra = parent[ra as usize];
                }

                let mut rb: i64 = b as i64;
                while parent[rb as usize] != rb {
                    rb = parent[rb as usize];
                }

                if ra != rb {
                    parent[rb as usize] = ra;
                    count -= 1;
                }
            }

            b += 1;
        }

        a += 1;
    }

    count
}
