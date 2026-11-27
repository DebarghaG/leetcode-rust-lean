pub fn count_distinct(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut children: Vec<Vec<i64>> = Vec::new();

    let mut root: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        root.push(-1);
        k += 1;
    }
    children.push(root);

    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut node: usize = 0;
        let mut j: usize = i;

        while j < n {
            let c: usize = (s[j] as usize) - (b'a' as usize);
            let child: i64 = children[node][c];

            if child == -1 {
                let mut row: Vec<i64> = Vec::new();
                let mut m: usize = 0;
                while m < 26 {
                    row.push(-1);
                    m += 1;
                }

                let new_node_i64: i64 = children.len() as i64;
                children.push(row);
                children[node][c] = new_node_i64;

                node = new_node_i64 as usize;
                count += 1;
            } else {
                node = child as usize;
            }

            j += 1;
        }

        i += 1;
    }

    count
}
