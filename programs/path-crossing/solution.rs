pub fn is_path_crossing(path: &[u8]) -> bool {
    let mut xs: Vec<i64> = Vec::new();
    let mut ys: Vec<i64> = Vec::new();

    let mut x: i64 = 0;
    let mut y: i64 = 0;

    xs.push(x);
    ys.push(y);

    let n = path.len();
    let mut i: usize = 0;
    let mut crossed: bool = false;

    while i < n && !crossed {
        let c = path[i];

        if c == b'N' {
            y = y + 1;
        } else if c == b'S' {
            y = y - 1;
        } else if c == b'E' {
            x = x + 1;
        } else {
            x = x - 1;
        }

        let mut j: usize = 0;
        while j < xs.len() {
            if xs[j] == x && ys[j] == y {
                crossed = true;
            }
            j = j + 1;
        }

        xs.push(x);
        ys.push(y);
        i = i + 1;
    }

    crossed
}
