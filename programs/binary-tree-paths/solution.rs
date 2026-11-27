pub fn binary_tree_paths(root: &Tree) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut path: Vec<u8> = Vec::new();
    collect_paths(root, &path, &mut out);
    out
}

fn collect_paths(t: &Tree, path: &[u8], out: &mut Vec<Vec<u8>>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            let new_path = append_value(path, *v);
            let left_is_null = match &**l {
                Tree::Null => true,
                _ => false,
            };
            let right_is_null = match &**r {
                Tree::Null => true,
                _ => false,
            };

            if left_is_null && right_is_null {
                out.push(new_path);
            } else {
                if !left_is_null {
                    collect_paths(&**l, &new_path, out);
                }
                if !right_is_null {
                    collect_paths(&**r, &new_path, out);
                }
            }
        }
    }
}

fn append_value(path: &[u8], val: i64) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();

    let mut i: usize = 0;
    while i < path.len() {
        out.push(path[i]);
        i += 1;
    }

    if out.len() > 0 {
        out.push(b'-');
        out.push(b'>');
    }

    let mut x: i64 = val;
    if x < 0 {
        out.push(b'-');
        x = -x;
    }

    if x >= 100 {
        out.push(b'1');
        x = x - 100;
        out.push(b'0' + ((x / 10) as u8));
        out.push(b'0' + ((x % 10) as u8));
    } else if x >= 10 {
        out.push(b'0' + ((x / 10) as u8));
        out.push(b'0' + ((x % 10) as u8));
    } else {
        out.push(b'0' + (x as u8));
    }

    out
}
