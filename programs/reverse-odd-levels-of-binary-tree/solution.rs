fn collect(t: &Tree, depth: usize, levels: &mut Vec<Vec<i64>>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            while levels.len() <= depth {
                levels.push(Vec::new());
            }
            levels[depth].push(*v);
            collect(&**l, depth + 1, levels);
            collect(&**r, depth + 1, levels);
        }
    }
}

fn rebuild(
    t: &Tree,
    depth: usize,
    levels: &Vec<Vec<i64>>,
    cursors: &mut Vec<usize>,
) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(_v, l, r) => {
            while cursors.len() <= depth {
                cursors.push(0);
            }
            let idx = cursors[depth];
            let val = levels[depth][idx];
            cursors[depth] = idx + 1;

            let lt = rebuild(&**l, depth + 1, levels, cursors);
            let rt = rebuild(&**r, depth + 1, levels, cursors);

            Tree::Node(val, Box::new(lt), Box::new(rt))
        }
    }
}

pub fn reverse_odd_levels(root: &Tree) -> Tree {
    let mut levels: Vec<Vec<i64>> = Vec::new();
    collect(root, 0, &mut levels);

    let mut d: usize = 0;
    while d < levels.len() {
        if d % 2 == 1 {
            let m = levels[d].len();
            let mut i: usize = 0;
            while i < m / 2 {
                let j = m - 1 - i;
                let a = levels[d][i];
                let b = levels[d][j];
                levels[d][i] = b;
                levels[d][j] = a;
                i += 1;
            }
        }
        d += 1;
    }

    let mut cursors: Vec<usize> = Vec::new();
    rebuild(root, 0, &levels, &mut cursors)
}
