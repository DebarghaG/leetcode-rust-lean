fn build(t: &Tree, lefts: &mut Vec<i64>, rights: &mut Vec<i64>) -> i64 {
    match t {
        Tree::Null => -1,
        Tree::Node(_, l, r) => {
            let idx = lefts.len() as i64;
            lefts.push(-1);
            rights.push(-1);
            let li = build(&**l, lefts, rights);
            let ri = build(&**r, lefts, rights);
            lefts[idx as usize] = li;
            rights[idx as usize] = ri;
            idx
        }
    }
}

pub fn min_camera_cover(root: &Tree) -> i64 {
    let mut lefts: Vec<i64> = Vec::new();
    let mut rights: Vec<i64> = Vec::new();
    build(root, &mut lefts, &mut rights);

    let n = lefts.len();
    if n == 0 {
        return 0;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut states: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        counts.push(0);
        states.push(0);
        i = i + 1;
    }

    let mut k = n;
    while k > 0 {
        k = k - 1;
        let li = lefts[k];
        let ri = rights[k];

        let mut ls = 1;
        let mut lc = 0;
        if li >= 0 {
            ls = states[li as usize];
            lc = counts[li as usize];
        }

        let mut rs = 1;
        let mut rc = 0;
        if ri >= 0 {
            rs = states[ri as usize];
            rc = counts[ri as usize];
        }

        let mut c = lc + rc;
        let mut st = 0;
        if ls == 0 {
            st = 2;
        } else if rs == 0 {
            st = 2;
        } else if ls == 2 {
            st = 1;
        } else if rs == 2 {
            st = 1;
        } else {
            st = 0;
        }
        if st == 2 {
            c = c + 1;
        }

        counts[k] = c;
        states[k] = st;
    }

    let root_state = states[0];
    let root_count = counts[0];
    if root_state == 0 {
        root_count + 1
    } else {
        root_count
    }
}
