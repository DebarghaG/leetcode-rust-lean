pub fn str2tree(s: &[u8]) -> Tree {
    let n = s.len();
    if n == 0 {
        return Tree::Null;
    }

    let mut i: usize = 0;
    let mut sign: i64 = 1;
    if s[i] == b'-' {
        sign = -1;
        i += 1;
    }
    let mut root_val: i64 = 0;
    while i < n && s[i] >= b'0' && s[i] <= b'9' {
        root_val = root_val * 10 + ((s[i] - b'0') as i64);
        i += 1;
    }
    root_val = sign * root_val;

    let mut vals: Vec<i64> = Vec::new();
    let mut lefts: Vec<Tree> = Vec::new();
    let mut rights: Vec<Tree> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();

    vals.push(root_val);
    lefts.push(Tree::Null);
    rights.push(Tree::Null);
    counts.push(0);

    while i < n {
        if s[i] == b'(' {
            i += 1;
            if i < n && s[i] == b')' {
                let p = vals.len() - 1;
                if counts[p] == 0 {
                    lefts[p] = Tree::Null;
                } else if counts[p] == 1 {
                    rights[p] = Tree::Null;
                }
                counts[p] += 1;
                i += 1;
            } else {
                let mut child_sign: i64 = 1;
                if i < n && s[i] == b'-' {
                    child_sign = -1;
                    i += 1;
                }
                let mut child_val: i64 = 0;
                while i < n && s[i] >= b'0' && s[i] <= b'9' {
                    child_val = child_val * 10 + ((s[i] - b'0') as i64);
                    i += 1;
                }
                child_val = child_sign * child_val;

                vals.push(child_val);
                lefts.push(Tree::Null);
                rights.push(Tree::Null);
                counts.push(0);
            }
        } else if s[i] == b')' {
            if vals.len() > 1 {
                let child_val = match vals.pop() {
                    Some(x) => x,
                    None => 0,
                };
                let child_left = match lefts.pop() {
                    Some(x) => x,
                    None => Tree::Null,
                };
                let child_right = match rights.pop() {
                    Some(x) => x,
                    None => Tree::Null,
                };
                let _child_count = match counts.pop() {
                    Some(x) => x,
                    None => 0,
                };

                let child = Tree::Node(child_val, Box::new(child_left), Box::new(child_right));

                let p = vals.len() - 1;
                if counts[p] == 0 {
                    lefts[p] = child;
                } else if counts[p] == 1 {
                    rights[p] = child;
                }
                counts[p] += 1;
            }
            i += 1;
        } else {
            i += 1;
        }
    }

    while vals.len() > 1 {
        vals.pop();
        lefts.pop();
        rights.pop();
        counts.pop();
    }

    let final_val = match vals.pop() {
        Some(x) => x,
        None => 0,
    };
    let final_left = match lefts.pop() {
        Some(x) => x,
        None => Tree::Null,
    };
    let final_right = match rights.pop() {
        Some(x) => x,
        None => Tree::Null,
    };

    Tree::Node(final_val, Box::new(final_left), Box::new(final_right))
}
