fn inorder(t: &Tree, out: &mut Vec<i64>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, left, right) => {
            inorder(left, out);
            out.push(*v);
            inorder(right, out);
        }
    }
}

pub fn get_all_elements(root1: &Tree, root2: &Tree) -> Vec<i64> {
    let mut a: Vec<i64> = Vec::new();
    let mut b: Vec<i64> = Vec::new();

    inorder(root1, &mut a);
    inorder(root2, &mut b);

    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < a.len() && j < b.len() {
        if a[i] <= b[j] {
            result.push(a[i]);
            i = i + 1;
        } else {
            result.push(b[j]);
            j = j + 1;
        }
    }

    while i < a.len() {
        result.push(a[i]);
        i = i + 1;
    }

    while j < b.len() {
        result.push(b[j]);
        j = j + 1;
    }

    result
}
