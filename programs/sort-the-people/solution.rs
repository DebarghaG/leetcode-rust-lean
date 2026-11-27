fn build_order(heights: &[i64]) -> Vec<i64> {
    let n: usize = heights.len();

    // Copy heights into an owned vec and build the identity index permutation.
    let mut h: Vec<i64> = Vec::new();
    let mut order: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        h.push(heights[i]);
        order.push(i as i64);
        i += 1;
    }

    // Selection sort: descending by height, moving the index permutation along.
    let mut a: usize = 0;
    while a < n {
        let mut maxpos: usize = a;
        let mut b: usize = a + 1;
        while b < n {
            if h[b] > h[maxpos] {
                maxpos = b;
            }
            b += 1;
        }

        let tmp_h: i64 = h[a];
        h[a] = h[maxpos];
        h[maxpos] = tmp_h;

        let tmp_o: i64 = order[a];
        order[a] = order[maxpos];
        order[maxpos] = tmp_o;

        a += 1;
    }

    order
}

fn copy_name(names: &[Vec<u8>], idx: usize) -> Vec<u8> {
    let row = &names[idx];
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < row.len() {
        out.push(row[i]);
        i += 1;
    }
    out
}

pub fn sort_people(names: &[Vec<u8>], heights: &[i64]) -> Vec<Vec<u8>> {
    let order: Vec<i64> = build_order(heights);
    let n: usize = order.len();

    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut p: usize = 0;
    while p < n {
        let idx: usize = order[p] as usize;
        result.push(copy_name(names, idx));
        p += 1;
    }

    result
}
