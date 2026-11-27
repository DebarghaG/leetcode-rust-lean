pub fn group_the_people(groupSizes: &[i64]) -> Vec<Vec<i64>> {
    let n = groupSizes.len();

    let mut order: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let s = groupSizes[i];
        let mut seen: bool = false;
        let mut j: usize = 0;
        while j < order.len() {
            if order[j] == s {
                seen = true;
            }
            j += 1;
        }
        if !seen {
            order.push(s);
        }
        i += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut oi: usize = 0;
    while oi < order.len() {
        let size = order[oi];
        let mut pos: usize = 0;

        while pos < n {
            let mut group: Vec<i64> = Vec::new();
            let mut count: i64 = 0;

            while pos < n && count < size {
                if groupSizes[pos] == size {
                    group.push(pos as i64);
                    count += 1;
                }
                pos += 1;
            }

            if group.len() > 0 {
                out.push(group);
            }
        }

        oi += 1;
    }

    out
}
