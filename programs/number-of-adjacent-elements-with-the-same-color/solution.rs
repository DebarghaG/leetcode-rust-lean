pub fn color_the_array(n: i64, queries: &[Vec<i64>]) -> Vec<i64> {
    let n_usize = n as usize;

    let mut colors: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        colors.push(0);
        i += 1;
    }

    let mut answer: Vec<i64> = Vec::new();
    let mut count: i64 = 0;

    let mut qi: usize = 0;
    while qi < queries.len() {
        let query = &queries[qi];
        let idx = query[0] as usize;
        let new_color = query[1];
        let old_color = colors[idx];

        if old_color != new_color {
            if old_color != 0 {
                if idx > 0 {
                    if colors[idx - 1] == old_color {
                        count -= 1;
                    }
                }
                if idx + 1 < n_usize {
                    if colors[idx + 1] == old_color {
                        count -= 1;
                    }
                }
            }

            colors[idx] = new_color;

            if new_color != 0 {
                if idx > 0 {
                    if colors[idx - 1] == new_color {
                        count += 1;
                    }
                }
                if idx + 1 < n_usize {
                    if colors[idx + 1] == new_color {
                        count += 1;
                    }
                }
            }
        }

        answer.push(count);
        qi += 1;
    }

    answer
}
