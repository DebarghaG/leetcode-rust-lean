fn get_colors(edges: &[Vec<i64>]) -> Vec<i64> {
    let n: usize = edges.len() + 1;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    i = 0;
    while i < edges.len() {
        let u = edges[i][0] as usize;
        let v = edges[i][1] as usize;
        adj[u].push(v as i64);
        adj[v].push(u as i64);
        i += 1;
    }

    let mut colors: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        colors.push(-1);
        i += 1;
    }

    colors[0] = 0;

    let mut queue: Vec<i64> = Vec::new();
    queue.push(0);

    let mut head: usize = 0;
    while head < queue.len() {
        let u = queue[head] as usize;
        head += 1;

        let mut j: usize = 0;
        while j < adj[u].len() {
            let v = adj[u][j] as usize;
            if colors[v] == -1 {
                colors[v] = 1 - colors[u];
                queue.push(v as i64);
            }
            j += 1;
        }
    }

    colors
}

pub fn max_target_nodes(edges1: &[Vec<i64>], edges2: &[Vec<i64>]) -> Vec<i64> {
    let colors1 = get_colors(edges1);
    let colors2 = get_colors(edges2);

    let mut cnt10: i64 = 0;
    let mut cnt11: i64 = 0;

    let mut i: usize = 0;
    while i < colors1.len() {
        if colors1[i] == 0 {
            cnt10 += 1;
        } else {
            cnt11 += 1;
        }
        i += 1;
    }

    let mut cnt20: i64 = 0;
    let mut cnt21: i64 = 0;

    i = 0;
    while i < colors2.len() {
        if colors2[i] == 0 {
            cnt20 += 1;
        } else {
            cnt21 += 1;
        }
        i += 1;
    }

    let best2: i64 = if cnt20 > cnt21 { cnt20 } else { cnt21 };

    let mut answer: Vec<i64> = Vec::new();

    i = 0;
    while i < colors1.len() {
        let same_color_count: i64 = if colors1[i] == 0 { cnt10 } else { cnt11 };
        answer.push(same_color_count + best2);
        i += 1;
    }

    answer
}
