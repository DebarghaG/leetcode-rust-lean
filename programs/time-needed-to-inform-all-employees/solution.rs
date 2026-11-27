pub fn num_of_minutes(n: i64, headID: i64, manager: &[i64], informTime: &[i64]) -> i64 {
    let n_usize = n as usize;

    let mut children: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        let row: Vec<i64> = Vec::new();
        children.push(row);
        i += 1;
    }

    let mut emp: usize = 0;
    while emp < n_usize {
        let m = manager[emp];
        if m >= 0 {
            let mi = m as usize;
            children[mi].push(emp as i64);
        }
        emp += 1;
    }

    let mut nodes: Vec<i64> = Vec::new();
    let mut times: Vec<i64> = Vec::new();

    nodes.push(headID);
    times.push(0);

    let mut q: usize = 0;
    let mut answer: i64 = 0;

    while q < nodes.len() {
        let u = nodes[q];
        let current_time = times[q];
        q += 1;

        if current_time > answer {
            answer = current_time;
        }

        let u_usize = u as usize;
        let next_time = current_time + informTime[u_usize];

        let row = &children[u_usize];
        let mut j: usize = 0;
        while j < row.len() {
            nodes.push(row[j]);
            times.push(next_time);
            j += 1;
        }
    }

    answer
}
