pub fn max_students_on_bench(students: &[Vec<i64>]) -> i64 {
    let n = students.len();
    if n == 0 {
        return 0;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut k = 0;
    while k < 101 {
        counts.push(0);
        k += 1;
    }

    let mut i = 0;
    while i < n {
        let student_id = students[i][0];
        let bench_id = students[i][1];

        let mut unique = true;
        let mut j = 0;
        while j < i {
            if students[j][0] == student_id && students[j][1] == bench_id {
                unique = false;
            }
            j += 1;
        }

        if unique {
            let idx = bench_id as usize;
            counts[idx] = counts[idx] + 1;
        }

        i += 1;
    }

    let mut best = 0;
    let mut b = 0;
    while b < counts.len() {
        if counts[b] > best {
            best = counts[b];
        }
        b += 1;
    }

    best
}
