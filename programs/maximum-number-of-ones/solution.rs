pub fn maximum_number_of_ones(width: i64, height: i64, sideLength: i64, maxOnes: i64) -> i64 {
    let s: usize = sideLength as usize;
    let mut counts: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < s {
        let row_count: i64 = (height - (i as i64) + sideLength - 1) / sideLength;

        let mut j: usize = 0;
        while j < s {
            let col_count: i64 = (width - (j as i64) + sideLength - 1) / sideLength;
            counts.push(row_count * col_count);
            j += 1;
        }

        i += 1;
    }

    let n: usize = counts.len();

    // Sort counts in nondecreasing order using a simple selection sort.
    let mut a: usize = 0;
    while a < n {
        let mut b: usize = a + 1;
        while b < n {
            if counts[b] < counts[a] {
                let tmp: i64 = counts[a];
                counts[a] = counts[b];
                counts[b] = tmp;
            }
            b += 1;
        }
        a += 1;
    }

    let mut answer: i64 = 0;
    let mut taken: usize = 0;
    let mut pos: usize = n;

    while taken < (maxOnes as usize) {
        pos -= 1;
        answer += counts[pos];
        taken += 1;
    }

    answer
}
