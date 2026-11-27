pub fn count_days(days: i64, meetings: &[Vec<i64>]) -> i64 {
    let n = meetings.len();
    if n == 0 {
        return days;
    }

    let mut arr: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < n {
        let m = &meetings[i];
        let mut row: Vec<i64> = Vec::new();
        row.push(m[0]);
        row.push(m[1]);
        arr.push(row);
        i += 1;
    }

    arr.sort();

    let mut covered: i64 = 0;
    let mut cur_start: i64 = arr[0][0];
    let mut cur_end: i64 = arr[0][1];

    let mut j = 1;
    while j < arr.len() {
        let s = arr[j][0];
        let e = arr[j][1];

        if s <= cur_end + 1 {
            if e > cur_end {
                cur_end = e;
            }
        } else {
            covered += cur_end - cur_start + 1;
            cur_start = s;
            cur_end = e;
        }

        j += 1;
    }

    covered += cur_end - cur_start + 1;
    days - covered
}
