#[cfg(test)]
#[macro_export]
macro_rules! vec {
    () => {
        Vec::<Vec<i64>>::new()
    };
    ($($x:expr),+ $(,)?) => {{
        let mut v = Vec::new();
        $( v.push($x); )+
        v
    }};
}

pub fn interval_intersection(firstList: &[Vec<i64>], secondList: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let mut result: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < firstList.len() && j < secondList.len() {
        let a_start: i64 = firstList[i][0];
        let a_end: i64 = firstList[i][1];
        let b_start: i64 = secondList[j][0];
        let b_end: i64 = secondList[j][1];

        let start: i64 = if a_start > b_start { a_start } else { b_start };
        let end: i64 = if a_end < b_end { a_end } else { b_end };

        if start <= end {
            let mut interval: Vec<i64> = Vec::new();
            interval.push(start);
            interval.push(end);
            result.push(interval);
        }

        if a_end < b_end {
            i += 1;
        } else {
            j += 1;
        }
    }

    result
}
