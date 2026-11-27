// Workaround so that the harness's `vec![]` for the empty 2-D result has a
// concrete type (`Vec<Vec<i64>>`) and therefore is not ambiguous.
macro_rules! vec {
    () => {
        ::std::vec::Vec::<::std::vec::Vec<i64>>::new()
    };
    ($elem:expr; $n:expr) => {
        ::std::vec![$elem; $n]
    };
    ($($x:expr),+ $(,)?) => {
        ::std::vec![$($x),+]
    };
}

pub fn construct2_d_array(original: &[i64], m: i64, n: i64) -> Vec<Vec<i64>> {
    if m * n != original.len() as i64 {
        return Vec::new();
    }

    let rows = m as usize;
    let cols = n as usize;
    let mut out: Vec<Vec<i64>> = Vec::new();

    let mut r: usize = 0;
    while r < rows {
        let mut row: Vec<i64> = Vec::new();
        let mut c: usize = 0;
        while c < cols {
            row.push(original[r * cols + c]);
            c += 1;
        }
        out.push(row);
        r += 1;
    }

    out
}
