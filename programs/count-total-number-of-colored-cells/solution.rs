pub fn colored_cells(n: i64) -> i64 {
    let rings = n - 1;
    1 + 2 * n * rings
}
