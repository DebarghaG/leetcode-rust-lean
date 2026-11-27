#[allow(non_snake_case)]
pub fn max_containers(n: i64, w: i64, maxWeight: i64) -> i64 {
    let cells = n * n;
    let by_weight = maxWeight / w;

    if cells < by_weight {
        cells
    } else {
        by_weight
    }
}
