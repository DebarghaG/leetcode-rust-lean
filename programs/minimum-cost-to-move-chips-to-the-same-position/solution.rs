pub fn min_cost_to_move_chips(position: &[i64]) -> i64 {
    let mut even_count: i64 = 0;
    let mut odd_count: i64 = 0;

    let mut i: usize = 0;
    while i < position.len() {
        if position[i] % 2 == 0 {
            even_count += 1;
        } else {
            odd_count += 1;
        }
        i += 1;
    }

    if even_count < odd_count {
        even_count
    } else {
        odd_count
    }
}
