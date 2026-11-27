pub fn minimum_health(damage: &[i64], armor: i64) -> i64 {
    let mut total: i64 = 0;
    let mut max_damage: i64 = 0;

    let n = damage.len();
    let mut i: usize = 0;
    while i < n {
        let d = damage[i];
        total += d;
        if d > max_damage {
            max_damage = d;
        }
        i += 1;
    }

    let protected = if max_damage < armor {
        max_damage
    } else {
        armor
    };

    total - protected + 1
}
