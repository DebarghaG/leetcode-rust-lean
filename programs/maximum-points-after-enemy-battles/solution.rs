pub fn maximum_points(enemyEnergies: &[i64], currentEnergy: i64) -> i64 {
    let n = enemyEnergies.len();
    if n == 0 {
        return 0;
    }

    let mut min_energy = enemyEnergies[0];
    let mut sum_energy: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let energy = enemyEnergies[i];
        sum_energy = sum_energy + energy;
        if energy < min_energy {
            min_energy = energy;
        }
        i = i + 1;
    }

    if currentEnergy < min_energy {
        return 0;
    }

    let total_energy = sum_energy + currentEnergy;
    (total_energy - min_energy) / min_energy
}
