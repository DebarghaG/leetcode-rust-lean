pub fn max_energy_boost(energyDrinkA: &[i64], energyDrinkB: &[i64]) -> i64 {
    let n = energyDrinkA.len();
    if n == 0 {
        return 0;
    }
    if n == 1 {
        if energyDrinkA[0] > energyDrinkB[0] {
            return energyDrinkA[0];
        } else {
            return energyDrinkB[0];
        }
    }

    let mut a_im2: i64 = 0;
    let mut b_im2: i64 = 0;
    let mut a_im1: i64 = energyDrinkA[0];
    let mut b_im1: i64 = energyDrinkB[0];

    let mut i: usize = 1;
    while i < n {
        let best_a_prev = if a_im1 > b_im2 { a_im1 } else { b_im2 };
        let best_b_prev = if b_im1 > a_im2 { b_im1 } else { a_im2 };

        let a_cur = energyDrinkA[i] + best_a_prev;
        let b_cur = energyDrinkB[i] + best_b_prev;

        a_im2 = a_im1;
        b_im2 = b_im1;
        a_im1 = a_cur;
        b_im1 = b_cur;

        i += 1;
    }

    if a_im1 > b_im1 {
        a_im1
    } else {
        b_im1
    }
}
