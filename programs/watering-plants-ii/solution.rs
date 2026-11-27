pub fn minimum_refill(plants: &[i64], capacityA: i64, capacityB: i64) -> i64 {
    let n = plants.len();
    let mut left: usize = 0;
    let mut right: usize = n - 1;
    let mut water_a = capacityA;
    let mut water_b = capacityB;
    let mut refills: i64 = 0;

    while left < right {
        if water_a < plants[left] {
            refills += 1;
            water_a = capacityA;
        }
        water_a -= plants[left];
        left += 1;

        if water_b < plants[right] {
            refills += 1;
            water_b = capacityB;
        }
        water_b -= plants[right];
        right -= 1;
    }

    if left == right {
        if water_a >= water_b {
            if water_a < plants[left] {
                refills += 1;
            }
        } else {
            if water_b < plants[left] {
                refills += 1;
            }
        }
    }

    refills
}
