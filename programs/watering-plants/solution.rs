pub fn watering_plants(plants: &[i64], capacity: i64) -> i64 {
    let n = plants.len();
    let mut steps: i64 = 0;
    let mut water: i64 = capacity;
    let mut i: usize = 0;
    let mut pos: i64 = 0;

    while i < n {
        if water < plants[i] {
            steps = steps + 2 * pos;
            water = capacity;
        }

        steps = steps + 1;
        water = water - plants[i];

        i = i + 1;
        pos = pos + 1;
    }

    steps
}
