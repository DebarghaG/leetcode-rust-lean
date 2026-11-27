pub fn num_of_burgers(tomatoSlices: i64, cheeseSlices: i64) -> Vec<i64> {
    if tomatoSlices < 2 * cheeseSlices {
        return Vec::new();
    }
    if tomatoSlices > 4 * cheeseSlices {
        return Vec::new();
    }
    if tomatoSlices % 2 != 0 {
        return Vec::new();
    }

    let jumbo = (tomatoSlices - 2 * cheeseSlices) / 2;
    let small = cheeseSlices - jumbo;

    let mut result: Vec<i64> = Vec::new();
    result.push(jumbo);
    result.push(small);
    result
}
