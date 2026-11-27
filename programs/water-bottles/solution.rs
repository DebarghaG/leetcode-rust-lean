pub fn num_water_bottles(numBottles: i64, numExchange: i64) -> i64 {
    let mut total = numBottles;
    let mut empty = numBottles;

    while empty >= numExchange {
        let new_full = empty / numExchange;
        total = total + new_full;
        empty = (empty % numExchange) + new_full;
    }

    total
}
