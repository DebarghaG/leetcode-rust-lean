pub fn distance_traveled(mainTank: i64, additionalTank: i64) -> i64 {
    let mut main_fuel: i64 = mainTank;
    let mut add_fuel: i64 = additionalTank;
    let mut consumed_in_cycle: i64 = 0;
    let mut distance: i64 = 0;

    while main_fuel > 0 {
        main_fuel = main_fuel - 1;
        consumed_in_cycle = consumed_in_cycle + 1;
        distance = distance + 10;

        if consumed_in_cycle == 5 {
            if add_fuel >= 1 {
                add_fuel = add_fuel - 1;
                main_fuel = main_fuel + 1;
            }
            consumed_in_cycle = 0;
        }
    }

    distance
}
