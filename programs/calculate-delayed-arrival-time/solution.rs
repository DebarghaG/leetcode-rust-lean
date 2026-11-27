pub fn find_delayed_arrival_time(arrivalTime: i64, delayedTime: i64) -> i64 {
    (arrivalTime + delayedTime) % 24
}
