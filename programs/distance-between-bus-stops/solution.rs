pub fn distance_between_bus_stops(distance: &[i64], start: i64, destination: i64) -> i64 {
    let n = distance.len();
    let s = start as usize;
    let d = destination as usize;

    let mut total: i64 = 0;
    let mut i = 0;
    while i < n {
        total += distance[i];
        i += 1;
    }

    let mut lo = s;
    let mut hi = d;
    if lo > hi {
        lo = d;
        hi = s;
    }

    let mut clockwise: i64 = 0;
    let mut j = lo;
    while j < hi {
        clockwise += distance[j];
        j += 1;
    }

    let counterclockwise = total - clockwise;

    if clockwise < counterclockwise {
        clockwise
    } else {
        counterclockwise
    }
}
