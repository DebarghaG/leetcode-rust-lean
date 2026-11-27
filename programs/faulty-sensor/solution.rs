pub fn bad_sensor(sensor1: &[i64], sensor2: &[i64]) -> i64 {
    let n = sensor1.len();
    let mut i: usize = 0;

    while i < n && sensor1[i] == sensor2[i] {
        i += 1;
    }

    if i == n {
        return -1;
    }

    let mut can1: bool = true;
    let mut can2: bool = true;
    let mut j: usize = i;

    while j + 1 < n {
        if sensor1[j] != sensor2[j + 1] {
            can1 = false;
        }
        if sensor2[j] != sensor1[j + 1] {
            can2 = false;
        }
        j += 1;
    }

    if can1 && can2 {
        return -1;
    }

    if can2 {
        return 2;
    }

    1
}
