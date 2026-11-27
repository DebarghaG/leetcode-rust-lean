pub fn mem_leak(memory1: i64, memory2: i64) -> Vec<i64> {
    let mut m1 = memory1;
    let mut m2 = memory2;
    let mut time: i64 = 1;
    let mut crashed: bool = false;

    while !crashed {
        if m1 >= m2 {
            if m1 >= time {
                m1 -= time;
                time += 1;
            } else {
                crashed = true;
            }
        } else {
            if m2 >= time {
                m2 -= time;
                time += 1;
            } else {
                crashed = true;
            }
        }
    }

    let mut result: Vec<i64> = Vec::new();
    result.push(time);
    result.push(m1);
    result.push(m2);
    result
}
