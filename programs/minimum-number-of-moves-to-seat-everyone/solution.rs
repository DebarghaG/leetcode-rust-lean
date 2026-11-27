pub fn min_moves_to_seat(seats: &[i64], students: &[i64]) -> i64 {
    let mut sorted_seats: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < seats.len() {
        sorted_seats.push(seats[i]);
        i += 1;
    }

    let mut sorted_students: Vec<i64> = Vec::new();
    i = 0;
    while i < students.len() {
        sorted_students.push(students[i]);
        i += 1;
    }

    let mut a: usize = 1;
    while a < sorted_seats.len() {
        let key: i64 = sorted_seats[a];
        let mut b: usize = a;
        let mut moving: bool = true;
        while b > 0 && moving {
            if sorted_seats[b - 1] > key {
                sorted_seats[b] = sorted_seats[b - 1];
                b -= 1;
            } else {
                moving = false;
            }
        }
        sorted_seats[b] = key;
        a += 1;
    }

    a = 1;
    while a < sorted_students.len() {
        let key: i64 = sorted_students[a];
        let mut b: usize = a;
        let mut moving: bool = true;
        while b > 0 && moving {
            if sorted_students[b - 1] > key {
                sorted_students[b] = sorted_students[b - 1];
                b -= 1;
            } else {
                moving = false;
            }
        }
        sorted_students[b] = key;
        a += 1;
    }

    let mut ans: i64 = 0;
    i = 0;
    while i < sorted_seats.len() {
        let mut diff: i64 = sorted_seats[i] - sorted_students[i];
        if diff < 0 {
            diff = -diff;
        }
        ans += diff;
        i += 1;
    }

    ans
}
