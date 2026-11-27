pub fn number_of_ways(corridor: &[u8]) -> i64 {
    let n: usize = corridor.len();
    let mut total_seats: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if corridor[i] == b'S' {
            total_seats += 1;
        }
        i += 1;
    }

    if total_seats == 0 {
        return 0;
    }

    if total_seats % 2 != 0 {
        return 0;
    }

    if total_seats == 2 {
        return 1;
    }

    let modulo: i64 = 1000000007;
    let mut answer: i64 = 1;
    let mut seat_count: i64 = 0;
    let mut plants: i64 = 0;
    let mut j: usize = 0;

    while j < n {
        if corridor[j] == b'S' {
            seat_count += 1;

            if seat_count > 2 && seat_count % 2 == 1 {
                answer = (answer * ((plants + 1) % modulo)) % modulo;
                plants = 0;
            }
        } else {
            if seat_count >= 2 && seat_count % 2 == 0 {
                plants += 1;
            }
        }

        j += 1;
    }

    answer
}
