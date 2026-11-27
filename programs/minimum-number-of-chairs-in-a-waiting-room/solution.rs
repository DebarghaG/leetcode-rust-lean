pub fn minimum_chairs(s: &[u8]) -> i64 {
    let mut current: i64 = 0;
    let mut max_people: i64 = 0;
    let mut i: usize = 0;

    while i < s.len() {
        if s[i] == b'E' {
            current += 1;
        } else {
            current -= 1;
        }

        if current > max_people {
            max_people = current;
        }

        i += 1;
    }

    max_people
}
