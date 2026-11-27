pub fn lemonade_change(bills: &[i64]) -> bool {
    let mut fives: i64 = 0;
    let mut tens: i64 = 0;
    let mut i: usize = 0;

    while i < bills.len() {
        let bill = bills[i];

        if bill == 5 {
            fives += 1;
        } else if bill == 10 {
            if fives == 0 {
                return false;
            }
            fives -= 1;
            tens += 1;
        } else {
            if tens > 0 && fives > 0 {
                tens -= 1;
                fives -= 1;
            } else if fives >= 3 {
                fives -= 3;
            } else {
                return false;
            }
        }

        i += 1;
    }

    true
}
