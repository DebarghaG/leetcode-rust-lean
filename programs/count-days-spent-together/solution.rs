fn days_before_month(month: i64) -> i64 {
    if month <= 1 {
        0
    } else if month == 2 {
        31
    } else if month == 3 {
        59
    } else if month == 4 {
        90
    } else if month == 5 {
        120
    } else if month == 6 {
        151
    } else if month == 7 {
        181
    } else if month == 8 {
        212
    } else if month == 9 {
        243
    } else if month == 10 {
        273
    } else if month == 11 {
        304
    } else {
        334
    }
}

fn day_of_year(date: &[u8]) -> i64 {
    let month_hi: i64 = date[0] as i64 - 48;
    let month_lo: i64 = date[1] as i64 - 48;
    let month: i64 = month_hi * 10 + month_lo;

    let day_hi: i64 = date[3] as i64 - 48;
    let day_lo: i64 = date[4] as i64 - 48;
    let day: i64 = day_hi * 10 + day_lo;

    days_before_month(month) + day - 1
}

pub fn count_days_together(
    arriveAlice: &[u8],
    leaveAlice: &[u8],
    arriveBob: &[u8],
    leaveBob: &[u8],
) -> i64 {
    let alice_arrive: i64 = day_of_year(arriveAlice);
    let alice_leave: i64 = day_of_year(leaveAlice);
    let bob_arrive: i64 = day_of_year(arriveBob);
    let bob_leave: i64 = day_of_year(leaveBob);

    let start: i64 = if alice_arrive > bob_arrive {
        alice_arrive
    } else {
        bob_arrive
    };

    let end: i64 = if alice_leave < bob_leave {
        alice_leave
    } else {
        bob_leave
    };

    if start > end {
        0
    } else {
        end - start + 1
    }
}
