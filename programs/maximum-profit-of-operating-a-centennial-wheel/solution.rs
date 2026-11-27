pub fn min_operations_max_profit(customers: &[i64], boardingCost: i64, runningCost: i64) -> i64 {
    let n: usize = customers.len();
    let mut i: usize = 0;
    let mut waiting: i64 = 0;
    let mut profit: i64 = 0;
    let mut max_profit: i64 = 0;
    let mut best: i64 = -1;
    let mut rotations: i64 = 0;

    while i < n || waiting > 0 {
        if i < n {
            waiting = waiting + customers[i];
            i = i + 1;
        }

        let mut board: i64 = 0;
        if waiting >= 4 {
            board = 4;
        } else {
            board = waiting;
        }

        waiting = waiting - board;
        rotations = rotations + 1;
        profit = profit + board * boardingCost - runningCost;

        if profit > max_profit {
            max_profit = profit;
            best = rotations;
        }
    }

    best
}
