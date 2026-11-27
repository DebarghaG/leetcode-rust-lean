pub fn time_taken(arrival: &[i64], state: &[i64]) -> Vec<i64> {
    let n = arrival.len();

    let mut answer: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        answer.push(0);
        i += 1;
    }

    if n == 0 {
        return answer;
    }

    let mut next_enter: usize = 0;
    while next_enter < n {
        if state[next_enter] == 0 {
            break;
        }
        next_enter += 1;
    }

    let mut next_exit: usize = 0;
    while next_exit < n {
        if state[next_exit] == 1 {
            break;
        }
        next_exit += 1;
    }

    let mut t: i64 = 0;
    let mut last_used: i64 = -1; // -1: not used, 0: entering, 1: exiting
    let mut served: usize = 0;

    while served < n {
        let mut enter_available: bool = false;
        if next_enter < n {
            if arrival[next_enter] <= t {
                enter_available = true;
            }
        }

        let mut exit_available: bool = false;
        if next_exit < n {
            if arrival[next_exit] <= t {
                exit_available = true;
            }
        }

        if !enter_available && !exit_available {
            last_used = -1;
            t += 1;
        } else {
            let mut choose_enter: bool = false;

            if enter_available && exit_available {
                if last_used == 0 {
                    choose_enter = true;
                }
            } else if enter_available {
                choose_enter = true;
            }

            if choose_enter {
                let idx = next_enter;
                answer[idx] = t;
                last_used = 0;
                served += 1;

                next_enter += 1;
                while next_enter < n {
                    if state[next_enter] == 0 {
                        break;
                    }
                    next_enter += 1;
                }
            } else {
                let idx = next_exit;
                answer[idx] = t;
                last_used = 1;
                served += 1;

                next_exit += 1;
                while next_exit < n {
                    if state[next_exit] == 1 {
                        break;
                    }
                    next_exit += 1;
                }
            }

            t += 1;
        }
    }

    answer
}
