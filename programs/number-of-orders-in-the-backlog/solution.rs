fn heap_push_min(keys: &mut Vec<i64>, amounts: &mut Vec<i64>, key: i64, amount: i64) {
    keys.push(key);
    amounts.push(amount);

    let mut i = keys.len() - 1;
    while i > 0 {
        let parent = (i - 1) / 2;
        if keys[parent] <= keys[i] {
            break;
        }

        let tmp_key = keys[i];
        keys[i] = keys[parent];
        keys[parent] = tmp_key;

        let tmp_amount = amounts[i];
        amounts[i] = amounts[parent];
        amounts[parent] = tmp_amount;

        i = parent;
    }
}

fn heap_pop_min(keys: &mut Vec<i64>, amounts: &mut Vec<i64>) {
    let n = keys.len();
    if n == 0 {
        return;
    }

    if n > 1 {
        keys[0] = keys[n - 1];
        amounts[0] = amounts[n - 1];
    }

    keys.pop();
    amounts.pop();

    let m = keys.len();
    if m == 0 {
        return;
    }

    let mut i = 0;
    while i < m {
        let left = 2 * i + 1;
        if left >= m {
            break;
        }

        let mut child = left;
        let right = left + 1;
        if right < m && keys[right] < keys[child] {
            child = right;
        }

        if keys[child] < keys[i] {
            let tmp_key = keys[i];
            keys[i] = keys[child];
            keys[child] = tmp_key;

            let tmp_amount = amounts[i];
            amounts[i] = amounts[child];
            amounts[child] = tmp_amount;

            i = child;
        } else {
            break;
        }
    }
}

pub fn get_number_of_backlog_orders(orders: &[Vec<i64>]) -> i64 {
    let mut buy_keys: Vec<i64> = Vec::new();
    let mut buy_amounts: Vec<i64> = Vec::new();
    let mut sell_keys: Vec<i64> = Vec::new();
    let mut sell_amounts: Vec<i64> = Vec::new();

    let mut idx = 0;
    while idx < orders.len() {
        let price = orders[idx][0];
        let mut amount = orders[idx][1];
        let order_type = orders[idx][2];

        if order_type == 0 {
            while amount > 0 {
                if sell_keys.len() == 0 {
                    break;
                }
                if sell_keys[0] > price {
                    break;
                }

                let sell_amount = sell_amounts[0];
                if amount >= sell_amount {
                    amount -= sell_amount;
                    heap_pop_min(&mut sell_keys, &mut sell_amounts);
                } else {
                    sell_amounts[0] = sell_amount - amount;
                    amount = 0;
                }
            }

            if amount > 0 {
                heap_push_min(&mut buy_keys, &mut buy_amounts, -price, amount);
            }
        } else {
            while amount > 0 {
                if buy_keys.len() == 0 {
                    break;
                }

                let buy_price = -buy_keys[0];
                if buy_price < price {
                    break;
                }

                let buy_amount = buy_amounts[0];
                if amount >= buy_amount {
                    amount -= buy_amount;
                    heap_pop_min(&mut buy_keys, &mut buy_amounts);
                } else {
                    buy_amounts[0] = buy_amount - amount;
                    amount = 0;
                }
            }

            if amount > 0 {
                heap_push_min(&mut sell_keys, &mut sell_amounts, price, amount);
            }
        }

        idx += 1;
    }

    let mut total: i64 = 0;
    let mut i = 0;
    while i < buy_amounts.len() {
        total = (total + buy_amounts[i]) % 1000000007;
        i += 1;
    }

    i = 0;
    while i < sell_amounts.len() {
        total = (total + sell_amounts[i]) % 1000000007;
        i += 1;
    }

    total
}
