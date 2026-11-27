fn feasible(
    m: usize,
    count: i64,
    composition: &[Vec<i64>],
    stock: &[i64],
    cost: &[i64],
    budget: i64,
) -> bool {
    let n = stock.len();
    let mut j = 0;
    let mut spent: i64 = 0;

    while j < n {
        let need = composition[m][j] * count;
        if need > stock[j] {
            let buy = need - stock[j];
            spent = spent + buy * cost[j];
            if spent > budget {
                return false;
            }
        }
        j += 1;
    }

    true
}

pub fn max_number_of_alloys(
    n: i64,
    k: i64,
    budget: i64,
    composition: &[Vec<i64>],
    stock: &[i64],
    cost: &[i64],
) -> i64 {
    let _ = n;
    let _ = k;

    let machines = composition.len();

    let mut max_stock: i64 = 0;
    let mut i = 0;
    while i < stock.len() {
        if stock[i] > max_stock {
            max_stock = stock[i];
        }
        i += 1;
    }

    let high = max_stock + budget + 1;
    let mut answer: i64 = 0;
    let mut m = 0;

    while m < machines {
        let mut low: i64 = 0;
        let mut hi: i64 = high;

        while low < hi {
            let mid = low + (hi - low + 1) / 2;
            if feasible(m, mid, composition, stock, cost, budget) {
                low = mid;
            } else {
                hi = mid - 1;
            }
        }

        if low > answer {
            answer = low;
        }

        m += 1;
    }

    answer
}
