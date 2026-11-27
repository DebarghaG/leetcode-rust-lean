pub fn max_bottles_drunk(numBottles: i64, numExchange: i64) -> i64 {
    let mut drunk = numBottles;
    let mut empty = numBottles;
    let mut exchange = numExchange;

    while empty >= exchange {
        empty = empty - exchange;
        empty = empty + 1;
        drunk = drunk + 1;
        exchange = exchange + 1;
    }

    drunk
}
