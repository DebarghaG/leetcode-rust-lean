pub fn is_same_after_reversals(num: i64) -> bool {
    if num == 0 {
        return true;
    }
    num % 10 != 0
}
