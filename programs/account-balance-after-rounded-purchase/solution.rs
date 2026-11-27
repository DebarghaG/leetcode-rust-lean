pub fn account_balance_after_purchase(purchaseAmount: i64) -> i64 {
    let roundedAmount = ((purchaseAmount + 5) / 10) * 10;
    100 - roundedAmount
}
