pub fn k_items_with_maximum_sum(numOnes: i64, numZeros: i64, numNegOnes: i64, k: i64) -> i64 {
    let mut remaining = k;
    let mut total = 0i64;

    let take_ones = if remaining < numOnes { remaining } else { numOnes };
    total += take_ones;
    remaining -= take_ones;

    let take_zeros = if remaining < numZeros { remaining } else { numZeros };
    remaining -= take_zeros;

    let take_neg_ones = if remaining < numNegOnes { remaining } else { numNegOnes };
    total -= take_neg_ones;

    total
}
