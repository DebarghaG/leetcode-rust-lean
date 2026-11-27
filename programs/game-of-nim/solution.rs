pub fn nim_game(piles: &[i64]) -> bool {
    let mut xor_sum: i64 = 0;
    let mut i: usize = 0;
    while i < piles.len() {
        xor_sum = xor_sum ^ piles[i];
        i = i + 1;
    }
    xor_sum != 0
}
