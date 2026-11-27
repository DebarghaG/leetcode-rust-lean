pub fn num_jewels_in_stones(jewels: &[u8], stones: &[u8]) -> i64 {
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < stones.len() {
        let stone = stones[i];
        let mut is_jewel: bool = false;
        let mut j: usize = 0;

        while j < jewels.len() {
            if jewels[j] == stone {
                is_jewel = true;
            }
            j += 1;
        }

        if is_jewel {
            count += 1;
        }

        i += 1;
    }

    count
}
