pub fn minimum_perimeter(neededApples: i64) -> i64 {
    let mut low: i64 = 0;
    let mut high: i64 = 1000000;

    while low < high {
        let mid: i64 = (low + high) / 2;
        let apples: i64 = 2 * mid * (mid + 1) * (2 * mid + 1);

        if apples >= neededApples {
            high = mid;
        } else {
            low = mid + 1;
        }
    }

    low * 8
}
