pub fn can_place_flowers(flowerbed: &[i64], n: i64) -> bool {
    let len = flowerbed.len();
    let mut planted: i64 = 0;
    let mut i: usize = 0;
    let mut prev: i64 = 0; // an empty plot just before the left edge

    while i < len {
        let cur: i64 = flowerbed[i];

        let mut next: i64 = 0; // an empty plot just past the right edge
        if i + 1 < len {
            next = flowerbed[i + 1];
        }

        if prev == 0 && cur == 0 && next == 0 {
            planted = planted + 1;
            prev = 1;
        } else {
            prev = cur;
        }

        i = i + 1;
    }

    if planted >= n {
        true
    } else {
        false
    }
}
