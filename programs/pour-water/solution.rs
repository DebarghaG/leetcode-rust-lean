pub fn pour_water(heights: &[i64], volume: i64, k: i64) -> Vec<i64> {
    let n = heights.len();

    let mut water: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        water.push(heights[i]);
        i += 1;
    }

    let start = k as usize;
    let mut dropped: i64 = 0;

    while dropped < volume {
        let p = start;
        let cur = water[p];

        let mut l = p;
        while l > 0 && water[l - 1] <= water[l] {
            l -= 1;
        }
        let left_min = water[l];

        if left_min < cur {
            let mut j = l;
            while j < p && water[j + 1] == left_min {
                j += 1;
            }
            water[j] += 1;
        } else {
            let mut r = p;
            while r + 1 < n && water[r + 1] <= water[r] {
                r += 1;
            }
            let right_min = water[r];

            if right_min < cur {
                let mut j = r;
                while j > p && water[j - 1] == right_min {
                    j -= 1;
                }
                water[j] += 1;
            } else {
                water[p] += 1;
            }
        }

        dropped += 1;
    }

    water
}
