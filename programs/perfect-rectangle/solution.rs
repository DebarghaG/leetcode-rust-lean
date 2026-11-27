pub fn is_rectangle_cover(rectangles: &[Vec<i64>]) -> bool {
    let n = rectangles.len();
    if n == 0 {
        return false;
    }

    let mut min_x = rectangles[0][0];
    let mut min_y = rectangles[0][1];
    let mut max_x = rectangles[0][2];
    let mut max_y = rectangles[0][3];

    let offset: i64 = 200000;
    let base: i64 = 1000000;

    let mut area_sum: i64 = 0;
    let mut corners: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let x1 = rectangles[i][0];
        let y1 = rectangles[i][1];
        let x2 = rectangles[i][2];
        let y2 = rectangles[i][3];

        if x1 < min_x {
            min_x = x1;
        }
        if y1 < min_y {
            min_y = y1;
        }
        if x2 > max_x {
            max_x = x2;
        }
        if y2 > max_y {
            max_y = y2;
        }

        area_sum += (x2 - x1) * (y2 - y1);

        let p1 = (x1 + offset) * base + (y1 + offset);
        let p2 = (x2 + offset) * base + (y1 + offset);
        let p3 = (x1 + offset) * base + (y2 + offset);
        let p4 = (x2 + offset) * base + (y2 + offset);

        corners.push(p1);
        corners.push(p2);
        corners.push(p3);
        corners.push(p4);

        i += 1;
    }

    let bounding_area = (max_x - min_x) * (max_y - min_y);
    if area_sum != bounding_area {
        return false;
    }

    // Manual insertion sort to avoid depending on std sorting internals.
    let m = corners.len();
    let mut a: usize = 0;
    while a < m {
        let mut b: usize = a;
        let mut going = b > 0;
        while going {
            if corners[b - 1] > corners[b] {
                let tmp = corners[b];
                corners[b] = corners[b - 1];
                corners[b - 1] = tmp;
                b -= 1;
                going = b > 0;
            } else {
                going = false;
            }
        }
        a += 1;
    }

    let g1 = (min_x + offset) * base + (min_y + offset);
    let g2 = (max_x + offset) * base + (min_y + offset);
    let g3 = (min_x + offset) * base + (max_y + offset);
    let g4 = (max_x + offset) * base + (max_y + offset);

    let mut seen1 = false;
    let mut seen2 = false;
    let mut seen3 = false;
    let mut seen4 = false;
    let mut ok = true;

    let mut idx: usize = 0;
    while idx < m {
        let key = corners[idx];
        let mut count: i64 = 0;
        let mut keep = true;
        while keep {
            if corners[idx] == key {
                count += 1;
                idx += 1;
                if idx >= m {
                    keep = false;
                }
            } else {
                keep = false;
            }
        }

        if key == g1 {
            seen1 = true;
            if count != 1 {
                ok = false;
            }
        } else if key == g2 {
            seen2 = true;
            if count != 1 {
                ok = false;
            }
        } else if key == g3 {
            seen3 = true;
            if count != 1 {
                ok = false;
            }
        } else if key == g4 {
            seen4 = true;
            if count != 1 {
                ok = false;
            }
        } else {
            if count % 2 != 0 {
                ok = false;
            }
        }
    }

    if !ok {
        return false;
    }

    seen1 && seen2 && seen3 && seen4
}
