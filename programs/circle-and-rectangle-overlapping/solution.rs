pub fn check_overlap(radius: i64, xCenter: i64, yCenter: i64, x1: i64, y1: i64, x2: i64, y2: i64) -> bool {
    let mut closest_x = xCenter;
    if closest_x < x1 {
        closest_x = x1;
    }
    if closest_x > x2 {
        closest_x = x2;
    }

    let mut closest_y = yCenter;
    if closest_y < y1 {
        closest_y = y1;
    }
    if closest_y > y2 {
        closest_y = y2;
    }

    let dx = xCenter - closest_x;
    let dy = yCenter - closest_y;

    dx * dx + dy * dy <= radius * radius
}
