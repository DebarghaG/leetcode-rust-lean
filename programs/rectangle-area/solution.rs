pub fn compute_area(
    ax1: i64,
    ay1: i64,
    ax2: i64,
    ay2: i64,
    bx1: i64,
    by1: i64,
    bx2: i64,
    by2: i64,
) -> i64 {
    let area_a = (ax2 - ax1) * (ay2 - ay1);
    let area_b = (bx2 - bx1) * (by2 - by1);

    let left = if ax1 > bx1 { ax1 } else { bx1 };
    let right = if ax2 < bx2 { ax2 } else { bx2 };
    let bottom = if ay1 > by1 { ay1 } else { by1 };
    let top = if ay2 < by2 { ay2 } else { by2 };

    let overlap_width = if right > left { right - left } else { 0 };
    let overlap_height = if top > bottom { top - bottom } else { 0 };
    let overlap_area = overlap_width * overlap_height;

    area_a + area_b - overlap_area
}
