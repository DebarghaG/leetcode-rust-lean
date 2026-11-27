fn find(parent: &Vec<usize>, mut x: usize) -> usize {
    while parent[x] != x {
        x = parent[x];
    }
    x
}

fn link(parent: &Vec<usize>, child: usize, par: usize) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < parent.len() {
        if i == child {
            out.push(par);
        } else {
            out.push(parent[i]);
        }
        i += 1;
    }
    out
}

fn touches_vertical(x: i64, y: i64, r: i64, sx: i64, yc: i64) -> bool {
    let dx = if x > sx {
        x - sx
    } else if x < 0 {
        0 - x
    } else {
        sx - x
    };

    let dy = if y > yc {
        y - yc
    } else if y < 0 {
        0 - y
    } else {
        0
    };

    dx * dx + dy * dy <= r * r
}

fn touches_horizontal(x: i64, y: i64, r: i64, sy: i64, xc: i64) -> bool {
    let dy = if y > sy {
        y - sy
    } else if y < 0 {
        0 - y
    } else {
        sy - y
    };

    let dx = if x > xc {
        x - xc
    } else if x < 0 {
        0 - x
    } else {
        0
    };

    dx * dx + dy * dy <= r * r
}

fn pair_inside(
    x1: i64,
    y1: i64,
    r1: i64,
    x2: i64,
    y2: i64,
    r2: i64,
    xc: i64,
    yc: i64,
) -> bool {
    let dx = x1 - x2;
    let dy = y1 - y2;
    let sr = r1 + r2;

    if dx * dx + dy * dy > sr * sr {
        return false;
    }

    let nx = x1 * r2 + x2 * r1;
    let ny = y1 * r2 + y2 * r1;

    if nx > sr * xc {
        return false;
    }
    if ny > sr * yc {
        return false;
    }

    true
}

pub fn can_reach_corner(xCorner: i64, yCorner: i64, circles: &[Vec<i64>]) -> bool {
    let n = circles.len();
    let left_top = n;
    let right_bottom = n + 1;

    let mut parent: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < n + 2 {
        parent.push(k);
        k += 1;
    }

    let mut result: bool = true;

    // Phase 1: per-circle corner containment and boundary contact.
    let mut i: usize = 0;
    while i < n {
        let x = circles[i][0];
        let y = circles[i][1];
        let r = circles[i][2];

        if x * x + y * y <= r * r {
            result = false;
        }
        let ex = x - xCorner;
        let ey = y - yCorner;
        if ex * ex + ey * ey <= r * r {
            result = false;
        }

        let mut touches_left_top = false;
        let mut touches_right_bottom = false;

        if touches_vertical(x, y, r, 0, yCorner) {
            touches_left_top = true;
        }
        if touches_horizontal(x, y, r, yCorner, xCorner) {
            touches_left_top = true;
        }
        if touches_horizontal(x, y, r, 0, xCorner) {
            touches_right_bottom = true;
        }
        if touches_vertical(x, y, r, xCorner, yCorner) {
            touches_right_bottom = true;
        }

        if touches_left_top {
            let ri = find(&parent, i);
            let rb = find(&parent, left_top);
            if ri != rb {
                parent = link(&parent, ri, rb);
            }
        }

        if touches_right_bottom {
            let ri = find(&parent, i);
            let ra = find(&parent, right_bottom);
            if ri != ra {
                parent = link(&parent, ri, ra);
            }
        }

        if find(&parent, left_top) == find(&parent, right_bottom) {
            result = false;
        }

        i += 1;
    }

    // Phase 2: pairwise circle connections.
    let mut i: usize = 1;
    while i < n {
        let mut j: usize = 0;
        while j < i {
            let x1 = circles[i][0];
            let y1 = circles[i][1];
            let r1 = circles[i][2];

            let x2 = circles[j][0];
            let y2 = circles[j][1];
            let r2 = circles[j][2];

            if pair_inside(x1, y1, r1, x2, y2, r2, xCorner, yCorner) {
                let ri = find(&parent, i);
                let rj = find(&parent, j);
                if ri != rj {
                    parent = link(&parent, ri, rj);

                    if find(&parent, left_top) == find(&parent, right_bottom) {
                        result = false;
                    }
                }
            }

            j += 1;
        }
        i += 1;
    }

    result
}
