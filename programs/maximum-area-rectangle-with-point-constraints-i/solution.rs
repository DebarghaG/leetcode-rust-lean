pub fn max_rectangle_area(points: &[Vec<i64>]) -> i64 {
    let n = points.len();
    let mut best: i64 = -1;

    let mut i = 0usize;
    while i < n {
        let mut j = 0usize;
        while j < n {
            let xi = points[i][0];
            let yi = points[i][1];
            let xj = points[j][0];
            let yj = points[j][1];

            if xi < xj && yi < yj {
                let mut has_top_left = false;
                let mut has_bottom_right = false;

                let mut k = 0usize;
                while k < n {
                    let xk = points[k][0];
                    let yk = points[k][1];

                    if xk == xi && yk == yj {
                        has_top_left = true;
                    }
                    if xk == xj && yk == yi {
                        has_bottom_right = true;
                    }

                    k += 1;
                }

                if has_top_left && has_bottom_right {
                    let mut inside_count: i64 = 0;

                    let mut m = 0usize;
                    while m < n {
                        let xm = points[m][0];
                        let ym = points[m][1];

                        if xm >= xi && xm <= xj && ym >= yi && ym <= yj {
                            inside_count += 1;
                        }

                        m += 1;
                    }

                    if inside_count == 4 {
                        let area = (xj - xi) * (yj - yi);
                        if area > best {
                            best = area;
                        }
                    }
                }
            }

            j += 1;
        }

        i += 1;
    }

    best
}
