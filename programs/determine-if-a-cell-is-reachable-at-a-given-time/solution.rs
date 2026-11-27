pub fn is_reachable_at_time(sx: i64, sy: i64, fx: i64, fy: i64, t: i64) -> bool {
    if sx == fx && sy == fy && t == 1 {
        return false;
    }

    let dx = if sx > fx { sx - fx } else { fx - sx };
    let dy = if sy > fy { sy - fy } else { fy - sy };

    let dist = if dx > dy { dx } else { dy };

    t >= dist
}
