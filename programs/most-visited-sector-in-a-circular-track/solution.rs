pub fn most_visited(n: i64, rounds: &[i64]) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();

    if rounds.len() == 0 {
        return out;
    }

    let start = rounds[0];
    let end = rounds[rounds.len() - 1];

    if start <= end {
        let mut sector = start;
        while sector <= end {
            out.push(sector);
            sector += 1;
        }
    } else {
        let mut sector = 1;
        while sector <= end {
            out.push(sector);
            sector += 1;
        }

        let mut sector2 = start;
        while sector2 <= n {
            out.push(sector2);
            sector2 += 1;
        }
    }

    out
}
