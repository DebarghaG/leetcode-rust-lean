pub fn minimum_recolors(blocks: &[u8], k: i64) -> i64 {
    let n = blocks.len();
    let kk = k as usize;

    let mut whites: i64 = 0;
    let mut i: usize = 0;
    while i < kk {
        if blocks[i] == b'W' {
            whites += 1;
        }
        i += 1;
    }

    let mut best: i64 = whites;
    let mut start: usize = 1;
    while start + kk <= n {
        if blocks[start - 1] == b'W' {
            whites -= 1;
        }
        if blocks[start + kk - 1] == b'W' {
            whites += 1;
        }
        if whites < best {
            best = whites;
        }
        start += 1;
    }

    best
}
