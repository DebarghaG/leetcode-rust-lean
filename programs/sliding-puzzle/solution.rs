fn pid3(a: i64, b: i64, c: i64) -> i64 {
    let mut o: i64 = 0;
    if a < b {
        if b < c {
            o = 0;
        } else if a < c {
            o = 1;
        } else {
            o = 2;
        }
    } else if a < c {
        o = 3;
    } else if b < c {
        o = 4;
    } else {
        o = 5;
    }
    o
}

// Dense index for a permutation code: the number c/216 keeps the three high
// digits, and pid3 tells the relative order of the three low digits (which is
// exactly the missing information), so this map is injective on codes.
fn cidx(c: i64) -> usize {
    let a: i64 = c % 6;
    let b: i64 = (c / 6) % 6;
    let e: i64 = (c / 36) % 6;
    let hi: i64 = c / 216;
    let o: i64 = pid3(a, b, e);
    (hi * 6 + o) as usize
}

pub fn sliding_puzzle(board: &[Vec<i64>]) -> i64 {
    let target: i64 = 7465;

    let b0: i64 = board[0][0];
    let b1: i64 = board[0][1];
    let b2: i64 = board[0][2];
    let b3: i64 = board[1][0];
    let b4: i64 = board[1][1];
    let b5: i64 = board[1][2];

    let start: i64 = b0 + b1 * 6 + b2 * 36 + b3 * 216 + b4 * 1296 + b5 * 7776;

    if start == target {
        return 0;
    }

    let mut zstart: i64 = 0;
    if b0 == 0 {
        zstart = 0;
    }
    if b1 == 0 {
        zstart = 1;
    }
    if b2 == 0 {
        zstart = 2;
    }
    if b3 == 0 {
        zstart = 3;
    }
    if b4 == 0 {
        zstart = 4;
    }
    if b5 == 0 {
        zstart = 5;
    }

    let mut dist: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 1296 {
        dist.push(-1);
        k = k + 1;
    }
    dist[cidx(start)] = 0;

    let mut q_code: Vec<i64> = Vec::new();
    let mut q_zero: Vec<i64> = Vec::new();
    q_code.push(start);
    q_zero.push(zstart);

    let mut ans: i64 = -1;
    let mut head: usize = 0;
    while head < q_code.len() {
        if ans == -1 {
            let code: i64 = q_code[head];
            let z: i64 = q_zero[head];
            let d: i64 = dist[cidx(code)];

            let p0: i64 = code % 6;
            let p1: i64 = (code / 6) % 6;
            let p2: i64 = (code / 36) % 6;
            let p3: i64 = (code / 216) % 6;
            let p4: i64 = (code / 1296) % 6;
            let p5: i64 = code / 7776;

            // edge (0,1)
            if z == 0 {
                let nc: i64 = code - 5 * p1;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(1);
                    }
                }
            } else if z == 1 {
                let nc: i64 = code + 5 * p0;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(0);
                    }
                }
            }

            // edge (0,3)
            if z == 0 {
                let nc: i64 = code - 215 * p3;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(3);
                    }
                }
            } else if z == 3 {
                let nc: i64 = code + 215 * p0;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(0);
                    }
                }
            }

            // edge (1,2)
            if z == 1 {
                let nc: i64 = code - 30 * p2;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(2);
                    }
                }
            } else if z == 2 {
                let nc: i64 = code + 30 * p1;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(1);
                    }
                }
            }

            // edge (1,4)
            if z == 1 {
                let nc: i64 = code - 1290 * p4;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(4);
                    }
                }
            } else if z == 4 {
                let nc: i64 = code + 1290 * p1;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(1);
                    }
                }
            }

            // edge (2,5)
            if z == 2 {
                let nc: i64 = code - 7740 * p5;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(5);
                    }
                }
            } else if z == 5 {
                let nc: i64 = code + 7740 * p2;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(2);
                    }
                }
            }

            // edge (3,4)
            if z == 3 {
                let nc: i64 = code - 1080 * p4;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(4);
                    }
                }
            } else if z == 4 {
                let nc: i64 = code + 1080 * p3;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(3);
                    }
                }
            }

            // edge (4,5)
            if z == 4 {
                let nc: i64 = code - 6480 * p5;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(5);
                    }
                }
            } else if z == 5 {
                let nc: i64 = code + 6480 * p4;
                if nc == target {
                    ans = d + 1;
                } else {
                    let ix: usize = cidx(nc);
                    if dist[ix] == -1 {
                        dist[ix] = d + 1;
                        q_code.push(nc);
                        q_zero.push(4);
                    }
                }
            }
        }
        head = head + 1;
    }

    ans
}
