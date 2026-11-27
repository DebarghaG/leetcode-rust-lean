fn bit_count6(mut x: i64) -> i64 {
    let mut c: i64 = 0;

    if x >= 32 {
        c += 1;
        x -= 32;
    }
    if x >= 16 {
        c += 1;
        x -= 16;
    }
    if x >= 8 {
        c += 1;
        x -= 8;
    }
    if x >= 4 {
        c += 1;
        x -= 4;
    }
    if x >= 2 {
        c += 1;
        x -= 2;
    }
    if x >= 1 {
        c += 1;
    }

    c
}

fn digit(d: i64) -> u8 {
    if d == 0 {
        b'0'
    } else if d == 1 {
        b'1'
    } else if d == 2 {
        b'2'
    } else if d == 3 {
        b'3'
    } else if d == 4 {
        b'4'
    } else if d == 5 {
        b'5'
    } else if d == 6 {
        b'6'
    } else if d == 7 {
        b'7'
    } else if d == 8 {
        b'8'
    } else {
        b'9'
    }
}

fn format_time(h: i64, m: i64) -> Vec<u8> {
    let mut s: Vec<u8> = Vec::new();

    if h < 10 {
        s.push(digit(h));
    } else {
        s.push(b'1');
        if h == 10 {
            s.push(b'0');
        } else {
            s.push(b'1');
        }
    }

    s.push(b':');

    if m < 10 {
        s.push(b'0');
        s.push(digit(m));
    } else if m < 20 {
        s.push(b'1');
        s.push(digit(m - 10));
    } else if m < 30 {
        s.push(b'2');
        s.push(digit(m - 20));
    } else if m < 40 {
        s.push(b'3');
        s.push(digit(m - 30));
    } else if m < 50 {
        s.push(b'4');
        s.push(digit(m - 40));
    } else {
        s.push(b'5');
        s.push(digit(m - 50));
    }

    s
}

pub fn read_binary_watch(turnedOn: i64) -> Vec<Vec<u8>> {
    let mut mins0: Vec<i64> = Vec::new();
    let mut mins1: Vec<i64> = Vec::new();
    let mut mins2: Vec<i64> = Vec::new();
    let mut mins3: Vec<i64> = Vec::new();
    let mut mins4: Vec<i64> = Vec::new();
    let mut mins5: Vec<i64> = Vec::new();
    let mut mins6: Vec<i64> = Vec::new();

    let mut m: i64 = 0;
    while m < 60 {
        let c = bit_count6(m);

        if c == 0 {
            mins0.push(m);
        } else if c == 1 {
            mins1.push(m);
        } else if c == 2 {
            mins2.push(m);
        } else if c == 3 {
            mins3.push(m);
        } else if c == 4 {
            mins4.push(m);
        } else if c == 5 {
            mins5.push(m);
        } else {
            mins6.push(m);
        }

        m += 1;
    }

    let mut out: Vec<Vec<u8>> = Vec::new();

    let mut h: i64 = 0;
    while h < 12 {
        let target = turnedOn - bit_count6(h);

        if target == 0 {
            let mut i: usize = 0;
            while i < mins0.len() {
                out.push(format_time(h, mins0[i]));
                i += 1;
            }
        } else if target == 1 {
            let mut i: usize = 0;
            while i < mins1.len() {
                out.push(format_time(h, mins1[i]));
                i += 1;
            }
        } else if target == 2 {
            let mut i: usize = 0;
            while i < mins2.len() {
                out.push(format_time(h, mins2[i]));
                i += 1;
            }
        } else if target == 3 {
            let mut i: usize = 0;
            while i < mins3.len() {
                out.push(format_time(h, mins3[i]));
                i += 1;
            }
        } else if target == 4 {
            let mut i: usize = 0;
            while i < mins4.len() {
                out.push(format_time(h, mins4[i]));
                i += 1;
            }
        } else if target == 5 {
            let mut i: usize = 0;
            while i < mins5.len() {
                out.push(format_time(h, mins5[i]));
                i += 1;
            }
        } else if target == 6 {
            let mut i: usize = 0;
            while i < mins6.len() {
                out.push(format_time(h, mins6[i]));
                i += 1;
            }
        }

        h += 1;
    }

    out
}
