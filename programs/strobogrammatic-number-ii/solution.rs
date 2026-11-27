pub fn find_strobogrammatic(n: i64) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();

    let pairs: usize = (n / 2) as usize;
    let odd: bool = n % 2 == 1;

    // Total number of outputs, computed from the mixed-radix representation.
    let mut total: i64 = 1;
    let mut l: usize = 0;
    while l < pairs {
        if l + 1 == pairs {
            total = total * 4;
        } else {
            total = total * 5;
        }
        l = l + 1;
    }
    if odd {
        total = total * 3;
    }

    let mut k: i64 = 0;
    while k < total {
        let mut row: Vec<u8> = Vec::new();
        let mut q: i64 = k;

        // Build the left half from outermost to innermost.
        // The outermost pair has 4 choices: 1, 8, 6/9, 9/6.
        // Every inner pair also has the 0/0 choice, so 5 choices.
        let mut pos: usize = 0;
        while pos < pairs {
            let radix: i64 = if pos == 0 { 4 } else { 5 };
            let opt: i64 = q % radix;
            q = q / radix;

            if opt == 0 {
                row.push(b'1');
            } else if opt == 1 {
                row.push(b'8');
            } else if opt == 2 {
                row.push(b'6');
            } else if opt == 3 {
                row.push(b'9');
            } else {
                row.push(b'0');
            }

            pos = pos + 1;
        }

        // Optional middle digit for odd lengths.
        if odd {
            let mid_opt: i64 = q % 3;
            if mid_opt == 0 {
                row.push(b'0');
            } else if mid_opt == 1 {
                row.push(b'1');
            } else {
                row.push(b'8');
            }
        }

        // Mirror the left half, from innermost to outermost, to build the right half.
        let mut i: usize = pairs;
        while i > 0 {
            i = i - 1;
            let d: u8 = row[i];

            if d == b'0' {
                row.push(b'0');
            } else if d == b'1' {
                row.push(b'1');
            } else if d == b'6' {
                row.push(b'9');
            } else if d == b'8' {
                row.push(b'8');
            } else {
                row.push(b'6');
            }
        }

        out.push(row);
        k = k + 1;
    }

    out
}
