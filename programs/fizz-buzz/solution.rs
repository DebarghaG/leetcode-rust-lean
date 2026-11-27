pub fn fizz_buzz(n: i64) -> Vec<Vec<u8>> {
    let mut answer: Vec<Vec<u8>> = Vec::new();
    let mut i: i64 = 1;

    while i <= n {
        let mut row: Vec<u8> = Vec::new();

        if i % 15 == 0 {
            row.push(b'F');
            row.push(b'i');
            row.push(b'z');
            row.push(b'z');
            row.push(b'B');
            row.push(b'u');
            row.push(b'z');
            row.push(b'z');
        } else if i % 3 == 0 {
            row.push(b'F');
            row.push(b'i');
            row.push(b'z');
            row.push(b'z');
        } else if i % 5 == 0 {
            row.push(b'B');
            row.push(b'u');
            row.push(b'z');
            row.push(b'z');
        } else {
            if i < 10 {
                row.push(48u8 + (i as u8));
            } else if i < 100 {
                let tens = i / 10;
                let ones = i % 10;
                row.push(48u8 + (tens as u8));
                row.push(48u8 + (ones as u8));
            } else {
                let hundreds = i / 100;
                let rem = i % 100;
                let tens = rem / 10;
                let ones = rem % 10;
                row.push(48u8 + (hundreds as u8));
                row.push(48u8 + (tens as u8));
                row.push(48u8 + (ones as u8));
            }
        }

        answer.push(row);
        i += 1;
    }

    answer
}
