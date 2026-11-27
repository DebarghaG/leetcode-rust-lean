pub fn unique_morse_representations(words: &[Vec<u8>]) -> i64 {
    let mut morse: Vec<Vec<u8>> = Vec::new();

    let mut c0: Vec<u8> = Vec::new();
    c0.push(b'.');
    c0.push(b'-');
    morse.push(c0);

    let mut c1: Vec<u8> = Vec::new();
    c1.push(b'-');
    c1.push(b'.');
    c1.push(b'.');
    c1.push(b'.');
    morse.push(c1);

    let mut c2: Vec<u8> = Vec::new();
    c2.push(b'-');
    c2.push(b'.');
    c2.push(b'-');
    c2.push(b'.');
    morse.push(c2);

    let mut c3: Vec<u8> = Vec::new();
    c3.push(b'-');
    c3.push(b'.');
    c3.push(b'.');
    morse.push(c3);

    let mut c4: Vec<u8> = Vec::new();
    c4.push(b'.');
    morse.push(c4);

    let mut c5: Vec<u8> = Vec::new();
    c5.push(b'.');
    c5.push(b'.');
    c5.push(b'-');
    c5.push(b'.');
    morse.push(c5);

    let mut c6: Vec<u8> = Vec::new();
    c6.push(b'-');
    c6.push(b'-');
    c6.push(b'.');
    morse.push(c6);

    let mut c7: Vec<u8> = Vec::new();
    c7.push(b'.');
    c7.push(b'.');
    c7.push(b'.');
    c7.push(b'.');
    morse.push(c7);

    let mut c8: Vec<u8> = Vec::new();
    c8.push(b'.');
    c8.push(b'.');
    morse.push(c8);

    let mut c9: Vec<u8> = Vec::new();
    c9.push(b'.');
    c9.push(b'-');
    c9.push(b'-');
    c9.push(b'-');
    morse.push(c9);

    let mut c10: Vec<u8> = Vec::new();
    c10.push(b'-');
    c10.push(b'.');
    c10.push(b'-');
    morse.push(c10);

    let mut c11: Vec<u8> = Vec::new();
    c11.push(b'.');
    c11.push(b'-');
    c11.push(b'.');
    c11.push(b'.');
    morse.push(c11);

    let mut c12: Vec<u8> = Vec::new();
    c12.push(b'-');
    c12.push(b'-');
    morse.push(c12);

    let mut c13: Vec<u8> = Vec::new();
    c13.push(b'-');
    c13.push(b'.');
    morse.push(c13);

    let mut c14: Vec<u8> = Vec::new();
    c14.push(b'-');
    c14.push(b'-');
    c14.push(b'-');
    morse.push(c14);

    let mut c15: Vec<u8> = Vec::new();
    c15.push(b'.');
    c15.push(b'-');
    c15.push(b'-');
    c15.push(b'.');
    morse.push(c15);

    let mut c16: Vec<u8> = Vec::new();
    c16.push(b'-');
    c16.push(b'-');
    c16.push(b'.');
    c16.push(b'-');
    morse.push(c16);

    let mut c17: Vec<u8> = Vec::new();
    c17.push(b'.');
    c17.push(b'-');
    c17.push(b'.');
    morse.push(c17);

    let mut c18: Vec<u8> = Vec::new();
    c18.push(b'.');
    c18.push(b'.');
    c18.push(b'.');
    morse.push(c18);

    let mut c19: Vec<u8> = Vec::new();
    c19.push(b'-');
    morse.push(c19);

    let mut c20: Vec<u8> = Vec::new();
    c20.push(b'.');
    c20.push(b'.');
    c20.push(b'-');
    morse.push(c20);

    let mut c21: Vec<u8> = Vec::new();
    c21.push(b'.');
    c21.push(b'.');
    c21.push(b'.');
    c21.push(b'-');
    morse.push(c21);

    let mut c22: Vec<u8> = Vec::new();
    c22.push(b'.');
    c22.push(b'-');
    c22.push(b'-');
    morse.push(c22);

    let mut c23: Vec<u8> = Vec::new();
    c23.push(b'-');
    c23.push(b'.');
    c23.push(b'.');
    c23.push(b'-');
    morse.push(c23);

    let mut c24: Vec<u8> = Vec::new();
    c24.push(b'-');
    c24.push(b'.');
    c24.push(b'-');
    c24.push(b'-');
    morse.push(c24);

    let mut c25: Vec<u8> = Vec::new();
    c25.push(b'-');
    c25.push(b'-');
    c25.push(b'.');
    c25.push(b'.');
    morse.push(c25);

    let mut seen: Vec<Vec<u8>> = Vec::new();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < words.len() {
        let word = &words[i];
        let mut transformed: Vec<u8> = Vec::new();

        let mut j: usize = 0;
        while j < word.len() {
            let idx: usize = (word[j] - b'a') as usize;
            let code_len: usize = morse[idx].len();
            let mut k: usize = 0;
            while k < code_len {
                transformed.push(morse[idx][k]);
                k = k + 1;
            }
            j = j + 1;
        }

        let mut found: bool = false;
        let mut s: usize = 0;
        while s < seen.len() {
            if seen[s].len() == transformed.len() {
                let mut same: bool = true;
                let mut p: usize = 0;
                while p < transformed.len() {
                    if seen[s][p] != transformed[p] {
                        same = false;
                    }
                    p = p + 1;
                }
                if same {
                    found = true;
                }
            }
            s = s + 1;
        }

        if !found {
            seen.push(transformed);
            count = count + 1;
        }

        i = i + 1;
    }

    count
}
