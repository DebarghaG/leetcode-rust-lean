fn lower_byte(b: u8) -> u8 {
    if b >= b'A' && b <= b'Z' {
        b + 32
    } else {
        b
    }
}

fn is_vowel(b: u8) -> bool {
    b == b'a' || b == b'e' || b == b'i' || b == b'o' || b == b'u'
}

pub fn spellchecker(wordlist: &[Vec<u8>], queries: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut answer: Vec<Vec<u8>> = Vec::new();
    let wn = wordlist.len();
    let qn = queries.len();

    let mut qi: usize = 0;
    while qi < qn {
        let qlen = queries[qi].len();

        let mut exact_index: usize = wn;
        let mut lower_index: usize = wn;

        let mut j: usize = 0;
        while j < wn && exact_index == wn {
            if wordlist[j].len() == qlen {
                let mut ok_exact: bool = true;
                let mut k: usize = 0;
                while k < qlen && ok_exact {
                    if wordlist[j][k] != queries[qi][k] {
                        ok_exact = false;
                    }
                    k += 1;
                }

                if ok_exact {
                    exact_index = j;
                } else {
                    let mut ok_lower: bool = true;
                    k = 0;
                    while k < qlen && ok_lower {
                        if lower_byte(wordlist[j][k]) != lower_byte(queries[qi][k]) {
                            ok_lower = false;
                        }
                        k += 1;
                    }
                    if ok_lower && lower_index == wn {
                        lower_index = j;
                    }
                }
            }
            j += 1;
        }

        let mut selected: usize = wn;
        if exact_index < wn {
            selected = exact_index;
        } else if lower_index < wn {
            selected = lower_index;
        } else {
            j = 0;
            while j < wn && selected == wn {
                if wordlist[j].len() == qlen {
                    let mut ok_vowel: bool = true;
                    let mut k: usize = 0;
                    while k < qlen && ok_vowel {
                        let wb = lower_byte(wordlist[j][k]);
                        let qb = lower_byte(queries[qi][k]);
                        let wv = is_vowel(wb);
                        let qv = is_vowel(qb);

                        if wv != qv {
                            ok_vowel = false;
                        } else if !wv && wb != qb {
                            ok_vowel = false;
                        }
                        k += 1;
                    }
                    if ok_vowel {
                        selected = j;
                    }
                }
                j += 1;
            }
        }

        let mut out_word: Vec<u8> = Vec::new();
        if selected < wn {
            let mut k: usize = 0;
            while k < wordlist[selected].len() {
                out_word.push(wordlist[selected][k]);
                k += 1;
            }
        }
        answer.push(out_word);

        qi += 1;
    }

    answer
}
