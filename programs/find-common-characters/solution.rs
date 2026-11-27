pub fn common_chars(words: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();

    if words.len() == 0 {
        return out;
    }

    // min_counts will hold the minimum frequency of each lowercase letter
    // across all words processed so far.
    let mut min_counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        min_counts.push(0);
        i += 1;
    }

    // Initialize counts using the first word.
    let first = &words[0];
    let mut j: usize = 0;
    while j < first.len() {
        let b: u8 = first[j];
        let idx: usize = (b - b'a') as usize;
        min_counts[idx] = min_counts[idx] + 1;
        j += 1;
    }

    // Update minimum counts using each subsequent word.
    i = 1;
    while i < words.len() {
        let mut counts: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < 26 {
            counts.push(0);
            k += 1;
        }

        let word = &words[i];
        j = 0;
        while j < word.len() {
            let b: u8 = word[j];
            let idx: usize = (b - b'a') as usize;
            counts[idx] = counts[idx] + 1;
            j += 1;
        }

        k = 0;
        while k < 26 {
            if counts[k] < min_counts[k] {
                min_counts[k] = counts[k];
            }
            k += 1;
        }

        i += 1;
    }

    // Build the output in alphabetical order.
    let mut letter: usize = 0;
    while letter < 26 {
        let c: u8 = b'a' + (letter as u8);
        let mut rep: i64 = 0;
        while rep < min_counts[letter] {
            let mut s: Vec<u8> = Vec::new();
            s.push(c);
            out.push(s);
            rep += 1;
        }
        letter += 1;
    }

    out
}
