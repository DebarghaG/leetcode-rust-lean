pub fn find_even_numbers(digits: &[i64]) -> Vec<i64> {
    let mut counts: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 10 {
        counts.push(0);
        k += 1;
    }

    let mut i: usize = 0;
    while i < digits.len() {
        let d = digits[i] as usize;
        counts[d] = counts[d] + 1;
        i += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut n: i64 = 100;
    while n <= 999 {
        let a = (n / 100) as usize;
        let b = ((n / 10) % 10) as usize;
        let c = (n % 10) as usize;

        if can_form(&counts, a, b, c) {
            result.push(n);
        }

        n += 2;
    }

    result
}

fn can_form(counts: &[i64], a: usize, b: usize, c: usize) -> bool {
    if a == b && b == c {
        counts[a] >= 3
    } else if a == b {
        counts[a] >= 2 && counts[c] >= 1
    } else if a == c {
        counts[a] >= 2 && counts[b] >= 1
    } else if b == c {
        counts[b] >= 2 && counts[a] >= 1
    } else {
        counts[a] >= 1 && counts[b] >= 1 && counts[c] >= 1
    }
}
