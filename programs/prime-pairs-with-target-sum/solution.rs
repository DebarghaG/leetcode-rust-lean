// Only exists during `cargo test`; invisible to a normal build (and to Charon/Aeneas).
// It resolves the `vec![]`-element inference ambiguity in the test harness by
// pinning the empty-vector type to `Vec<Vec<i64>>` (the function's return type).
#[cfg(test)]
macro_rules! vec {
    () => {
        ::std::vec::Vec::<Vec<i64>>::new()
    };
    ($($x:expr),+ $(,)?) => {{
        let mut __v = ::std::vec::Vec::new();
        $( __v.push($x); )+
        __v
    }};
}

pub fn find_prime_pairs(n: i64) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = Vec::new();

    if n < 2 {
        return out;
    }

    let m: usize = n as usize;

    // Sieve of Eratosthenes: is_prime[i] == true iff i is prime (for i in 0..=m).
    let mut is_prime: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i <= m {
        is_prime.push(true);
        i += 1;
    }

    is_prime[0] = false;
    is_prime[1] = false;

    let mut p: usize = 2;
    while p * p <= m {
        if is_prime[p] {
            let mut j: usize = p * p;
            while j <= m {
                is_prime[j] = false;
                j += p;
            }
        }
        p += 1;
    }

    // Enumerate x from 2 up to n/2 (so that x <= y = n - x).
    let half: i64 = n / 2;
    let mut x: i64 = 2;
    while x <= half {
        let y: i64 = n - x;
        let xu: usize = x as usize;
        let yu: usize = y as usize;
        if is_prime[xu] && is_prime[yu] {
            let mut pair: Vec<i64> = Vec::new();
            pair.push(x);
            pair.push(y);
            out.push(pair);
        }
        x += 1;
    }

    out
}
