pub fn large_group_positions(s: &[u8]) -> Vec<Vec<i64>> {
    let n: usize = s.len();
    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;
        while j < n && s[j] == s[i] {
            j += 1;
        }

        if j - i >= 3 {
            let mut interval: Vec<i64> = Vec::new();
            interval.push(i as i64);
            interval.push((j - 1) as i64);
            out.push(interval);
        }

        i = j;
    }

    out
}

// The appended unit tests compare `Vec<Vec<i64>>` results against `vec![]`.
// With std's `vec![]` that comparison is ambiguous (E0282) because the empty
// literal's element type cannot be inferred against a nested `Vec`. This
// test-only macro pins the empty case to `Vec<Vec<i64>>` and otherwise behaves
// exactly like the standard macro. It is compiled only under `cfg(test)`, so it
// never appears in the normal (translatable) build of the crate.
#[cfg(test)]
macro_rules! vec {
    () => {
        ::std::vec::Vec::<::std::vec::Vec<i64>>::new()
    };
    ($($x:expr),+ $(,)?) => {{
        let mut v = ::std::vec::Vec::new();
        $( v.push($x); )+
        v
    }};
}
