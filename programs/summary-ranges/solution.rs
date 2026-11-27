#![allow(unused_macros)]

// The appended harness tests compare against empty expected lists with the bare
// `vec![]`, whose element type is ambiguous when the other operand is
// `Vec<Vec<u8>>` (several `PartialEq` impls match). This local macro fixes the
// type for the empty case and keeps ordinary vector construction for the rest.
macro_rules! vec {
    () => {
        ::std::vec::Vec::<::std::vec::Vec<u8>>::new()
    };
    ($($x:expr),+ $(,)?) => {{
        let mut __out: ::std::vec::Vec<_> = ::std::vec::Vec::new();
        $(
            __out.push($x);
        )+
        __out
    }};
}

fn digit_byte(d: i64) -> u8 {
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

fn int_to_bytes(value: i64) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut x: i64 = value;

    if x < 0 {
        out.push(b'-');
        x = -x;
    }

    if x == 0 {
        out.push(b'0');
        return out;
    }

    let mut tmp: Vec<u8> = Vec::new();
    while x > 0 {
        let d: i64 = x % 10;
        tmp.push(digit_byte(d));
        x = x / 10;
    }

    let mut k: usize = tmp.len();
    while k > 0 {
        k = k - 1;
        out.push(tmp[k]);
    }

    out
}

pub fn summary_ranges(nums: &[i64]) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let n: usize = nums.len();

    if n == 0 {
        return out;
    }

    let mut i: usize = 0;
    while i < n {
        let start: i64 = nums[i];
        let mut end: i64 = start;

        while i + 1 < n && nums[i + 1] == end + 1 {
            i = i + 1;
            end = nums[i];
        }

        let mut s: Vec<u8> = int_to_bytes(start);

        if end != start {
            s.push(b'-');
            s.push(b'>');

            let tail: Vec<u8> = int_to_bytes(end);
            let mut j: usize = 0;
            while j < tail.len() {
                s.push(tail[j]);
                j = j + 1;
            }
        }

        out.push(s);
        i = i + 1;
    }

    out
}
