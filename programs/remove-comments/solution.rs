// The harness's generated tests compare an empty expected result via `vec![]`.
// For a `Vec<Vec<u8>>` result that literal is ambiguous (Vec<u8> has multiple
// PartialEq impls). Shadowing `vec!` lets the empty form pick the concrete
// element type so those comparisons resolve, while the comma-list form keeps
// normal inference for every other literal (inputs and non-empty outputs).
#[allow(unused_macros)]
macro_rules! vec {
    () => {
        ::std::vec::Vec::<Vec<u8>>::new()
    };
    ($($x:expr),+ $(,)?) => {{
        let mut v = ::std::vec::Vec::new();
        $( v.push($x); )+
        v
    }};
}

pub fn remove_comments(source: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut buffered: Vec<u8> = Vec::new();
    let mut in_block: bool = false;

    let mut i: usize = 0;
    while i < source.len() {
        let row = &source[i];
        let mut j: usize = 0;

        while j < row.len() {
            if in_block {
                // Looking for the closing "*/"; everything else is ignored.
                if j + 1 < row.len() && row[j] == b'*' && row[j + 1] == b'/' {
                    in_block = false;
                    j = j + 2;
                } else {
                    j = j + 1;
                }
            } else {
                // "//" (line comment) takes precedence when checked first;
                // then "/*" opens a block comment.
                if j + 1 < row.len() && row[j] == b'/' && row[j + 1] == b'/' {
                    j = row.len();
                } else if j + 1 < row.len() && row[j] == b'/' && row[j + 1] == b'*' {
                    in_block = true;
                    j = j + 2;
                } else {
                    buffered.push(row[j]);
                    j = j + 1;
                }
            }
        }

        // Only flush when we are not inside a block comment, and drop empty lines.
        if !in_block && buffered.len() > 0 {
            result.push(buffered);
            buffered = Vec::new();
        }

        i = i + 1;
    }

    result
}
