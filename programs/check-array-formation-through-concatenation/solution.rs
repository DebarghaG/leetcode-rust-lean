pub fn can_form_array(arr: &[i64], pieces: &[Vec<i64>]) -> bool {
    let n = arr.len();
    let num_pieces = pieces.len();

    let mut pos: usize = 0;
    let mut ok: bool = true;
    let mut active: bool = true;

    while active && pos < n {
        // Find the piece that starts with arr[pos].
        let mut q: usize = num_pieces;
        let mut pi: usize = 0;
        while pi < num_pieces {
            if pieces[pi].len() > 0 && pieces[pi][0] == arr[pos] {
                q = pi;
            }
            pi += 1;
        }

        if q == num_pieces {
            ok = false;
            active = false;
        } else {
            let m = pieces[q].len();
            let mut match_ok: bool = true;
            let mut j: usize = 0;
            while j < m {
                let idx = pos + j;
                if idx >= n || arr[idx] != pieces[q][j] {
                    match_ok = false;
                }
                j += 1;
            }

            if !match_ok {
                ok = false;
                active = false;
            } else {
                pos += m;
            }
        }
    }

    if pos < n {
        ok = false;
    }

    ok
}
