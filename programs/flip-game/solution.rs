pub fn generate_possible_next_moves(currentState: &[u8]) -> Vec<Vec<u8>> {
    let n = currentState.len();
    let mut result: Vec<Vec<u8>> = Vec::new();

    let mut i: usize = 0;
    while i + 1 < n {
        if currentState[i] == b'+' && currentState[i + 1] == b'+' {
            let mut next_state: Vec<u8> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                if j == i || j == i + 1 {
                    next_state.push(b'-');
                } else {
                    next_state.push(currentState[j]);
                }
                j += 1;
            }
            result.push(next_state);
        }
        i += 1;
    }

    result
}
