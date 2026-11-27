fn make_push() -> Vec<u8> {
    let mut op: Vec<u8> = Vec::new();
    op.push(b'P');
    op.push(b'u');
    op.push(b's');
    op.push(b'h');
    op
}

fn make_pop() -> Vec<u8> {
    let mut op: Vec<u8> = Vec::new();
    op.push(b'P');
    op.push(b'o');
    op.push(b'p');
    op
}

pub fn build_array(target: &[i64], n: i64) -> Vec<Vec<u8>> {
    let mut operations: Vec<Vec<u8>> = Vec::new();
    let mut target_index: usize = 0;
    let mut stream_value: i64 = 1;

    while target_index < target.len() {
        if target[target_index] == stream_value {
            operations.push(make_push());
            target_index += 1;
        } else {
            operations.push(make_push());
            operations.push(make_pop());
        }

        stream_value += 1;
    }

    operations
}
