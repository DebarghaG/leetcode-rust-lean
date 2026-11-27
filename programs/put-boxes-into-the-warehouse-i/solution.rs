pub fn max_boxes_in_warehouse(boxes: &[i64], warehouse: &[i64]) -> i64 {
    let n = warehouse.len();
    let m = boxes.len();

    if n == 0 || m == 0 {
        return 0;
    }

    let mut sorted_boxes: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        sorted_boxes.push(boxes[i]);
        i += 1;
    }
    sorted_boxes.sort();

    let mut caps: Vec<i64> = Vec::new();
    let mut current_min = warehouse[0];
    i = 0;
    while i < n {
        if warehouse[i] < current_min {
            current_min = warehouse[i];
        }
        caps.push(current_min);
        i += 1;
    }

    let mut count: i64 = 0;
    let mut box_idx: usize = 0;
    let mut room = n;

    while room > 0 {
        room -= 1;
        if box_idx < sorted_boxes.len() && sorted_boxes[box_idx] <= caps[room] {
            count += 1;
            box_idx += 1;
        }
    }

    count
}
