pub fn halve_array(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    // We compare reductions using denominator 2^24.
    // A reduction of S/2 corresponds to total * 2^23 in this scale.
    let target: i64 = total * 8388608; // 2^23

    let mut heap_a: Vec<i64> = Vec::new();
    let mut heap_c: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        heap_a.push(nums[i]);
        heap_c.push(0);
        i += 1;
    }

    let mut j: usize = n / 2;
    while j > 0 {
        j -= 1;
        sift_down(&mut heap_a, &mut heap_c, j, n);
    }

    let mut removed: i64 = 0;
    let mut ops: i64 = 0;

    while removed < target {
        let a = heap_a[0];
        let c = heap_c[0];

        let shift: usize = (23 - c) as usize;
        removed += a << shift;

        heap_c[0] = c + 1;
        sift_down(&mut heap_a, &mut heap_c, 0, n);

        ops += 1;
    }

    ops
}

fn greater(a1: i64, c1: i64, a2: i64, c2: i64) -> bool {
    // Compare a1 / 2^c1 with a2 / 2^c2.
    // All original values are at most 10^7 < 2^24,
    // so differences of exponents at least 24 can be decided immediately.
    if c1 >= c2 {
        let diff = c1 - c2;
        if diff >= 24 {
            false
        } else {
            let rhs = a2 << (diff as usize);
            a1 > rhs
        }
    } else {
        let diff = c2 - c1;
        if diff >= 24 {
            true
        } else {
            let lhs = a1 << (diff as usize);
            lhs > a2
        }
    }
}

fn sift_down(heap_a: &mut Vec<i64>, heap_c: &mut Vec<i64>, mut i: usize, n: usize) {
    loop {
        let mut largest = i;
        let left = 2 * i + 1;
        let right = left + 1;

        if left < n
            && greater(
                heap_a[left],
                heap_c[left],
                heap_a[largest],
                heap_c[largest],
            )
        {
            largest = left;
        }

        if right < n
            && greater(
                heap_a[right],
                heap_c[right],
                heap_a[largest],
                heap_c[largest],
            )
        {
            largest = right;
        }

        if largest == i {
            break;
        }

        let tmp_a = heap_a[i];
        heap_a[i] = heap_a[largest];
        heap_a[largest] = tmp_a;

        let tmp_c = heap_c[i];
        heap_c[i] = heap_c[largest];
        heap_c[largest] = tmp_c;

        i = largest;
    }
}
