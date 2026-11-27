pub fn max_number_of_apples(weight: &[i64]) -> i64 {
    let n = weight.len();

    let mut arr: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        arr.push(weight[i]);
        i += 1;
    }

    let mut a = 1usize;
    while a < n {
        let key = arr[a];
        let mut b = a;
        while b > 0 && arr[b - 1] > key {
            arr[b] = arr[b - 1];
            b -= 1;
        }
        arr[b] = key;
        a += 1;
    }

    let mut total: i64 = 0;
    let mut count: i64 = 0;
    let mut j = 0usize;

    while j < n {
        if total + arr[j] > 5000 {
            return count;
        }
        total += arr[j];
        count += 1;
        j += 1;
    }

    count
}
