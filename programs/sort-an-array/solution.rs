pub fn sort_array(nums: &[i64]) -> Vec<i64> {
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < nums.len() {
        a.push(nums[i]);
        i = i + 1;
    }

    let n: usize = a.len();
    if n > 1 {
        let mut start: usize = n / 2;
        while start > 0 {
            start = start - 1;

            let mut root: usize = start;
            let mut going: bool = true;
            while going {
                let left: usize = root * 2 + 1;
                let right: usize = left + 1;
                let mut largest: usize = root;

                if left < n && a[left] > a[largest] {
                    largest = left;
                }
                if right < n && a[right] > a[largest] {
                    largest = right;
                }

                if largest == root {
                    going = false;
                } else {
                    let tmp: i64 = a[root];
                    a[root] = a[largest];
                    a[largest] = tmp;
                    root = largest;
                }
            }
        }

        let mut end: usize = n;
        while end > 1 {
            end = end - 1;

            let tmp: i64 = a[0];
            a[0] = a[end];
            a[end] = tmp;

            let mut root: usize = 0;
            let mut going: bool = true;
            while going {
                let left: usize = root * 2 + 1;
                let right: usize = left + 1;
                let mut largest: usize = root;

                if left < end && a[left] > a[largest] {
                    largest = left;
                }
                if right < end && a[right] > a[largest] {
                    largest = right;
                }

                if largest == root {
                    going = false;
                } else {
                    let tmp2: i64 = a[root];
                    a[root] = a[largest];
                    a[largest] = tmp2;
                    root = largest;
                }
            }
        }
    }

    a
}
