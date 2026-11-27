pub fn sequential_digits(low: i64, high: i64) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();

    let mut length: i64 = 2;
    while length <= 9 {
        let mut start: i64 = 1;
        while start + length - 1 <= 9 {
            let mut num: i64 = 0;
            let mut digit: i64 = start;
            let mut count: i64 = 0;

            while count < length {
                num = num * 10 + digit;
                digit = digit + 1;
                count = count + 1;
            }

            if num >= low && num <= high {
                result.push(num);
            }

            start = start + 1;
        }

        length = length + 1;
    }

    result
}
