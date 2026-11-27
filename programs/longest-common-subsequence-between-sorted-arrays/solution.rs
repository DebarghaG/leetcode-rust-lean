pub fn longest_common_subsequence(arrays: &[Vec<i64>]) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();
    if arrays.len() == 0 {
        return ans;
    }

    let first = &arrays[0];
    let mut j: usize = 0;
    while j < first.len() {
        let val = first[j];
        let mut in_all: bool = true;
        let mut i: usize = 1;

        while i < arrays.len() {
            let row = &arrays[i];
            let mut found: bool = false;
            let mut k: usize = 0;

            while k < row.len() {
                if row[k] == val {
                    found = true;
                }
                k += 1;
            }

            if !found {
                in_all = false;
            }
            i += 1;
        }

        if in_all {
            ans.push(val);
        }
        j += 1;
    }

    ans
}
