pub fn num_unique_emails(emails: &[Vec<u8>]) -> i64 {
    let mut unique: Vec<Vec<u8>> = Vec::new();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < emails.len() {
        let mut key: Vec<u8> = Vec::new();
        let mut p: usize = 0;
        let mut ignoring: bool = false;

        while p < emails[i].len() {
            let b: u8 = emails[i][p];

            if b == b'@' {
                key.push(b'@');
                p = p + 1;
                while p < emails[i].len() {
                    key.push(emails[i][p]);
                    p = p + 1;
                }
            } else {
                if ignoring {
                    // Skip everything until '@' in the local name.
                } else if b == b'+' {
                    ignoring = true;
                } else if b != b'.' {
                    key.push(b);
                }
                p = p + 1;
            }
        }

        let mut found: bool = false;
        let mut j: usize = 0;

        while j < unique.len() {
            if unique[j].len() == key.len() {
                let mut same: bool = true;
                let mut k: usize = 0;

                while k < key.len() {
                    if unique[j][k] != key[k] {
                        same = false;
                        break;
                    }
                    k = k + 1;
                }

                if same {
                    found = true;
                    break;
                }
            }

            j = j + 1;
        }

        if !found {
            unique.push(key);
            count = count + 1;
        }

        i = i + 1;
    }

    count
}
