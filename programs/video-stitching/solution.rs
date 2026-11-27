pub fn video_stitching(clips: &[Vec<i64>], time: i64) -> i64 {
    let n = clips.len();
    let mut count: i64 = 0;
    let mut covered: i64 = 0;

    while covered < time {
        let mut best: i64 = covered;
        let mut i: usize = 0;

        while i < n {
            let start = clips[i][0];
            let end = clips[i][1];

            if start <= covered && end > best {
                best = end;
            }

            i += 1;
        }

        if best <= covered {
            return -1;
        }

        covered = best;
        count += 1;
    }

    count
}
