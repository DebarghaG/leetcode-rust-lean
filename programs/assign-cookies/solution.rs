pub fn find_content_children(g: &[i64], s: &[i64]) -> i64 {
    let mut greeds: Vec<i64> = Vec::new();
    let mut cookies: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < g.len() {
        greeds.push(g[i]);
        i += 1;
    }

    let mut j: usize = 0;
    while j < s.len() {
        cookies.push(s[j]);
        j += 1;
    }

    greeds.sort();
    cookies.sort();

    let mut child: usize = 0;
    let mut cookie: usize = 0;
    let mut content: i64 = 0;

    while child < greeds.len() && cookie < cookies.len() {
        if cookies[cookie] >= greeds[child] {
            content += 1;
            child += 1;
            cookie += 1;
        } else {
            cookie += 1;
        }
    }

    content
}
