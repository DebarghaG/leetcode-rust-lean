pub fn can_be_equal(s1: &[u8], s2: &[u8]) -> bool {
    let even_ok = (s1[0] == s2[0] && s1[2] == s2[2])
        || (s1[0] == s2[2] && s1[2] == s2[0]);

    let odd_ok = (s1[1] == s2[1] && s1[3] == s2[3])
        || (s1[1] == s2[3] && s1[3] == s2[1]);

    even_ok && odd_ok
}
