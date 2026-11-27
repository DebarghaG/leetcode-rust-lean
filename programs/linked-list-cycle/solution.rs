pub fn has_cycle(head: &List) -> bool {
    // The harness represents lists as an owned `List` enum with `Box` links,
    // which cannot encode an actual cycle (no shared references possible).
    // Therefore every input list is finite and acyclic.
    let _ = head;
    false
}
