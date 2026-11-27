pub fn get_folder_names(names: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut ans: Vec<Vec<u8>> = Vec::new();

    let mut head: Vec<i64> = Vec::new();
    let mut edge_ch: Vec<u8> = Vec::new();
    let mut edge_to: Vec<i64> = Vec::new();
    let mut edge_next: Vec<i64> = Vec::new();
    let mut used: Vec<bool> = Vec::new();
    let mut next_k: Vec<i64> = Vec::new();

    head.push(-1);
    used.push(false);
    next_k.push(0);

    let mut i: usize = 0;
    while i < names.len() {
        let s = &names[i];

        // Check whether s is already used.
        let mut probe_node: i64 = 0;
        let mut probe_pos: usize = 0;
        let mut probe_ok: bool = true;
        while probe_pos < s.len() {
            let ch = s[probe_pos];
            let mut e = head[probe_node as usize];
            let mut child: i64 = -1;
            while e != -1 {
                let ei = e as usize;
                if edge_ch[ei] == ch {
                    child = edge_to[ei];
                    e = -1;
                } else {
                    e = edge_next[ei];
                }
            }
            if child == -1 {
                probe_ok = false;
                probe_pos = s.len();
            } else {
                probe_node = child;
                probe_pos = probe_pos + 1;
            }
        }
        if probe_ok {
            probe_ok = used[probe_node as usize];
        }

        if !probe_ok {
            // s is new: insert it, mark it used, and initialize its next suffix.
            let mut ins_node: i64 = 0;
            let mut ins_pos: usize = 0;
            while ins_pos < s.len() {
                let ch = s[ins_pos];
                let mut e = head[ins_node as usize];
                let mut child: i64 = -1;
                while e != -1 {
                    let ei = e as usize;
                    if edge_ch[ei] == ch {
                        child = edge_to[ei];
                        e = -1;
                    } else {
                        e = edge_next[ei];
                    }
                }
                if child == -1 {
                    let created = used.len() as i64;
                    used.push(false);
                    next_k.push(0);
                    head.push(-1);
                    let edge_idx = edge_ch.len() as i64;
                    edge_ch.push(ch);
                    edge_to.push(created);
                    edge_next.push(head[ins_node as usize]);
                    head[ins_node as usize] = edge_idx;
                    child = created;
                }
                ins_node = child;
                ins_pos = ins_pos + 1;
            }
            used[ins_node as usize] = true;
            if next_k[ins_node as usize] == 0 {
                next_k[ins_node as usize] = 1;
            }

            let mut out: Vec<u8> = Vec::new();
            let mut cp: usize = 0;
            while cp < s.len() {
                out.push(s[cp]);
                cp = cp + 1;
            }
            ans.push(out);
        } else {
            // s is used: find its base node and generate the next unique suffix.
            let mut base_node: i64 = 0;
            let mut base_pos: usize = 0;
            while base_pos < s.len() {
                let ch = s[base_pos];
                let mut e = head[base_node as usize];
                let mut child: i64 = -1;
                while e != -1 {
                    let ei = e as usize;
                    if edge_ch[ei] == ch {
                        child = edge_to[ei];
                        e = -1;
                    } else {
                        e = edge_next[ei];
                    }
                }
                if child == -1 {
                    let created = used.len() as i64;
                    used.push(false);
                    next_k.push(0);
                    head.push(-1);
                    let edge_idx = edge_ch.len() as i64;
                    edge_ch.push(ch);
                    edge_to.push(created);
                    edge_next.push(head[base_node as usize]);
                    head[base_node as usize] = edge_idx;
                    child = created;
                }
                base_node = child;
                base_pos = base_pos + 1;
            }

            let mut k = next_k[base_node as usize];
            if k == 0 {
                k = 1;
            }

            let mut assigned: bool = false;
            while !assigned {
                // Build s + "(" + k + ")".
                let mut cand: Vec<u8> = Vec::new();
                let mut cp: usize = 0;
                while cp < s.len() {
                    cand.push(s[cp]);
                    cp = cp + 1;
                }
                cand.push(b'(');

                let mut kk = k;
                let mut digits: Vec<u8> = Vec::new();
                while kk > 0 {
                    let d = (kk % 10) as u8;
                    digits.push(48u8 + d);
                    kk = kk / 10;
                }
                let mut dlen = digits.len();
                while dlen > 0 {
                    dlen = dlen - 1;
                    cand.push(digits[dlen]);
                }
                cand.push(b')');

                // Check whether the candidate is already used.
                let mut cnode: i64 = 0;
                let mut cpos: usize = 0;
                let mut cok: bool = true;
                while cpos < cand.len() {
                    let ch = cand[cpos];
                    let mut e = head[cnode as usize];
                    let mut child: i64 = -1;
                    while e != -1 {
                        let ei = e as usize;
                        if edge_ch[ei] == ch {
                            child = edge_to[ei];
                            e = -1;
                        } else {
                            e = edge_next[ei];
                        }
                    }
                    if child == -1 {
                        cok = false;
                        cpos = cand.len();
                    } else {
                        cnode = child;
                        cpos = cpos + 1;
                    }
                }
                if cok {
                    cok = used[cnode as usize];
                }

                if !cok {
                    // Insert the candidate.
                    let mut ins_node: i64 = 0;
                    let mut ins_pos: usize = 0;
                    while ins_pos < cand.len() {
                        let ch = cand[ins_pos];
                        let mut e = head[ins_node as usize];
                        let mut child: i64 = -1;
                        while e != -1 {
                            let ei = e as usize;
                            if edge_ch[ei] == ch {
                                child = edge_to[ei];
                                e = -1;
                            } else {
                                e = edge_next[ei];
                            }
                        }
                        if child == -1 {
                            let created = used.len() as i64;
                            used.push(false);
                            next_k.push(0);
                            head.push(-1);
                            let edge_idx = edge_ch.len() as i64;
                            edge_ch.push(ch);
                            edge_to.push(created);
                            edge_next.push(head[ins_node as usize]);
                            head[ins_node as usize] = edge_idx;
                            child = created;
                        }
                        ins_node = child;
                        ins_pos = ins_pos + 1;
                    }

                    used[ins_node as usize] = true;
                    if next_k[ins_node as usize] == 0 {
                        next_k[ins_node as usize] = 1;
                    }
                    next_k[base_node as usize] = k + 1;
                    ans.push(cand);
                    assigned = true;
                } else {
                    k = k + 1;
                }
            }
        }

        i = i + 1;
    }

    ans
}
