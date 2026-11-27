import Aegis.MaxNumOfSubstrings.Code.Funs

/-!
# Specifications of `Aegis.MaxNumOfSubstrings.max_num_of_substrings`

LeetCode problem `maximum-number-of-non-overlapping-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxNumOfSubstrings

def byteAt (s : List Std.U8) (i : Nat) : Nat := (s[i]!).val

def seg (s : List Std.U8) (l r : Nat) : List Std.U8 := (s.drop l).take (r + 1 - l)

def IsSubAt (s : List Std.U8) (t : List Std.U8) (l r : Nat) : Prop :=
  t.length = r + 1 - l ∧ ∀ k : Nat, k < t.length → (t[k]!).val = byteAt s (l + k)

def IsClosed (s : List Std.U8) (l r : Nat) : Prop :=
  0 ≤ l ∧ l ≤ r ∧ r < s.length ∧
    ∀ p q : Nat, l ≤ p → p ≤ r → q < s.length → byteAt s q = byteAt s p → l ≤ q ∧ q ≤ r

def IsMinimalClosed (s : List Std.U8) (l r : Nat) : Prop :=
  IsClosed s l r ∧
    ∀ l' r' : Nat, IsClosed s l' r' → l ≤ l' → l' ≤ r' → r' ≤ r → l' = l ∧ r' = r

def IsFamily (s : List Std.U8) (I : List (Nat × Nat)) : Prop :=
  I.Nodup ∧ (∀ p ∈ I, IsClosed s p.1 p.2) ∧
    I.Pairwise (fun p q : Nat × Nat => p.2 < q.1 ∨ q.2 < p.1)

def famLen (I : List (Nat × Nat)) : Nat := (I.map (fun p => p.2 + 1 - p.1)).sum

def IsOptimalFamily (s : List Std.U8) (I : List (Nat × Nat)) : Prop :=
  IsFamily s I ∧
    (∀ J : List (Nat × Nat), IsFamily s J → J.length ≤ I.length) ∧
    (∀ J : List (Nat × Nat), IsFamily s J → J.length = I.length → famLen I ≤ famLen J)

def Occurs (out : List (alloc.vec.Vec Std.U8)) (t : List Std.U8) : Prop :=
  ∃ v ∈ out, v.val = t

def OccursOnce (out : List (alloc.vec.Vec Std.U8)) (t : List Std.U8) : Prop :=
  ∃ v, v ∈ out ∧ v.val = t ∧ ∀ w, w ∈ out → w.val = t → w = v

def distinctBytes (s : List Std.U8) : Nat := (s.map (fun b => b.val)).dedup.length

def totalLen (out : List (alloc.vec.Vec Std.U8)) : Nat :=
  (out.map (fun v => v.val.length)).sum

/-- Call an interval [l,r] closed when 0 <= l <= r < n and, for every p with l <= p <= r and every q with 0 <= q < n, if s[q] = s[p] then l <= q <= r. Call a set I of closed intervals separated when for any two distinct [l1,r1] and [l2,r2] in I, either r1 < l2 or r2 < l1. Let O be the unique separated set of closed intervals that has maximum cardinality and, among all such maximum-cardinality sets, has minimum sum of interval lengths (r-l+1). The function returns a result out such that every element of out is s[l..r] for exactly one interval [l,r] in O, and for every [l,r] in O the byte vector s[l..r] occurs exactly once as an element of out; the order of elements of out is arbitrary. Here s[l..r] is the byte vector of length r-l+1 whose k-th byte is s[l+k].
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_1 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122) :
    ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out ∧
      ∀ O : List (Nat × Nat), IsOptimalFamily s.val O →
        List.Perm (out.val.map (fun v => v.val)) (O.map (fun p => seg s.val p.1 p.2)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out ∧
      ∀ O : List (Nat × Nat), IsOptimalFamily s.val O →
        List.Perm (out.val.map (fun v => v.val)) (O.map (fun p => seg s.val p.1 p.2))) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result out and does not fail (no panic, out-of-bounds access, or 64-bit overflow).
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_2 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122) :
    ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(out), len(out[i]) >= 1.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_3 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    ∀ i, i < out.val.length → 1 ≤ (out.val[i]!).val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), ∀ i, i < out.val.length → 1 ≤ (out.val[i]!).val.length) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(out) there exist integers l and r such that 0 <= l <= r < n, out[i] has length r-l+1, and for every k with 0 <= k < len(out[i]), out[i][k] = s[l+k]. Thus every returned byte vector is a contiguous substring of s.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_4 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    ∀ i, i < out.val.length →
      ∃ l r : Nat, 0 ≤ l ∧ l ≤ r ∧ r < s.val.length ∧ IsSubAt s.val (out.val[i]!).val l r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), ∀ i, i < out.val.length →
      ∃ l r : Nat, 0 ≤ l ∧ l ≤ r ∧ r < s.val.length ∧ IsSubAt s.val (out.val[i]!).val l r) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(out) there exist l and r with 0 <= l <= r < n such that out[i] = s[l..r] and [l,r] is closed: for every p with l <= p <= r and every q with 0 <= q < n, if s[q] = s[p] then l <= q <= r.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_5 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    ∀ i, i < out.val.length →
      ∃ l r : Nat, 0 ≤ l ∧ l ≤ r ∧ r < s.val.length ∧
        (out.val[i]!).val = seg s.val l r ∧ IsClosed s.val l r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), ∀ i, i < out.val.length →
      ∃ l r : Nat, 0 ≤ l ∧ l ≤ r ∧ r < s.val.length ∧
        (out.val[i]!).val = seg s.val l r ∧ IsClosed s.val l r) := by
  sorry

/-- Whenever the function returns a result out, there exist closed intervals [l_i,r_i] for every i with 0 <= i < len(out) such that out[i] = s[l_i..r_i], and for every distinct i,j with 0 <= i,j < len(out), either r_i < l_j or r_j < l_i. In particular, the returned substrings can be represented by pairwise non-overlapping intervals of s.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_6 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    ∃ p : Nat → Nat × Nat,
      (∀ i, i < out.val.length →
        IsClosed s.val (p i).1 (p i).2 ∧ (out.val[i]!).val = seg s.val (p i).1 (p i).2) ∧
      (∀ i j, i < out.val.length → j < out.val.length → i ≠ j →
        (p i).2 < (p j).1 ∨ (p j).2 < (p i).1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), ∃ p : Nat → Nat × Nat,
      (∀ i, i < out.val.length →
        IsClosed s.val (p i).1 (p i).2 ∧ (out.val[i]!).val = seg s.val (p i).1 (p i).2) ∧
      (∀ i j, i < out.val.length → j < out.val.length → i ≠ j →
        (p i).2 < (p j).1 ∨ (p j).2 < (p i).1)) := by
  sorry

/-- Whenever the function returns a result out, for every element t of out there exists an interval [l,r] such that 0 <= l <= r < n, t = s[l..r], [l,r] is closed, and there is no nonempty closed interval [l',r'] with l <= l' <= r' <= r and (l',r') != (l,r). Thus every returned substring corresponds to an inclusion-minimal closed interval.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_7 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    ∀ v ∈ out.val, ∃ l r : Nat, IsMinimalClosed s.val l r ∧ v.val = seg s.val l r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), ∀ v ∈ out.val, ∃ l r : Nat, IsMinimalClosed s.val l r ∧ v.val = seg s.val l r) := by
  sorry

/-- Whenever the function returns a result out, for every interval [l,r] with 0 <= l <= r < n that is closed and has no proper nonempty closed subinterval, the byte vector s[l..r] occurs as an element of out.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_8 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    ∀ l r : Nat, IsMinimalClosed s.val l r → Occurs out.val (seg s.val l r) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), ∀ l r : Nat, IsMinimalClosed s.val l r → Occurs out.val (seg s.val l r)) := by
  sorry

/-- Whenever the function returns a result out, len(out) <= D, where D is the number of distinct byte values occurring in s, that is, D = |{s[i] | 0 <= i < n}|.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_9 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    out.val.length ≤ distinctBytes s.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), out.val.length ≤ distinctBytes s.val) := by
  sorry

/-- Whenever the function returns a result out, the sum of the lengths of all elements of out is at most len(s): sum_{i=0}^{len(out)-1} len(out[i]) <= len(s).
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_10 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    totalLen out.val ≤ s.val.length := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), totalLen out.val ≤ s.val.length) := by
  sorry

/-- Whenever the function returns a result out, for every set I of nonempty closed intervals of s such that any two distinct intervals in I are non-overlapping, the cardinality of I is at most len(out). Here closed means the interval contains all occurrences in s of every byte appearing in it, and non-overlapping means for distinct [l1,r1], [l2,r2] either r1 < l2 or r2 < l1.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_11 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    ∀ I : List (Nat × Nat), IsFamily s.val I → I.length ≤ out.val.length := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), ∀ I : List (Nat × Nat), IsFamily s.val I → I.length ≤ out.val.length) := by
  sorry

/-- Whenever the function returns a result out, for every set I of nonempty closed intervals of s that are pairwise non-overlapping and have cardinality exactly len(out), the inequality sum_{t in out} len(t) <= sum_{[l,r] in I} (r-l+1) holds.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_12 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    ∀ I : List (Nat × Nat), IsFamily s.val I → I.length = out.val.length →
      totalLen out.val ≤ famLen I := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), ∀ I : List (Nat × Nat), IsFamily s.val I → I.length = out.val.length →
      totalLen out.val ≤ famLen I) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(out) there is exactly one interval [l,r] with 0 <= l <= r < n such that out[i] = s[l..r] and [l,r] is closed.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
theorem spec_13 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    ∀ i, i < out.val.length →
      ∃! p : Nat × Nat,
        p.2 < s.val.length ∧ (out.val[i]!).val = seg s.val p.1 p.2 ∧ IsClosed s.val p.1 p.2 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), ∀ i, i < out.val.length →
      ∃! p : Nat × Nat,
        p.2 < s.val.length ∧ (out.val[i]!).val = seg s.val p.1 p.2 ∧ IsClosed s.val p.1 p.2) := by
  sorry

/-- Whenever the function returns a result out, len(out) = 1 and out[0] = s, the whole input byte array.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). Additionally, all bytes of s are equal: s[i] = s[0] for every 0 <= i < n. -/
theorem spec_14 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (hsame : ∀ i, i < s.val.length → s.val[i]! = s.val[0]!)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    out.val.length = 1 ∧ (out.val[0]!).val = s.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (hsame : ∀ i, i < s.val.length → s.val[i]! = s.val[0]!)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), out.val.length = 1 ∧ (out.val[0]!).val = s.val) := by
  sorry

/-- Whenever the function returns a result out, len(out) = len(s), and for every i with 0 <= i < len(s) the one-byte vector whose only byte is s[i] occurs exactly once as an element of out. Equivalently, out is a permutation of the list of all one-byte substrings of s.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). Additionally, every byte value occurs at most once in s: for all i,j with 0 <= i,j < n, if s[i] = s[j] then i = j. -/
theorem spec_15 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (huniq : ∀ i j, i < s.val.length → j < s.val.length → s.val[i]! = s.val[j]! → i = j)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    out.val.length = s.val.length ∧
      ∀ i, i < s.val.length → OccursOnce out.val [s.val[i]!] := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (huniq : ∀ i j, i < s.val.length → j < s.val.length → s.val[i]! = s.val[j]! → i = j)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), out.val.length = s.val.length ∧
      ∀ i, i < s.val.length → OccursOnce out.val [s.val[i]!]) := by
  sorry

/-- Whenever the function returns a result out, the one-byte vector whose only byte is c occurs exactly once as an element of out.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). Additionally, there exist a byte value c and an index i with 0 <= i < n such that s[i] = c and for every j with 0 <= j < n, if s[j] = c then j = i. -/
theorem spec_16 (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (c : Std.U8) (i : Nat) (hi : i < s.val.length) (hc : s.val[i]! = c)
    (hocc : ∀ j, j < s.val.length → s.val[j]! = c → j = i)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out) :
    OccursOnce out.val [c] := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s.val i ∧ byteAt s.val i ≤ 122)
    (c : Std.U8) (i : Nat) (hi : i < s.val.length) (hc : s.val[i]! = c)
    (hocc : ∀ j, j < s.val.length → s.val[j]! = c → j = i)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h : Aegis.MaxNumOfSubstrings.max_num_of_substrings s = ok out), OccursOnce out.val [c]) := by
  sorry

end AegisSpec.MaxNumOfSubstrings
