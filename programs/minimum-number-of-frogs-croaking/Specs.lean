import Aegis.MinNumberOfFrogs.Code.Funs

/-!
# Specifications of `Aegis.MinNumberOfFrogs.min_number_of_frogs`

LeetCode problem `minimum-number-of-frogs-croaking`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinNumberOfFrogs

  namespace AegisSpec.MinNumberOfFrogs

  def bytes (s : Slice Std.U8) : List Std.U8 := s.list.toList

  def byteAt (s : Slice Std.U8) (i : Nat) : Option Std.U8 := (bytes s)[i]?

  def countUpto (s : Slice Std.U8) (x : Std.U8) (p : Nat) : Nat :=
    ((bytes s).take p).countP (fun b => b == x)

  def countC (s : Slice Std.U8) (p : Nat) : Nat := countUpto s 99#u8 p

  def countR (s : Slice Std.U8) (p : Nat) : Nat := countUpto s 114#u8 p

  def countO (s : Slice Std.U8) (p : Nat) : Nat := countUpto s 111#u8 p

  def countA (s : Slice Std.U8) (p : Nat) : Nat := countUpto s 97#u8 p

  def countK (s : Slice Std.U8) (p : Nat) : Nat := countUpto s 107#u8 p

  def IsCroakByte (b : Std.U8) : Prop :=
    b = 99#u8 ∨ b = 114#u8 ∨ b = 111#u8 ∨ b = 97#u8 ∨ b = 107#u8

  def AllCroak (s : Slice Std.U8) : Prop := ∀ b, b ∈ bytes s → IsCroakByte b

  def Valid (s : Slice Std.U8) : Prop :=
    (∀ p, p ≤ s.leng →
        countK s p ≤ countA s p ∧ countA s p ≤ countO s p ∧ countO s p ≤ countR s p ∧
          countR s p ≤ countC s p) ∧
      countC s s.leng = countR s s.leng ∧ countR s s.leng = countO s s.leng ∧
        countO s s.leng = countA s s.leng ∧ countA s s.leng = countK s s.leng

  def TotalsEqual (s : Slice Std.U8) : Prop :=
    countC s s.leng = countR s s.leng ∧ countR s s.leng = countO s s.leng ∧
      countO s s.leng = countA s s.leng ∧ countA s s.leng = countK s s.leng

  def maxActive (s : Slice Std.U8) : ℤ :=
    ((List.range (s.leng + 1)).map (fun p => (countC s p : ℤ) - (countK s p : ℤ))).foldr max 0

  def croakBlocks (m : Nat) : List Std.U8 :=
    (List.range m).flatMap (fun _ => [99#u8, 114#u8, 111#u8, 97#u8, 107#u8])

  def SpellsCroakBlocks (l : List Std.U8) : Prop := ∃ m, 1 ≤ m ∧ l = croakBlocks m

  def blockOf (s : Slice Std.U8) (col : Nat → Nat) (j p : Nat) : List Std.U8 :=
    (((List.range p).filter (fun i => decide (col i = j))).filterMap (fun i => byteAt s i))

  def CroakPartition (s : Slice Std.U8) (r : Nat) : Prop :=
    ∃ col : Nat → Nat,
      (∀ i, i < s.leng → col i < r) ∧
        (∀ j, j < r → ∃ i, i < s.leng ∧ col i = j) ∧
          (∀ j, j < r → SpellsCroakBlocks (blockOf s col j s.leng))

  /-- For 0 <= p <= n, let C(p), R(p), O(p), A(p), K(p) be the numbers of occurrences of 'c', 'r', 'o', 'a', 'k' among s[0], ..., s[p-1]. Call s valid when C(p) >= R(p) >= O(p) >= A(p) >= K(p) for every p with 0 <= p <= n, and C(n) = R(n) = O(n) = A(n) = K(n). Whenever min_number_of_frogs s returns a result r: if s is valid, then r = max{ C(p) - K(p) | 0 <= p <= n }; otherwise r = -1.
    Preconditions: Let s = croakOfFrogs and n = len(s). Assume 1 <= n <= 100000 (the problem's 10^5 bound) and that for every i with 0 <= i < n, s[i] is one of the ASCII bytes for 'c', 'r', 'o', 'a', 'k'. -/
  theorem spec_1 (s : Slice Std.U8)
      (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s) :
      ∀ r : Std.I64, min_number_of_frogs s = ok r →
        (Valid s → r.val = maxActive s) ∧ (¬ Valid s → r.val = (-1 : ℤ)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s), ∀ r : Std.I64, min_number_of_frogs s = ok r →
          (Valid s → r.val = maxActive s) ∧ (¬ Valid s → r.val = (-1 : ℤ))) := by
    sorry

  /-- There exists an i64 r such that min_number_of_frogs s = Result.ok r; in particular the call does not return Err and does not panic, overflow, or access out of bounds.
    Preconditions: Let s = croakOfFrogs and n = len(s). Assume 1 <= n <= 100000 and that for every i with 0 <= i < n, s[i] is one of the ASCII bytes for 'c', 'r', 'o', 'a', 'k'. -/
  theorem spec_2 (s : Slice Std.U8)
      (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s) :
      ∃ r : Std.I64, min_number_of_frogs s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s), ∃ r : Std.I64, min_number_of_frogs s = ok r) := by
    sorry

  /-- Whenever min_number_of_frogs s returns a result r, we have 1 <= r <= C(n), where C(n) is the total number of 'c' bytes in s. Since s is valid and nonempty, equivalently C(n) = n/5.
    Preconditions: Let s = croakOfFrogs and n = len(s). Assume 1 <= n <= 100000, all bytes of s are in {'c','r','o','a','k'}, and s is valid in the sense of S1 (prefix counts C(p) >= R(p) >= O(p) >= A(p) >= K(p), and all five total counts are equal). -/
  theorem spec_3 (s : Slice Std.U8)
      (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
      (hvalid : Valid s) :
      ∀ r : Std.I64, min_number_of_frogs s = ok r →
        1 ≤ r.val ∧ r.val ≤ (countC s s.leng : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
        (hvalid : Valid s), ∀ r : Std.I64, min_number_of_frogs s = ok r →
          1 ≤ r.val ∧ r.val ≤ (countC s s.leng : ℤ)) := by
    sorry

  /-- Whenever min_number_of_frogs s returns a result r, for every p with 0 <= p <= n we have C(p) - K(p) <= r.
    Preconditions: Let s = croakOfFrogs and n = len(s). Assume 1 <= n <= 100000, all bytes of s are in {'c','r','o','a','k'}, and s is valid in the sense of spec_1, with C(p) and K(p) the counts of 'c' and 'k' in the first p bytes. -/
  theorem spec_4 (s : Slice Std.U8)
      (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
      (hvalid : Valid s) :
      ∀ r : Std.I64, min_number_of_frogs s = ok r →
        ∀ p, p ≤ s.leng → (countC s p : ℤ) - (countK s p : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
        (hvalid : Valid s), ∀ r : Std.I64, min_number_of_frogs s = ok r →
          ∀ p, p ≤ s.leng → (countC s p : ℤ) - (countK s p : ℤ) ≤ r.val) := by
    sorry

  /-- If C(n), R(n), O(n), A(n), K(n) are not all equal, then whenever min_number_of_frogs s returns a result r, r = -1.
    Preconditions: Let s = croakOfFrogs and n = len(s). Assume 1 <= n <= 100000 and all bytes of s are in {'c','r','o','a','k'}. Let C(n), R(n), O(n), A(n), K(n) be the total counts of 'c', 'r', 'o', 'a', 'k' in s. -/
  theorem spec_5 (s : Slice Std.U8)
      (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
      (hne : ¬ TotalsEqual s) :
      ∀ r : Std.I64, min_number_of_frogs s = ok r → r.val = (-1 : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
        (hne : ¬ TotalsEqual s), ∀ r : Std.I64, min_number_of_frogs s = ok r → r.val = (-1 : ℤ)) := by
    sorry

  /-- If there exists p with 0 <= p <= n such that C(p) < R(p) or R(p) < O(p) or O(p) < A(p) or A(p) < K(p), then whenever min_number_of_frogs s returns a result r, r = -1.
    Preconditions: Let s = croakOfFrogs and n = len(s). Assume 1 <= n <= 100000 and all bytes of s are in {'c','r','o','a','k'}. For 0 <= p <= n, let C(p), R(p), O(p), A(p), K(p) be the prefix counts of 'c', 'r', 'o', 'a', 'k' among the first p bytes. -/
  theorem spec_6 (s : Slice Std.U8)
      (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
      (hviol : ∃ p, p ≤ s.leng ∧
        (countC s p < countR s p ∨ countR s p < countO s p ∨
          countO s p < countA s p ∨ countA s p < countK s p)) :
      ∀ r : Std.I64, min_number_of_frogs s = ok r → r.val = (-1 : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
        (hviol : ∃ p, p ≤ s.leng ∧
          (countC s p < countR s p ∨ countR s p < countO s p ∨
            countO s p < countA s p ∨ countA s p < countK s p)), ∀ r : Std.I64, min_number_of_frogs s = ok r → r.val = (-1 : ℤ)) := by
    sorry

  /-- Whenever min_number_of_frogs s returns a result r, r = 1 if and only if n is a positive multiple of 5 and for every j with 0 <= j < n/5, s[5j] = 'c', s[5j+1] = 'r', s[5j+2] = 'o', s[5j+3] = 'a', and s[5j+4] = 'k'.
    Preconditions: Let s = croakOfFrogs and n = len(s). Assume 1 <= n <= 100000 and all bytes of s are in {'c','r','o','a','k'}. -/
  theorem spec_7 (s : Slice Std.U8)
      (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s) :
      ∀ r : Std.I64, min_number_of_frogs s = ok r →
        (r.val = 1 ↔
          0 < s.leng ∧ 5 ∣ s.leng ∧
            ∀ j, j < s.leng / 5 →
              byteAt s (5 * j) = some 99#u8 ∧ byteAt s (5 * j + 1) = some 114#u8 ∧
                byteAt s (5 * j + 2) = some 111#u8 ∧ byteAt s (5 * j + 3) = some 97#u8 ∧
                  byteAt s (5 * j + 4) = some 107#u8) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s), ∀ r : Std.I64, min_number_of_frogs s = ok r →
          (r.val = 1 ↔
            0 < s.leng ∧ 5 ∣ s.leng ∧
              ∀ j, j < s.leng / 5 →
                byteAt s (5 * j) = some 99#u8 ∧ byteAt s (5 * j + 1) = some 114#u8 ∧
                  byteAt s (5 * j + 2) = some 111#u8 ∧ byteAt s (5 * j + 3) = some 97#u8 ∧
                    byteAt s (5 * j + 4) = some 107#u8)) := by
    sorry

  /-- For this s, min_number_of_frogs s returns a result r and r = m.
    Preconditions: There is an integer m with 1 <= m and 5m <= 100000, and s has length 5m with s[i] = 'c' for 0 <= i < m, s[i] = 'r' for m <= i < 2m, s[i] = 'o' for 2m <= i < 3m, s[i] = 'a' for 3m <= i < 4m, and s[i] = 'k' for 4m <= i < 5m. -/
  theorem spec_8 (s : Slice Std.U8) (m : Nat)
      (hm : 1 ≤ m) (hmle : 5 * m ≤ 100000) (hlen : s.leng = 5 * m)
      (hc : ∀ i, i < m → byteAt s i = some 99#u8)
      (hr : ∀ i, m ≤ i → i < 2 * m → byteAt s i = some 114#u8)
      (ho : ∀ i, 2 * m ≤ i → i < 3 * m → byteAt s i = some 111#u8)
      (ha : ∀ i, 3 * m ≤ i → i < 4 * m → byteAt s i = some 97#u8)
      (hk : ∀ i, 4 * m ≤ i → i < 5 * m → byteAt s i = some 107#u8) :
      ∃ r : Std.I64, min_number_of_frogs s = ok r ∧ r.val = (m : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (m : Nat)
        (hm : 1 ≤ m) (hmle : 5 * m ≤ 100000) (hlen : s.leng = 5 * m)
        (hc : ∀ i, i < m → byteAt s i = some 99#u8)
        (hr : ∀ i, m ≤ i → i < 2 * m → byteAt s i = some 114#u8)
        (ho : ∀ i, 2 * m ≤ i → i < 3 * m → byteAt s i = some 111#u8)
        (ha : ∀ i, 3 * m ≤ i → i < 4 * m → byteAt s i = some 97#u8)
        (hk : ∀ i, 4 * m ≤ i → i < 5 * m → byteAt s i = some 107#u8), ∃ r : Std.I64, min_number_of_frogs s = ok r ∧ r.val = (m : ℤ)) := by
    sorry

  /-- If min_number_of_frogs s returns a result r, then the index set {0, ..., n-1} can be partitioned into r nonempty subsets P_1, ..., P_r such that for each j, when the indices in P_j are listed in increasing order, the corresponding bytes spell 'c','r','o','a','k','c','r','o','a','k', ... , i.e. a positive number of complete 'croak' blocks.
    Preconditions: Let s = croakOfFrogs and n = len(s). Assume 1 <= n <= 100000, all bytes of s are in {'c','r','o','a','k'}, and s is valid in the sense of spec_1. -/
  theorem spec_9 (s : Slice Std.U8)
      (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
      (hvalid : Valid s) :
      ∀ r : Std.I64, min_number_of_frogs s = ok r → CroakPartition s r.val.toNat := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
        (hvalid : Valid s), ∀ r : Std.I64, min_number_of_frogs s = ok r → CroakPartition s r.val.toNat) := by
    sorry

  /-- If min_number_of_frogs s returns a result r, then for every integer q with 0 <= q < r, there is no partition of {0, ..., n-1} into q nonempty subsets such that each subset, read in increasing index order, spells a positive number of complete 'croak' blocks.
    Preconditions: Let s = croakOfFrogs and n = len(s). Assume 1 <= n <= 100000, all bytes of s are in {'c','r','o','a','k'}, and s is valid in the sense of spec_1. -/
  theorem spec_10 (s : Slice Std.U8)
      (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
      (hvalid : Valid s) :
      ∀ r : Std.I64, min_number_of_frogs s = ok r →
        ∀ q : Nat, q < r.val.toNat → ¬ CroakPartition s q := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
        (hvalid : Valid s), ∀ r : Std.I64, min_number_of_frogs s = ok r →
          ∀ q : Nat, q < r.val.toNat → ¬ CroakPartition s q) := by
    sorry

  /-- Whenever min_number_of_frogs s returns r, min_number_of_frogs u returns r_u, and min_number_of_frogs v returns r_v, we have r = max(r_u, r_v).
    Preconditions: Let u and v be byte slices, each of length at least 1, with len(u) + len(v) <= 100000 and all bytes in {'c','r','o','a','k'}. Assume u and v are both valid in the sense of spec_1. Let s be the concatenation of u followed by v. -/
  theorem spec_11 (u v s : Slice Std.U8)
      (hu_pos : 1 ≤ u.leng) (hv_pos : 1 ≤ v.leng)
      (hlen : u.leng + v.leng ≤ 100000)
      (hu : AllCroak u) (hv : AllCroak v)
      (huvalid : Valid u) (hvvalid : Valid v)
      (hcat : bytes s = bytes u ++ bytes v) :
      ∀ r r_u r_v : Std.I64,
        min_number_of_frogs s = ok r → min_number_of_frogs u = ok r_u →
          min_number_of_frogs v = ok r_v → r.val = max r_u.val r_v.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (u v s : Slice Std.U8)
        (hu_pos : 1 ≤ u.leng) (hv_pos : 1 ≤ v.leng)
        (hlen : u.leng + v.leng ≤ 100000)
        (hu : AllCroak u) (hv : AllCroak v)
        (huvalid : Valid u) (hvvalid : Valid v)
        (hcat : bytes s = bytes u ++ bytes v), ∀ r r_u r_v : Std.I64,
          min_number_of_frogs s = ok r → min_number_of_frogs u = ok r_u →
            min_number_of_frogs v = ok r_v → r.val = max r_u.val r_v.val) := by
    sorry

  /-- Whenever min_number_of_frogs s returns r and min_number_of_frogs t returns r_t, we have r_t = r.
    Preconditions: Let s be a byte slice satisfying the S1 preconditions and assume s is valid. Let q >= 1 with len(s) + 5q <= 100000, and let t be the concatenation of s followed by q copies of the string 'croak'. -/
  theorem spec_12 (s t : Slice Std.U8) (q : Nat)
      (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
      (hvalid : Valid s)
      (hq : 1 ≤ q) (hlen : s.leng + 5 * q ≤ 100000)
      (ht : bytes t = bytes s ++ croakBlocks q) :
      ∀ r r_t : Std.I64,
        min_number_of_frogs s = ok r → min_number_of_frogs t = ok r_t → r_t.val = r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Slice Std.U8) (q : Nat)
        (hn_pos : 1 ≤ s.leng) (hn_le : s.leng ≤ 100000) (hbytes : AllCroak s)
        (hvalid : Valid s)
        (hq : 1 ≤ q) (hlen : s.leng + 5 * q ≤ 100000)
        (ht : bytes t = bytes s ++ croakBlocks q), ∀ r r_t : Std.I64,
          min_number_of_frogs s = ok r → min_number_of_frogs t = ok r_t → r_t.val = r.val) := by
    sorry

  end AegisSpec.MinNumberOfFrogs
