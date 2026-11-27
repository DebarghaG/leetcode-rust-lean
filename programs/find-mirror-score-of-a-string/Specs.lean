import Aegis.CalculateScore.Code.Funs

/-!
# Specifications of `Aegis.CalculateScore.calculate_score`

LeetCode problem `find-mirror-score-of-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CalculateScore

def mirrorCode (c : Nat) : Nat := 219 - c

def codes (l : List Std.U8) : List Nat := l.map (fun b => b.val)

def sliceTake (s : Slice Std.U8) (k : Nat) : Slice Std.U8 :=
  Slice.from (s.val.take k) (by
    have h : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
    have h2 : (s.val.take k).length ≤ s.val.length := by
      rw [List.length_take]; omega
    have h3 := s.bound
    omega)

def sliceDrop (s : Slice Std.U8) (k : Nat) : Slice Std.U8 :=
  Slice.from (s.val.drop k) (by
    have h : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
    have h2 : (s.val.drop k).length ≤ s.val.length := by
      rw [List.length_drop]; omega
    have h3 := s.bound
    omega)

def markAux (chr : Nat → Nat) (dist : Nat → Nat → Nat) :
    List Nat → List Nat → Nat → List Nat × Nat
  | [], U, sc => (U, sc)
  | i :: rest, U, sc =>
      match (U.filter (fun j => decide (chr j = mirrorCode (chr i)))).getLast? with
      | some j => markAux chr dist rest (U.erase j) (sc + dist j i)
      | none => markAux chr dist rest (U ++ [i]) sc

def markScore (chr : Nat → Nat) (dist : Nat → Nat → Nat) (is : List Nat) : Nat :=
  (markAux chr dist is [] 0).2

def specScore (cs : List Nat) : Nat :=
  markScore (fun i => cs.getD i 0) (fun j i => i - j) (List.range cs.length)

def classIndices (cs : List Nat) (c : Nat) : List Nat :=
  (List.range cs.length).filter
    (fun i => decide (cs.getD i 0 = c ∨ cs.getD i 0 = mirrorCode c))

def classScore (cs : List Nat) (c : Nat) : Nat :=
  let I := classIndices cs c
  markScore (fun t => cs.getD (I.getD t 0) 0) (fun a b => I.getD b 0 - I.getD a 0)
    (List.range I.length)

def totalClassScore (cs : List Nat) : Nat :=
  ((List.range 13).map (fun t => classScore cs (97 + t))).sum

/-- The function returns a result r, and r = score_n, where score_n is defined by the following left-to-right marking process. For i = 0, ..., n let U_i be a set of indices and score_i an integer. Set U_0 = the empty set and score_0 = 0. For each i with 0 <= i < n, let E_i = { j | j is in U_i and s[j] = 219 - s[i] } (these are exactly the unmarked earlier indices whose character is the mirror of s[i]). If E_i is nonempty, let j_i = max E_i; set U_{i+1} = U_i without j_i and score_{i+1} = score_i + (i - j_i). If E_i is empty, set U_{i+1} = U_i union {i} and score_{i+1} = score_i. Then r = score_n.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122 (s consists of lowercase ASCII letters). -/
theorem spec_1 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122) :
    ∃ r : Std.I64,
      Aegis.CalculateScore.calculate_score s = ok r ∧
        r.val = ((specScore (codes s.val) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122), ∃ r : Std.I64,
      Aegis.CalculateScore.calculate_score s = ok r ∧
        r.val = ((specScore (codes s.val) : Nat) : Int)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail due to overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122) :
    ∃ r : Std.I64, Aegis.CalculateScore.calculate_score s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122), ∃ r : Std.I64, Aegis.CalculateScore.calculate_score s = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= floor(n / 2) * (n - floor(n / 2)), where floor(n / 2) is integer division by 2.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r) :
    r.val ≤ (((s.val.length / 2) * (s.val.length - s.val.length / 2) : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r), r.val ≤ (((s.val.length / 2) * (s.val.length - s.val.length / 2) : Nat) : Int)) := by
  sorry

/-- If n = 1, then whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_5 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (hone : s.val.length = 1)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (hone : s.val.length = 1)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for all indices j and i with 0 <= j < i < n, s[j] != 219 - s[i].
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_6 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r) :
    r.val = 0 ↔ ∀ j i, j < i → i < s.val.length → (s.val[j]!).val ≠ 219 - (s.val[i]!).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r), r.val = 0 ↔ ∀ j i, j < i → i < s.val.length → (s.val[j]!).val ≠ 219 - (s.val[i]!).val) := by
  sorry

/-- If n = 2, then whenever the function returns a result r, r = 1 if s[1] = 219 - s[0], and r = 0 otherwise.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_7 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (htwo : s.val.length = 2)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r) :
    ((s.val[1]!).val = 219 - (s.val[0]!).val → r.val = 1) ∧
      ((s.val[1]!).val ≠ 219 - (s.val[0]!).val → r.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (htwo : s.val.length = 2)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r), ((s.val[1]!).val = 219 - (s.val[0]!).val → r.val = 1) ∧
      ((s.val[1]!).val ≠ 219 - (s.val[0]!).val → r.val = 0)) := by
  sorry

/-- Let t be the byte string of length n with t[i] = 219 - s[i] for every 0 <= i < n. If the function returns r on s and r' on t, then r = r'.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_8 (s t : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (htlen : t.val.length = s.val.length)
    (ht : ∀ i, i < s.val.length → (t.val[i]!).val = 219 - (s.val[i]!).val)
    (r r' : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r)
    (hr' : Aegis.CalculateScore.calculate_score t = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (htlen : t.val.length = s.val.length)
    (ht : ∀ i, i < s.val.length → (t.val[i]!).val = 219 - (s.val[i]!).val)
    (r r' : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r)
    (hr' : Aegis.CalculateScore.calculate_score t = ok r'), r = r') := by
  sorry

/-- For every k with 1 <= k <= n, let p_k be the prefix slice s[0..k). If the function returns r on s and r_k on p_k, then r >= r_k.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_9 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r) :
    ∀ k, 1 ≤ k → k ≤ s.val.length → ∀ rk : Std.I64,
      Aegis.CalculateScore.calculate_score (sliceTake s k) = ok rk → rk.val ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r), ∀ k, 1 ≤ k → k ≤ s.val.length → ∀ rk : Std.I64,
      Aegis.CalculateScore.calculate_score (sliceTake s k) = ok rk → rk.val ≤ r.val) := by
  sorry

/-- Let k be an index with 1 <= k < n, let x = s[0..k), and let y = s[k..n). Suppose that for every a and b with 0 <= a < k <= b < n, s[b] != 219 - s[a]. If the function returns r on s, r_x on x, and r_y on y, then r = r_x + r_y.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_10 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (k : Nat) (hk1 : 1 ≤ k) (hkn : k < s.val.length)
    (hcross : ∀ a b, a < k → k ≤ b → b < s.val.length →
      (s.val[b]!).val ≠ 219 - (s.val[a]!).val)
    (r rx ry : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r)
    (hrx : Aegis.CalculateScore.calculate_score (sliceTake s k) = ok rx)
    (hry : Aegis.CalculateScore.calculate_score (sliceDrop s k) = ok ry) :
    r.val = rx.val + ry.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (k : Nat) (hk1 : 1 ≤ k) (hkn : k < s.val.length)
    (hcross : ∀ a b, a < k → k ≤ b → b < s.val.length →
      (s.val[b]!).val ≠ 219 - (s.val[a]!).val)
    (r rx ry : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r)
    (hrx : Aegis.CalculateScore.calculate_score (sliceTake s k) = ok rx)
    (hry : Aegis.CalculateScore.calculate_score (sliceDrop s k) = ok ry), r.val = rx.val + ry.val) := by
  sorry

/-- If n is even and for every k with 0 <= k < n / 2 we have s[2*k + 1] = 219 - s[2*k], then whenever the function returns a result r, r = n / 2.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_11 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (heven : s.val.length % 2 = 0)
    (hpairs : ∀ k, k < s.val.length / 2 → (s.val[2 * k + 1]!).val = 219 - (s.val[2 * k]!).val)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r) :
    r.val = ((s.val.length / 2 : Nat) : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (heven : s.val.length % 2 = 0)
    (hpairs : ∀ k, k < s.val.length / 2 → (s.val[2 * k + 1]!).val = 219 - (s.val[2 * k]!).val)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r), r.val = ((s.val.length / 2 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exist indices j and i with 0 <= j < i < n such that s[j] = 219 - s[i] and 1 <= i - j <= r.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_12 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r) (hrpos : 0 < r.val) :
    ∃ j i, j < i ∧ i < s.val.length ∧ (s.val[j]!).val = 219 - (s.val[i]!).val ∧
      1 ≤ i - j ∧ ((i - j : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r) (hrpos : 0 < r.val), ∃ j i, j < i ∧ i < s.val.length ∧ (s.val[j]!).val = 219 - (s.val[i]!).val ∧
      1 ≤ i - j ∧ ((i - j : Nat) : Int) ≤ r.val) := by
  sorry

/-- If for every k with 0 <= k < floor(n / 2) we have s[2*k + 1] = 219 - s[2*k], then whenever the function returns a result r, r = floor(n / 2).
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_13 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (hpairs : ∀ k, k < s.val.length / 2 → (s.val[2 * k + 1]!).val = 219 - (s.val[2 * k]!).val)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r) :
    r.val = ((s.val.length / 2 : Nat) : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (hpairs : ∀ k, k < s.val.length / 2 → (s.val[2 * k + 1]!).val = 219 - (s.val[2 * k]!).val)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r), r.val = ((s.val.length / 2 : Nat) : Int)) := by
  sorry

/-- For each c with 97 <= c <= 109, let P_c = {c, 219 - c}. Let I_c be the increasing list of indices i with s[i] in P_c, and let u_c be the string u_c[t] = s[I_c[t]] for 0 <= t < len(I_c). Run the same left-to-right marking process on u_c, but when a pair is formed at positions a < b in u_c, add the original distance I_c[b] - I_c[a] instead of b - a. Let r_c be the total score for this pair. If the function returns r on s, then r = sum_{c=97}^{109} r_c.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_14 (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r) :
    r.val = ((totalClassScore (codes s.val) : Nat) : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (r : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r), r.val = ((totalClassScore (codes s.val) : Nat) : Int)) := by
  sorry

/-- Let t be the byte string of length n with t[i] = f(s[i]) for every 0 <= i < n. If the function returns r on s and r' on t, then r = r'.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, 97 <= s[i] <= 122. Let f be a permutation of {97, ..., 122} such that f(219 - c) = 219 - f(c) for every c with 97 <= c <= 122. -/
theorem spec_15 (s t : Slice Std.U8) (f : Nat → Nat)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (hf_range : ∀ c, 97 ≤ c → c ≤ 122 → 97 ≤ f c ∧ f c ≤ 122)
    (hf_inj : ∀ a b, 97 ≤ a → a ≤ 122 → 97 ≤ b → b ≤ 122 → f a = f b → a = b)
    (hf_mirror : ∀ c, 97 ≤ c → c ≤ 122 → f (219 - c) = 219 - f c)
    (htlen : t.val.length = s.val.length)
    (ht : ∀ i, i < s.val.length → (t.val[i]!).val = f (s.val[i]!).val)
    (r r' : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r)
    (hr' : Aegis.CalculateScore.calculate_score t = ok r') :
    r = r' := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s t : Slice Std.U8) (f : Nat → Nat)
    (hpos : 0 < s.val.length) (hlen : s.val.length ≤ 100000)
    (hlow : ∀ i, i < s.val.length → 97 ≤ (s.val[i]!).val ∧ (s.val[i]!).val ≤ 122)
    (hf_range : ∀ c, 97 ≤ c → c ≤ 122 → 97 ≤ f c ∧ f c ≤ 122)
    (hf_inj : ∀ a b, 97 ≤ a → a ≤ 122 → 97 ≤ b → b ≤ 122 → f a = f b → a = b)
    (hf_mirror : ∀ c, 97 ≤ c → c ≤ 122 → f (219 - c) = 219 - f c)
    (htlen : t.val.length = s.val.length)
    (ht : ∀ i, i < s.val.length → (t.val[i]!).val = f (s.val[i]!).val)
    (r r' : Std.I64) (hr : Aegis.CalculateScore.calculate_score s = ok r)
    (hr' : Aegis.CalculateScore.calculate_score t = ok r'), r = r') := by
  sorry

end AegisSpec.CalculateScore
