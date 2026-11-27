import Aegis.MinimizedStringLength.Code.Funs

/-!
# Specifications of `Aegis.MinimizedStringLength.minimized_string_length`

LeetCode problem `minimize-string-length`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimizedStringLength

  def bytes (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

  def occurs (c : Nat) (s : Slice Std.U8) : Prop := c ∈ bytes s

  def distinctCount (s : Slice Std.U8) : Nat := (bytes s).toFinset.card

  def allLowerASCII (s : Slice Std.U8) : Prop :=
    ∀ (i : Nat) (h : i < s.val.length),
      97 ≤ (s.val.get ⟨i, h⟩).val ∧ (s.val.get ⟨i, h⟩).val ≤ 122

  def pre (s : Slice Std.U8) : Prop :=
    1 ≤ s.val.length ∧ s.val.length ≤ 100 ∧ allLowerASCII s

  def pre99 (s : Slice Std.U8) : Prop :=
    1 ≤ s.val.length ∧ s.val.length ≤ 99 ∧ allLowerASCII s

  def extendBy (s s' : Slice Std.U8) (c : Nat) : Prop := bytes s' = bytes s ++ [c]

  def IsSubsequence (t s : Slice Std.U8) : Prop :=
    ∃ f : Fin t.val.length → Fin s.val.length,
      StrictMono f ∧ ∀ k, t.val.get k = s.val.get (f k)

  /-- The function returns a result r and r equals the number of distinct byte values occurring in s, i.e., r = |{ c : c is a byte and there exists i with 0 <= i < len(s) and s[i] = c }|.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (all characters are lowercase ASCII letters). -/
  theorem spec_1 (s : Slice Std.U8) (hpre : pre s) :
      ∃ r : Std.I64,
        Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧
          r.val = (distinctCount s : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : pre s), ∃ r : Std.I64,
          Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧
            r.val = (distinctCount s : Int)) := by
    sorry

  /-- The function returns a result r and r >= 1.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Slice Std.U8) (hpre : pre s) :
      ∃ r : Std.I64,
        Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : pre s), ∃ r : Std.I64,
          Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= len(s).
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Slice Std.U8) (hpre : pre s) :
      ∃ r : Std.I64,
        Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧
          r.val ≤ (s.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : pre s), ∃ r : Std.I64,
          Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧
            r.val ≤ (s.val.length : Int)) := by
    sorry

  /-- The function returns a result r and r <= 26.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Slice Std.U8) (hpre : pre s) :
      ∃ r : Std.I64,
        Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧ r.val ≤ 26 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : pre s), ∃ r : Std.I64,
          Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧ r.val ≤ 26) := by
    sorry

  /-- If every character in s is the same (i.e., for every i with 0 <= i < len(s), s[i] = s[0]), then the function returns a result r and r = 1.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_5 (s : Slice Std.U8) (hpre : pre s)
      (hsame : ∀ (i j : Nat) (hi : i < s.val.length) (hj : j < s.val.length),
        s.val.get ⟨i, hi⟩ = s.val.get ⟨j, hj⟩) :
      ∃ r : Std.I64,
        Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : pre s)
        (hsame : ∀ (i j : Nat) (hi : i < s.val.length) (hj : j < s.val.length),
          s.val.get ⟨i, hi⟩ = s.val.get ⟨j, hj⟩), ∃ r : Std.I64,
          Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧ r.val = 1) := by
    sorry

  /-- If all characters in s are pairwise distinct (i.e., for every i, j with 0 <= i < j < len(s), s[i] != s[j]), then the function returns a result r and r = len(s).
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_6 (s : Slice Std.U8) (hpre : pre s)
      (hdistinct : ∀ (i j : Nat) (hi : i < s.val.length) (hj : j < s.val.length),
        i < j → s.val.get ⟨i, hi⟩ ≠ s.val.get ⟨j, hj⟩) :
      ∃ r : Std.I64,
        Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧
          r.val = (s.val.length : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : pre s)
        (hdistinct : ∀ (i j : Nat) (hi : i < s.val.length) (hj : j < s.val.length),
          i < j → s.val.get ⟨i, hi⟩ ≠ s.val.get ⟨j, hj⟩), ∃ r : Std.I64,
          Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧
            r.val = (s.val.length : Int)) := by
    sorry

  /-- If every lowercase ASCII letter c with 97 <= c <= 122 occurs in s (i.e., for every such c there exists i with 0 <= i < len(s) and s[i] = c), then the function returns a result r and r = 26.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_7 (s : Slice Std.U8) (hpre : pre s)
      (hall : ∀ c : Nat, 97 ≤ c → c ≤ 122 → occurs c s) :
      ∃ r : Std.I64,
        Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧ r.val = 26 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : pre s)
        (hall : ∀ c : Nat, 97 ≤ c → c ≤ 122 → occurs c s), ∃ r : Std.I64,
          Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧ r.val = 26) := by
    sorry

  /-- For every byte array t satisfying the preconditions, if the set of characters occurring in t equals the set of characters occurring in s (i.e., for every byte c, there exists i with 0 <= i < len(t) and t[i] = c if and only if there exists j with 0 <= j < len(s) and s[j] = c), then the function returns a result r_s on s and a result r_t on t, and r_s = r_t.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_8 (s : Slice Std.U8) (hpre : pre s) :
      ∀ (t : Slice Std.U8), pre t →
        (∀ c : Nat, occurs c t ↔ occurs c s) →
          ∃ r_s r_t : Std.I64,
            Aegis.MinimizedStringLength.minimized_string_length s = ok r_s ∧
              Aegis.MinimizedStringLength.minimized_string_length t = ok r_t ∧
                r_s.val = r_t.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : pre s), ∀ (t : Slice Std.U8), pre t →
          (∀ c : Nat, occurs c t ↔ occurs c s) →
            ∃ r_s r_t : Std.I64,
              Aegis.MinimizedStringLength.minimized_string_length s = ok r_s ∧
                Aegis.MinimizedStringLength.minimized_string_length t = ok r_t ∧
                  r_s.val = r_t.val) := by
    sorry

  /-- For every nonempty byte array t satisfying the preconditions that is a subsequence of s (i.e., there exist indices 0 <= i_1 < i_2 < ... < i_{len(t)} < len(s) such that t[k] = s[i_{k+1}] for all 0 <= k < len(t)), the function returns a result r_s on s and a result r_t on t, and r_t <= r_s.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_9 (s : Slice Std.U8) (hpre : pre s) :
      ∀ (t : Slice Std.U8), pre t → 0 < t.val.length → IsSubsequence t s →
        ∃ r_s r_t : Std.I64,
          Aegis.MinimizedStringLength.minimized_string_length s = ok r_s ∧
            Aegis.MinimizedStringLength.minimized_string_length t = ok r_t ∧
              r_t.val ≤ r_s.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : pre s), ∀ (t : Slice Std.U8), pre t → 0 < t.val.length → IsSubsequence t s →
          ∃ r_s r_t : Std.I64,
            Aegis.MinimizedStringLength.minimized_string_length s = ok r_s ∧
              Aegis.MinimizedStringLength.minimized_string_length t = ok r_t ∧
                r_t.val ≤ r_s.val) := by
    sorry

  /-- The function returns a result r and there exist indices i_1, i_2, ..., i_r with 0 <= i_1 < i_2 < ... < i_r < len(s) such that the characters s[i_1], s[i_2], ..., s[i_r] are pairwise distinct and the set {s[i_1], s[i_2], ..., s[i_r]} equals the set of all characters occurring in s (i.e., for every byte c, c occurs in s if and only if c = s[i_k] for some k in {1, ..., r}).
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (all characters are lowercase ASCII letters). -/
  theorem spec_10 (s : Slice Std.U8) (hpre : pre s) :
      ∃ r : Std.I64,
        Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧
          ∃ idx : Fin r.val.toNat → Fin s.val.length,
            StrictMono idx ∧
              (∀ k l, (s.val.get (idx k)).val = (s.val.get (idx l)).val → k = l) ∧
                (∀ c : Nat, occurs c s ↔ ∃ k : Fin r.val.toNat, (s.val.get (idx k)).val = c) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : pre s), ∃ r : Std.I64,
          Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧
            ∃ idx : Fin r.val.toNat → Fin s.val.length,
              StrictMono idx ∧
                (∀ k l, (s.val.get (idx k)).val = (s.val.get (idx l)).val → k = l) ∧
                  (∀ c : Nat, occurs c s ↔ ∃ k : Fin r.val.toNat, (s.val.get (idx k)).val = c)) := by
    sorry

  /-- For every pair of nonempty byte arrays s1 and s2 satisfying the preconditions such that s = s1 ++ s2 (i.e., len(s) = len(s1) + len(s2), s[i] = s1[i] for 0 <= i < len(s1), and s[len(s1)+j] = s2[j] for 0 <= j < len(s2)), the function returns a result r on s, a result r1 on s1, and a result r2 on s2, and r <= r1 + r2.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_11 (s : Slice Std.U8) (hpre : pre s) :
      ∀ (s1 s2 : Slice Std.U8), pre s1 → pre s2 → bytes s = bytes s1 ++ bytes s2 →
        ∃ r r1 r2 : Std.I64,
          Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧
            Aegis.MinimizedStringLength.minimized_string_length s1 = ok r1 ∧
              Aegis.MinimizedStringLength.minimized_string_length s2 = ok r2 ∧
                r.val ≤ r1.val + r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : pre s), ∀ (s1 s2 : Slice Std.U8), pre s1 → pre s2 → bytes s = bytes s1 ++ bytes s2 →
          ∃ r r1 r2 : Std.I64,
            Aegis.MinimizedStringLength.minimized_string_length s = ok r ∧
              Aegis.MinimizedStringLength.minimized_string_length s1 = ok r1 ∧
                Aegis.MinimizedStringLength.minimized_string_length s2 = ok r2 ∧
                  r.val ≤ r1.val + r2.val) := by
    sorry

  end AegisSpec.MinimizedStringLength
