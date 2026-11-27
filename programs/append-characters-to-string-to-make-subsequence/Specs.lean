import Aegis.AppendCharacters.Code.Funs

/-!
# Specifications of `Aegis.AppendCharacters.append_characters`

LeetCode problem `append-characters-to-string-to-make-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AppendCharacters

def isLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def allLowerBytes (s : Slice Std.U8) : Prop := ∀ b ∈ s.val, isLowerByte b

def SubseqOf (p s : List Std.U8) : Prop :=
  ∃ f : Fin p.length → Fin s.length, StrictMono f ∧ ∀ j : Fin p.length, s.get (f j) = p.get j

/-- The function returns an I64 result r (it does not fail) and r = len(t) - k, where k is the largest integer with 0 <= k <= len(t) such that the prefix of t of length k is a subsequence of s. Here the prefix of t of length k is the sequence t[0],...,t[k-1] (empty when k=0), and it is a subsequence of s when there exist indices 0 <= i_0 < i_1 < ... < i_{k-1} < len(s) with s[i_j] = t[j] for every 0 <= j < k. Thus r is the minimum number of characters that must be appended to the end of s so that t becomes a subsequence of the extended string.
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_1 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∃ r : Std.I64,
      Aegis.AppendCharacters.append_characters s t = ok r ∧
        ∃ k : Nat,
          k ≤ t.val.length ∧
            SubseqOf (t.val.take k) s.val ∧
              (∀ k' : Nat, k' ≤ t.val.length → SubseqOf (t.val.take k') s.val → k' ≤ k) ∧
                r.val = (t.val.length : Int) - (k : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∃ r : Std.I64,
      Aegis.AppendCharacters.append_characters s t = ok r ∧
        ∃ k : Nat,
          k ≤ t.val.length ∧
            SubseqOf (t.val.take k) s.val ∧
              (∀ k' : Nat, k' ≤ t.val.length → SubseqOf (t.val.take k') s.val → k' ≤ k) ∧
                r.val = (t.val.length : Int) - (k : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the call append_characters s t returns some I64 result r and does not fail, in particular without overflow, out-of-bounds access, or panic.
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_2 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∃ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∃ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r) := by
  sorry

/-- Whenever the function returns a result r, the integer r satisfies 0 <= r.
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_3 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, the integer r satisfies r <= len(t), interpreting len(t) as an integer.
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_4 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      r.val ≤ (t.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      r.val ≤ (t.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, the integer r satisfies r >= max(0, len(t) - len(s)).
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_5 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      max (0 : Int) ((t.val.length : Int) - (s.val.length : Int)) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      max (0 : Int) ((t.val.length : Int) - (s.val.length : Int)) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if t is a subsequence of s, that is, if and only if there exist indices 0 <= i_0 < i_1 < ... < i_{len(t)-1} < len(s) with s[i_j] = t[j] for every 0 <= j < len(t).
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_6 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      (r.val = 0 ↔ SubseqOf t.val s.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      (r.val = 0 ↔ SubseqOf t.val s.val)) := by
  sorry

/-- Whenever the function returns a result r, define k = len(t) - r as an integer. Then 0 <= k <= len(t), and the sequence t[0],...,t[k-1] (empty when k=0) is a subsequence of s, meaning there exist indices 0 <= i_0 < i_1 < ... < i_{k-1} < len(s) with s[i_j] = t[j] for every 0 <= j < k.
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_7 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      ∃ k : Nat,
        k ≤ t.val.length ∧
          (k : Int) = (t.val.length : Int) - r.val ∧ SubseqOf (t.val.take k) s.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      ∃ k : Nat,
        k ≤ t.val.length ∧
          (k : Int) = (t.val.length : Int) - r.val ∧ SubseqOf (t.val.take k) s.val) := by
  sorry

/-- Whenever the function returns a result r, define k = len(t) - r. Then 0 <= k <= len(t), and t is a subsequence of the concatenation of s with the suffix t[k], t[k+1], ..., t[len(t)-1]; that is, appending that suffix of length r to s makes t a subsequence.
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_8 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      ∃ k : Nat,
        k ≤ t.val.length ∧
          (k : Int) = (t.val.length : Int) - r.val ∧
            SubseqOf t.val (s.val ++ t.val.drop k) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      ∃ k : Nat,
        k ≤ t.val.length ∧
          (k : Int) = (t.val.length : Int) - r.val ∧
            SubseqOf t.val (s.val ++ t.val.drop k)) := by
  sorry

/-- Whenever the function returns a result r, for every byte array u with len(u) < r, t is not a subsequence of the concatenation of s followed by u; equivalently, there do not exist indices 0 <= i_0 < ... < i_{len(t)-1} < len(s)+len(u) selecting t[0],...,t[len(t)-1] in order from s followed by u.
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_9 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      ∀ u : Slice Std.U8,
        (u.val.length : Int) < r.val → ¬ SubseqOf t.val (s.val ++ u.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      ∀ u : Slice Std.U8,
        (u.val.length : Int) < r.val → ¬ SubseqOf t.val (s.val ++ u.val)) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 0 <= k <= len(t), if the sequence t[0],...,t[k-1] (empty for k=0) is a subsequence of s, then r <= len(t) - k.
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_10 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      ∀ k : Nat, k ≤ t.val.length → SubseqOf (t.val.take k) s.val →
        r.val ≤ (t.val.length : Int) - (k : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      ∀ k : Nat, k ≤ t.val.length → SubseqOf (t.val.take k) s.val →
        r.val ≤ (t.val.length : Int) - (k : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 0 <= k <= len(t), if the sequence t[0],...,t[k-1] (empty for k=0) is not a subsequence of s, then r > len(t) - k.
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_11 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      ∀ k : Nat, k ≤ t.val.length → ¬ SubseqOf (t.val.take k) s.val →
        (t.val.length : Int) - (k : Int) < r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∀ r : Std.I64, Aegis.AppendCharacters.append_characters s t = ok r →
      ∀ k : Nat, k ≤ t.val.length → ¬ SubseqOf (t.val.take k) s.val →
        (t.val.length : Int) - (k : Int) < r.val) := by
  sorry

/-- For every byte slice v satisfying 1 <= len(v) <= 100000, every byte of v in 97..122, and such that s is a prefix of v (len(v) >= len(s) and v[i] = s[i] for every 0 <= i < len(s)), if append_characters s t returns r_s and append_characters v t returns r_v, then r_v <= r_s.
  Preconditions: s and t are byte slices representing nonempty strings of lowercase English letters: 1 <= len(s) <= 100000, 1 <= len(t) <= 100000, every byte of s and t is in the range 97..122. -/
theorem spec_12 (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t) :
    ∀ v : Slice Std.U8,
      1 ≤ v.val.length →
        v.val.length ≤ 100000 →
          allLowerBytes v →
            List.IsPrefix s.val v.val →
              ∀ r_s r_v : Std.I64,
                Aegis.AppendCharacters.append_characters s t = ok r_s →
                  Aegis.AppendCharacters.append_characters v t = ok r_v → r_v.val ≤ r_s.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length) (hs_max : s.val.length ≤ 100000) (hs_lower : allLowerBytes s)
    (ht_len : 1 ≤ t.val.length) (ht_max : t.val.length ≤ 100000) (ht_lower : allLowerBytes t), ∀ v : Slice Std.U8,
      1 ≤ v.val.length →
        v.val.length ≤ 100000 →
          allLowerBytes v →
            List.IsPrefix s.val v.val →
              ∀ r_s r_v : Std.I64,
                Aegis.AppendCharacters.append_characters s t = ok r_s →
                  Aegis.AppendCharacters.append_characters v t = ok r_v → r_v.val ≤ r_s.val) := by
  sorry

end AegisSpec.AppendCharacters
