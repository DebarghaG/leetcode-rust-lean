import Aegis.CheckString.Code.Funs

/-!
# Specifications of `Aegis.CheckString.check_string`

LeetCode problem `check-if-all-as-appears-before-all-bs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CheckString

  def lastA (s : Slice Std.U8) : Int :=
    match s.val.reverse.findIdx? (fun x => decide (x.val = 97)) with
    | some k => (s.val.length : Int) - 1 - (k : Int)
    | none => -1

  def firstB (s : Slice Std.U8) : Int :=
    match s.val.findIdx? (fun x => decide (x.val = 98)) with
    | some k => (k : Int)
    | none => (s.val.length : Int)

  /-- Whenever check_string(s) returns a result r, r = true if and only if for every i and every j with 0 <= i < len(s) and 0 <= j < len(s), if s[i] = 97 ('a') and s[j] = 98 ('b'), then i < j. Equivalently, r = false if and only if there exist i and j with 0 <= i < j < len(s), s[i] = 98 ('b'), and s[j] = 97 ('a').
    Preconditions: len(s) >= 1, len(s) <= 100, and for every i with 0 <= i < len(s), s[i] = 97 ('a') or s[i] = 98 ('b'). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98) :
      ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
        (r = true ↔ ∀ (i j : ℕ) (hi : i < s.val.length) (hj : j < s.val.length),
          s.val[i].val = 97 → s.val[j].val = 98 → i < j) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98), ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
          (r = true ↔ ∀ (i j : ℕ) (hi : i < s.val.length) (hj : j < s.val.length),
            s.val[i].val = 97 → s.val[j].val = 98 → i < j)) := by
    sorry

  /-- For every s satisfying the preconditions, check_string(s) returns a result r; it does not fail, panic, or overflow. The returned r is always a Boolean value.
    Preconditions: len(s) >= 1, len(s) <= 100, and for every i with 0 <= i < len(s), s[i] = 97 ('a') or s[i] = 98 ('b'). -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98) :
      ∃ (r : Bool), Aegis.CheckString.check_string s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98), ∃ (r : Bool), Aegis.CheckString.check_string s = ok r) := by
    sorry

  /-- Whenever check_string(s) returns a result r, r = true if and only if for every i and j with 0 <= i < j < len(s), s[i] <= s[j] as numeric byte values. Since the only allowed bytes are 97 ('a') and 98 ('b'), this says s is nondecreasing.
    Preconditions: len(s) >= 1, len(s) <= 100, and for every i with 0 <= i < len(s), s[i] = 97 ('a') or s[i] = 98 ('b'). -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98) :
      ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
        (r = true ↔ ∀ (i j : ℕ) (hij : i < j) (hj : j < s.val.length),
          s.val[i].val ≤ s.val[j].val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98), ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
          (r = true ↔ ∀ (i j : ℕ) (hij : i < j) (hj : j < s.val.length),
            s.val[i].val ≤ s.val[j].val)) := by
    sorry

  /-- Whenever check_string(s) returns a result r, r = true if and only if for every i with 0 <= i < len(s) - 1, it is not the case that s[i] = 98 ('b') and s[i+1] = 97 ('a').
    Preconditions: len(s) >= 1, len(s) <= 100, and for every i with 0 <= i < len(s), s[i] = 97 ('a') or s[i] = 98 ('b'). -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98) :
      ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
        (r = true ↔ ∀ (i : ℕ) (hi : i < s.val.length - 1),
          ¬ (s.val[i].val = 98 ∧ s.val[i + 1].val = 97)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98), ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
          (r = true ↔ ∀ (i : ℕ) (hi : i < s.val.length - 1),
            ¬ (s.val[i].val = 98 ∧ s.val[i + 1].val = 97))) := by
    sorry

  /-- Whenever check_string(s) returns a result r, r = true if and only if there exists an integer k with 0 <= k <= len(s) such that (for every i with 0 <= i < k, s[i] = 97 ('a')) and (for every i with k <= i < len(s), s[i] = 98 ('b')).
    Preconditions: len(s) >= 1, len(s) <= 100, and for every i with 0 <= i < len(s), s[i] = 97 ('a') or s[i] = 98 ('b'). -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98) :
      ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
        (r = true ↔ ∃ (k : ℕ), k ≤ s.val.length ∧
          (∀ (i : ℕ) (hi : i < k) (hlen : i < s.val.length), s.val[i].val = 97) ∧
          (∀ (i : ℕ) (h1 : k ≤ i) (h2 : i < s.val.length), s.val[i].val = 98)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98), ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
          (r = true ↔ ∃ (k : ℕ), k ≤ s.val.length ∧
            (∀ (i : ℕ) (hi : i < k) (hlen : i < s.val.length), s.val[i].val = 97) ∧
            (∀ (i : ℕ) (h1 : k ≤ i) (h2 : i < s.val.length), s.val[i].val = 98))) := by
    sorry

  /-- Whenever check_string(s) returns a result r, r = true if and only if lastA < firstB, where lastA is the largest index i with 0 <= i < len(s) and s[i] = 97 ('a'), or lastA = -1 if there is no such index; and firstB is the smallest index i with 0 <= i < len(s) and s[i] = 98 ('b'), or firstB = len(s) if there is no such index.
    Preconditions: len(s) >= 1, len(s) <= 100, and for every i with 0 <= i < len(s), s[i] = 97 ('a') or s[i] = 98 ('b'). -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98) :
      ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
        (r = true ↔ lastA s < firstB s) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98), ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
          (r = true ↔ lastA s < firstB s)) := by
    sorry

  /-- Whenever check_string(s) returns a result r, r = true if and only if for every i with 0 <= i < len(s) and s[i] = 97 ('a'), every j with 0 <= j < i satisfies s[j] = 97 ('a').
    Preconditions: len(s) >= 1, len(s) <= 100, and for every i with 0 <= i < len(s), s[i] = 97 ('a') or s[i] = 98 ('b'). -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98) :
      ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
        (r = true ↔ ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 →
          ∀ (j : ℕ) (hj : j < i), s.val[j].val = 97) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98), ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
          (r = true ↔ ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 →
            ∀ (j : ℕ) (hj : j < i), s.val[j].val = 97)) := by
    sorry

  /-- Whenever check_string(s) returns a result r, r = true if and only if for every i with 0 <= i < len(s) and s[i] = 98 ('b'), every j with i < j < len(s) satisfies s[j] = 98 ('b').
    Preconditions: len(s) >= 1, len(s) <= 100, and for every i with 0 <= i < len(s), s[i] = 97 ('a') or s[i] = 98 ('b'). -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98) :
      ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
        (r = true ↔ ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 98 →
          ∀ (j : ℕ) (hij : i < j) (hj : j < s.val.length), s.val[j].val = 98) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hab : ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 97 ∨ s.val[i].val = 98), ∀ (r : Bool), Aegis.CheckString.check_string s = ok r →
          (r = true ↔ ∀ (i : ℕ) (hi : i < s.val.length), s.val[i].val = 98 →
            ∀ (j : ℕ) (hij : i < j) (hj : j < s.val.length), s.val[j].val = 98)) := by
    sorry

  end AegisSpec.CheckString
