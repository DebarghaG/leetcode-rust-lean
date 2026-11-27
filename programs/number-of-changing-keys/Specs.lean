import Aegis.CountKeyChanges.Code.Funs

/-!
# Specifications of `Aegis.CountKeyChanges.count_key_changes`

LeetCode problem `number-of-changing-keys`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountKeyChanges

open Aegis.CountKeyChanges

def lower (c : Std.U8) : Nat :=
  if 65 ≤ c.val ∧ c.val ≤ 90 then c.val + 32 else c.val

def isAsciiLetter (c : Std.U8) : Prop :=
  (65 ≤ c.val ∧ c.val ≤ 90) ∨ (97 ≤ c.val ∧ c.val ≤ 122)

def allAsciiLetters (l : List Std.U8) : Prop :=
  ∀ i (h : i < l.length), isAsciiLetter (l.get ⟨i, h⟩)

def numKeyChanges : List Std.U8 → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if lower a = lower b then 0 else 1) + numKeyChanges (b :: rest)

def numKeySame : List Std.U8 → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if lower a = lower b then 1 else 0) + numKeySame (b :: rest)

def adjacentLowerAllEq (l : List Std.U8) : Prop :=
  ∀ i (h : i + 1 < l.length), lower (l.get ⟨i, by omega⟩) = lower (l.get ⟨i + 1, h⟩)

def existsAdjacentLowerNe (l : List Std.U8) : Prop :=
  ∃ i, ∃ (_h : i + 1 < l.length),
    lower (l.get ⟨i, by omega⟩) ≠ lower (l.get ⟨i + 1, _h⟩)

/-- Whenever the function returns a result r, r is the number of indices i with 0 <= i < len(s) - 1 and lower(s[i]) != lower(s[i+1]).
  Preconditions: Let n = len(s). 1 <= n <= 100. For every i with 0 <= i < n, s[i] is an ASCII uppercase English letter (65 <= s[i] <= 90) or an ASCII lowercase English letter (97 <= s[i] <= 122). Write lower(c) = c + 32 if 65 <= c <= 90, and lower(c) = c otherwise. -/
theorem spec_1 (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val) :
    ∀ r : Std.I64, count_key_changes s = ok r → r.val = (numKeyChanges s.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val), ∀ r : Std.I64, count_key_changes s = ok r → r.val = (numKeyChanges s.val : Int)) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, or panic) on every input satisfying the preconditions.
  Preconditions: Let n = len(s). 1 <= n <= 100. For every i with 0 <= i < n, s[i] is an ASCII uppercase English letter (65 <= s[i] <= 90) or an ASCII lowercase English letter (97 <= s[i] <= 122). Write lower(c) = c + 32 if 65 <= c <= 90, and lower(c) = c otherwise. -/
theorem spec_2 (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val) :
    ∃ r : Std.I64, count_key_changes s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val), ∃ r : Std.I64, count_key_changes s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(s) - 1.
  Preconditions: Let n = len(s). 1 <= n <= 100. For every i with 0 <= i < n, s[i] is an ASCII uppercase English letter (65 <= s[i] <= 90) or an ASCII lowercase English letter (97 <= s[i] <= 122). Write lower(c) = c + 32 if 65 <= c <= 90, and lower(c) = c otherwise. -/
theorem spec_3 (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val) :
    ∀ r : Std.I64, count_key_changes s = ok r → 0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val), ∀ r : Std.I64, count_key_changes s = ok r → 0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(s). 1 <= n <= 100. For every i with 0 <= i < n, s[i] is an ASCII uppercase English letter (65 <= s[i] <= 90) or an ASCII lowercase English letter (97 <= s[i] <= 122). Write lower(c) = c + 32 if 65 <= c <= 90, and lower(c) = c otherwise. Additionally len(s) = 1. -/
theorem spec_4 (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val) (hlen : s.val.length = 1) :
    ∀ r : Std.I64, count_key_changes s = ok r → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val) (hlen : s.val.length = 1), ∀ r : Std.I64, count_key_changes s = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = len(s) - 1.
  Preconditions: Let n = len(s). 1 <= n <= 100. For every i with 0 <= i < n, s[i] is an ASCII uppercase English letter (65 <= s[i] <= 90) or an ASCII lowercase English letter (97 <= s[i] <= 122). Write lower(c) = c + 32 if 65 <= c <= 90, and lower(c) = c otherwise. Additionally len(s) >= 2 and for every i with 0 <= i < len(s) - 1, lower(s[i]) != lower(s[i+1]). -/
theorem spec_5 (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val) (hge : 2 ≤ s.val.length)
    (hdiff : ∀ i (h : i + 1 < s.val.length),
      lower (s.val.get ⟨i, by omega⟩) ≠ lower (s.val.get ⟨i + 1, by omega⟩)) :
    ∀ r : Std.I64, count_key_changes s = ok r → r.val = (s.val.length : Int) - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val) (hge : 2 ≤ s.val.length)
    (hdiff : ∀ i (h : i + 1 < s.val.length),
      lower (s.val.get ⟨i, by omega⟩) ≠ lower (s.val.get ⟨i + 1, by omega⟩)), ∀ r : Std.I64, count_key_changes s = ok r → r.val = (s.val.length : Int) - 1) := by
  sorry

/-- Whenever the function returns r_s on s and r_t on t, r_s = r_t.
  Preconditions: Let n = len(s) = len(t). 1 <= n <= 100. Both s and t consist only of ASCII uppercase and lowercase English letters. Write lower(c) = c + 32 if 65 <= c <= 90, and lower(c) = c otherwise. For every i with 0 <= i < n, lower(s[i]) = lower(t[i]). -/
theorem spec_6 (s t : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hlen : s.val.length = t.val.length)
    (hchars_s : allAsciiLetters s.val) (hchars_t : allAsciiLetters t.val)
    (hlow : ∀ i (h : i < s.val.length),
      lower (s.val.get ⟨i, by omega⟩) = lower (t.val.get ⟨i, by omega⟩)) :
    ∀ r_s r_t : Std.I64,
      count_key_changes s = ok r_s → count_key_changes t = ok r_t → r_s = r_t := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s t : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hlen : s.val.length = t.val.length)
    (hchars_s : allAsciiLetters s.val) (hchars_t : allAsciiLetters t.val)
    (hlow : ∀ i (h : i < s.val.length),
      lower (s.val.get ⟨i, by omega⟩) = lower (t.val.get ⟨i, by omega⟩)), ∀ r_s r_t : Std.I64,
      count_key_changes s = ok r_s → count_key_changes t = ok r_t → r_s = r_t) := by
  sorry

/-- Whenever the function returns a result r, r + (the number of indices i with 0 <= i < len(s) - 1 and lower(s[i]) = lower(s[i+1])) = len(s) - 1.
  Preconditions: Let n = len(s). 1 <= n <= 100. For every i with 0 <= i < n, s[i] is an ASCII uppercase English letter (65 <= s[i] <= 90) or an ASCII lowercase English letter (97 <= s[i] <= 122). Write lower(c) = c + 32 if 65 <= c <= 90, and lower(c) = c otherwise. -/
theorem spec_7 (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val) :
    ∀ r : Std.I64,
      count_key_changes s = ok r →
        r.val + (numKeySame s.val : Int) = (s.val.length : Int) - 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val), ∀ r : Std.I64,
      count_key_changes s = ok r →
        r.val + (numKeySame s.val : Int) = (s.val.length : Int) - 1) := by
  sorry

/-- For every integer k with 1 <= k < len(s), define A to be the slice of length k with A[i] = s[i] for every 0 <= i < k, and define B to be the slice of length len(s)-k with B[j] = s[k+j] for every 0 <= j < len(s)-k. Whenever the function returns r on s, r1 on A, and r2 on B, r = r1 + r2 + (1 if lower(s[k-1]) != lower(s[k]) else 0).
  Preconditions: Let n = len(s). 1 <= n <= 100. For every i with 0 <= i < n, s[i] is an ASCII uppercase English letter (65 <= s[i] <= 90) or an ASCII lowercase English letter (97 <= s[i] <= 122). Write lower(c) = c + 32 if 65 <= c <= 90, and lower(c) = c otherwise. -/
theorem spec_8 (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : k < s.val.length)
    (A B : Slice Std.U8) (hA : A.val = s.val.take k) (hB : B.val = s.val.drop k) :
    ∀ r r1 r2 : Std.I64,
      count_key_changes s = ok r → count_key_changes A = ok r1 →
        count_key_changes B = ok r2 →
          r.val = r1.val + r2.val +
            (if lower (s.val.get ⟨k - 1, by omega⟩) ≠ lower (s.val.get ⟨k, by omega⟩)
              then (1 : Int) else 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : k < s.val.length)
    (A B : Slice Std.U8) (hA : A.val = s.val.take k) (hB : B.val = s.val.drop k), ∀ r r1 r2 : Std.I64,
      count_key_changes s = ok r → count_key_changes A = ok r1 →
        count_key_changes B = ok r2 →
          r.val = r1.val + r2.val +
            (if lower (s.val.get ⟨k - 1, by omega⟩) ≠ lower (s.val.get ⟨k, by omega⟩)
              then (1 : Int) else 0)) := by
  sorry

/-- Let rev(s) be the slice of length len(s) with rev(s)[i] = s[len(s)-1-i] for every i with 0 <= i < len(s). Whenever the function returns r on s and r_rev on rev(s), r = r_rev.
  Preconditions: Let n = len(s). 1 <= n <= 100. For every i with 0 <= i < n, s[i] is an ASCII uppercase English letter (65 <= s[i] <= 90) or an ASCII lowercase English letter (97 <= s[i] <= 122). Write lower(c) = c + 32 if 65 <= c <= 90, and lower(c) = c otherwise. -/
theorem spec_9 (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val)
    (t : Slice Std.U8) (ht : t.val = s.val.reverse) :
    ∀ r r_rev : Std.I64,
      count_key_changes s = ok r → count_key_changes t = ok r_rev → r = r_rev := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val)
    (t : Slice Std.U8) (ht : t.val = s.val.reverse), ∀ r r_rev : Std.I64,
      count_key_changes s = ok r → count_key_changes t = ok r_rev → r = r_rev) := by
  sorry

/-- Whenever the function returns a result r and r > 0, there exists an index i with 0 <= i < len(s) - 1 and lower(s[i]) != lower(s[i+1]).
  Preconditions: Let n = len(s). 1 <= n <= 100. For every i with 0 <= i < n, s[i] is an ASCII uppercase English letter (65 <= s[i] <= 90) or an ASCII lowercase English letter (97 <= s[i] <= 122). Write lower(c) = c + 32 if 65 <= c <= 90, and lower(c) = c otherwise. -/
theorem spec_10 (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val) :
    ∀ r : Std.I64, count_key_changes s = ok r → 0 < r.val → existsAdjacentLowerNe s.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val), ∀ r : Std.I64, count_key_changes s = ok r → 0 < r.val → existsAdjacentLowerNe s.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(s)-1, lower(s[i]) = lower(s[i+1]).
  Preconditions: Let n = len(s). 1 <= n <= 100. For every i with 0 <= i < n, s[i] is an ASCII uppercase English letter (65 <= s[i] <= 90) or an ASCII lowercase English letter (97 <= s[i] <= 122). Write lower(c) = c + 32 if 65 <= c <= 90, and lower(c) = c otherwise. -/
theorem spec_11 (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val) :
    ∀ r : Std.I64,
      count_key_changes s = ok r → (r.val = 0 ↔ adjacentLowerAllEq s.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100)
    (hchars : allAsciiLetters s.val), ∀ r : Std.I64,
      count_key_changes s = ok r → (r.val = 0 ↔ adjacentLowerAllEq s.val)) := by
  sorry

end AegisSpec.CountKeyChanges
