import Aegis.DiStringMatch.Code.Funs

/-!
# Specifications of `Aegis.DiStringMatch.di_string_match`

LeetCode problem `di-string-match`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DiStringMatch

open Aegis.DiStringMatch

def inGet (s : Slice Std.U8) (i : Nat) : Nat :=
  ((s.val[i]?).map (fun v => v.val)).getD 0

def outGet (r : alloc.vec.Vec Std.I64) (j : Nat) : Int :=
  ((r.val[j]?).map (fun v => v.val)).getD 0

def ascii_I : Nat := 73

def ascii_D : Nat := 68

/-- The function returns a result r such that: (a) len(r) = n + 1; (b) for every integer v with 0 <= v <= n, there is exactly one index j with 0 <= j <= n and r[j] = v; (c) for every i with 0 <= i < n, if s[i] = 73 then r[i] < r[i+1], and if s[i] = 68 then r[i] > r[i+1].
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] = 73 (ASCII 'I') or s[i] = 68 (ASCII 'D'). -/
theorem spec_1 (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D) :
    ∃ r, di_string_match s = ok r ∧
      r.val.length = s.val.length + 1 ∧
      (∀ v : Int, 0 ≤ v → v ≤ (s.val.length : Int) →
        ∃! j : Nat, j ≤ s.val.length ∧ outGet r j = v) ∧
      (∀ i, i < s.val.length → inGet s i = ascii_I → outGet r i < outGet r (i + 1)) ∧
      (∀ i, i < s.val.length → inGet s i = ascii_D → outGet r i > outGet r (i + 1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D), ∃ r, di_string_match s = ok r ∧
      r.val.length = s.val.length + 1 ∧
      (∀ v : Int, 0 ≤ v → v ≤ (s.val.length : Int) →
        ∃! j : Nat, j ≤ s.val.length ∧ outGet r j = v) ∧
      (∀ i, i < s.val.length → inGet s i = ascii_I → outGet r i < outGet r (i + 1)) ∧
      (∀ i, i < s.val.length → inGet s i = ascii_D → outGet r i > outGet r (i + 1))) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r; it does not fail due to arithmetic overflow, out-of-bounds indexing, or panic.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] = 73 (ASCII 'I') or s[i] = 68 (ASCII 'D'). -/
theorem spec_2 (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D) :
    ∃ r, Aegis.DiStringMatch.di_string_match s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D), ∃ r, Aegis.DiStringMatch.di_string_match s = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(s) + 1.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] = 73 (ASCII 'I') or s[i] = 68 (ASCII 'D'). -/
theorem spec_3 (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D) :
    ∀ r, di_string_match s = ok r →
      r.val.length = s.val.length + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D), ∀ r, di_string_match s = ok r →
      r.val.length = s.val.length + 1) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), 0 <= r[j] <= len(s).
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] = 73 (ASCII 'I') or s[i] = 68 (ASCII 'D'). -/
theorem spec_4 (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D) :
    ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ j, j < r.val.length → 0 ≤ outGet r j ∧ outGet r j ≤ (s.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D), ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ j, j < r.val.length → 0 ≤ outGet r j ∧ outGet r j ≤ (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every pair of indices j,k with 0 <= j < k < len(r), r[j] != r[k].
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] = 73 (ASCII 'I') or s[i] = 68 (ASCII 'D'). -/
theorem spec_5 (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D) :
    ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ j k, j < k → k < r.val.length → outGet r j ≠ outGet r k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D), ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ j k, j < k → k < r.val.length → outGet r j ≠ outGet r k) := by
  sorry

/-- Whenever the function returns a result r, for every integer v with 0 <= v <= len(s), there exists an index j with 0 <= j < len(r) and r[j] = v.
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] = 73 (ASCII 'I') or s[i] = 68 (ASCII 'D'). -/
theorem spec_6 (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D) :
    ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ v : Int, 0 ≤ v → v ≤ (s.val.length : Int) →
        ∃ j, j < r.val.length ∧ outGet r j = v := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D), ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ v : Int, 0 ≤ v → v ≤ (s.val.length : Int) →
        ∃ j, j < r.val.length ∧ outGet r j = v) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s) and i + 1 < len(r), if s[i] = 73 (ASCII 'I') then r[i] < r[i+1].
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] = 73 (ASCII 'I') or s[i] = 68 (ASCII 'D'). -/
theorem spec_7 (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D) :
    ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ i, i < s.val.length → i + 1 < r.val.length → inGet s i = ascii_I →
        outGet r i < outGet r (i + 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D), ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ i, i < s.val.length → i + 1 < r.val.length → inGet s i = ascii_I →
        outGet r i < outGet r (i + 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s) and i + 1 < len(r), if s[i] = 68 (ASCII 'D') then r[i] > r[i+1].
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] = 73 (ASCII 'I') or s[i] = 68 (ASCII 'D'). -/
theorem spec_8 (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D) :
    ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ i, i < s.val.length → i + 1 < r.val.length → inGet s i = ascii_D →
        outGet r i > outGet r (i + 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D), ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ i, i < s.val.length → i + 1 < r.val.length → inGet s i = ascii_D →
        outGet r i > outGet r (i + 1)) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r) and j <= len(s), if r[j] = 0 then: (if j > 0 then s[j-1] = 68 (ASCII 'D')), and (if j < len(s) then s[j] = 73 (ASCII 'I')).
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] = 73 (ASCII 'I') or s[i] = 68 (ASCII 'D'). -/
theorem spec_9 (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D) :
    ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ j, j < r.val.length → j ≤ s.val.length → outGet r j = 0 →
        (0 < j → inGet s (j - 1) = ascii_D) ∧ (j < s.val.length → inGet s j = ascii_I) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D), ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ j, j < r.val.length → j ≤ s.val.length → outGet r j = 0 →
        (0 < j → inGet s (j - 1) = ascii_D) ∧ (j < s.val.length → inGet s j = ascii_I)) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r) and j <= len(s), if r[j] = len(s) then: (if j > 0 then s[j-1] = 73 (ASCII 'I')), and (if j < len(s) then s[j] = 68 (ASCII 'D')).
  Preconditions: Let n = len(s). 1 <= n <= 100000, and for every i with 0 <= i < n, s[i] = 73 (ASCII 'I') or s[i] = 68 (ASCII 'D'). -/
theorem spec_10 (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D) :
    ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ j, j < r.val.length → j ≤ s.val.length → outGet r j = (s.val.length : Int) →
        (0 < j → inGet s (j - 1) = ascii_I) ∧ (j < s.val.length → inGet s j = ascii_D) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (hlo : 1 ≤ s.val.length)
    (hhi : s.val.length ≤ 100000)
    (hchars : ∀ i, i < s.val.length → inGet s i = ascii_I ∨ inGet s i = ascii_D), ∀ r, Aegis.DiStringMatch.di_string_match s = ok r →
      ∀ j, j < r.val.length → j ≤ s.val.length → outGet r j = (s.val.length : Int) →
        (0 < j → inGet s (j - 1) = ascii_I) ∧ (j < s.val.length → inGet s j = ascii_D)) := by
  sorry

end AegisSpec.DiStringMatch
