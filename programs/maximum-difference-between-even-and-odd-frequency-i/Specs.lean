import Aegis.MaxDifference.Code.Funs

/-!
# Specifications of `Aegis.MaxDifference.max_difference`

LeetCode problem `maximum-difference-between-even-and-odd-frequency-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxDifference

def IsLower (c : Nat) : Prop := 97 ≤ c ∧ c ≤ 122

def cnt (l : List Std.U8) (x : Nat) : Nat := l.countP (fun b => b.val == x)

def AllLower (l : List Std.U8) : Prop := ∀ b ∈ l, IsLower b.val

def HasOdd (l : List Std.U8) : Prop := ∃ c, IsLower c ∧ Odd (cnt l c)

def HasPosEven (l : List Std.U8) : Prop :=
  ∃ d, IsLower d ∧ 0 < cnt l d ∧ Even (cnt l d)

def oddCounts (l : List Std.U8) : Set Nat :=
  {n | ∃ c, IsLower c ∧ cnt l c = n ∧ Odd n}

def posEvenCounts (l : List Std.U8) : Set Nat :=
  {n | ∃ d, IsLower d ∧ cnt l d = n ∧ 0 < n ∧ Even n}

def diffSet (l : List Std.U8) : Set Int :=
  {m | ∃ c d, IsLower c ∧ IsLower d ∧ Odd (cnt l c) ∧ 0 < cnt l d ∧ Even (cnt l d) ∧
    m = (cnt l c : Int) - (cnt l d : Int)}

/-- The function returns a result r, and r viewed as a mathematical integer is the maximum of the set { cnt(s,c) - cnt(s,d) | 97 <= c <= 122, cnt(s,c) is odd, 97 <= d <= 122, cnt(s,d) > 0, cnt(s,d) is even }.
  Preconditions: Let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Assume 3 <= len(s) <= 100; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; there exists a byte c with 97 <= c <= 122 and cnt(s,c) odd; and there exists a byte d with 97 <= d <= 122, cnt(s,d) > 0, and cnt(s,d) even. -/
theorem spec_1 (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val) :
    ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      IsGreatest (diffSet s.val) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val), ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      IsGreatest (diffSet s.val) r.val) := by
  sorry

/-- The function returns a result r, and there exist bytes c and d with 97 <= c <= 122 and 97 <= d <= 122 such that cnt(s,c) is odd, cnt(s,d) > 0 and cnt(s,d) is even, and r = cnt(s,c) - cnt(s,d).
  Preconditions: Let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Assume 3 <= len(s) <= 100; all bytes of s are in 97..122; some letter has odd cnt; and some letter has positive even cnt. -/
theorem spec_2 (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val) :
    ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      ∃ c d : Nat, IsLower c ∧ IsLower d ∧ Odd (cnt s.val c) ∧
        0 < cnt s.val d ∧ Even (cnt s.val d) ∧
        r.val = (cnt s.val c : Int) - (cnt s.val d : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val), ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      ∃ c d : Nat, IsLower c ∧ IsLower d ∧ Odd (cnt s.val c) ∧
        0 < cnt s.val d ∧ Even (cnt s.val d) ∧
        r.val = (cnt s.val c : Int) - (cnt s.val d : Int)) := by
  sorry

/-- The function returns a result r, and for every byte c with 97 <= c <= 122 and cnt(s,c) odd, and for every byte d with 97 <= d <= 122, cnt(s,d) > 0, and cnt(s,d) even, we have cnt(s,c) - cnt(s,d) <= r.
  Preconditions: Let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Assume 3 <= len(s) <= 100; all bytes of s are in 97..122; some letter has odd cnt; and some letter has positive even cnt. -/
theorem spec_3 (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val) :
    ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      ∀ c d : Nat, IsLower c → Odd (cnt s.val c) →
        IsLower d → 0 < cnt s.val d → Even (cnt s.val d) →
        (cnt s.val c : Int) - (cnt s.val d : Int) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val), ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      ∀ c d : Nat, IsLower c → Odd (cnt s.val c) →
        IsLower d → 0 < cnt s.val d → Even (cnt s.val d) →
        (cnt s.val c : Int) - (cnt s.val d : Int) ≤ r.val) := by
  sorry

/-- The function returns a result r, and r = O - E, where O = max { cnt(s,c) | 97 <= c <= 122 and cnt(s,c) is odd } and E = min { cnt(s,d) | 97 <= d <= 122, cnt(s,d) > 0, and cnt(s,d) is even }.
  Preconditions: Let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Assume 3 <= len(s) <= 100; all bytes of s are in 97..122; some letter has odd cnt; and some letter has positive even cnt. -/
theorem spec_4 (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val) :
    ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      ∃ O E : Nat, IsGreatest (oddCounts s.val) O ∧ IsLeast (posEvenCounts s.val) E ∧
        r.val = (O : Int) - (E : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val), ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      ∃ O E : Nat, IsGreatest (oddCounts s.val) O ∧ IsLeast (posEvenCounts s.val) E ∧
        r.val = (O : Int) - (E : Int)) := by
  sorry

/-- For every such s, evaluation of max_difference(s) returns a result r; it does not fail, panic, go out of bounds, or overflow.
  Preconditions: Let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Assume 3 <= len(s) <= 100; all bytes of s are in 97..122; some letter has odd cnt; and some letter has positive even cnt. -/
theorem spec_5 (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val) :
    ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val), ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r) := by
  sorry

/-- The function returns a result r, and r <= 95.
  Preconditions: Let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Assume 3 <= len(s) <= 100; all bytes of s are in 97..122; some letter has odd cnt; and some letter has positive even cnt. -/
theorem spec_6 (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val) :
    ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧ r.val ≤ 95 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val), ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧ r.val ≤ 95) := by
  sorry

/-- The function returns a result r, and r >= -97.
  Preconditions: Let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Assume 3 <= len(s) <= 100; all bytes of s are in 97..122; some letter has odd cnt; and some letter has positive even cnt. -/
theorem spec_7 (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val) :
    ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧ -97 ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val), ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧ -97 ≤ r.val) := by
  sorry

/-- The function returns a result r, and r is odd as a mathematical integer: there exists an integer k such that r = 2*k + 1.
  Preconditions: Let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Assume 3 <= len(s) <= 100; all bytes of s are in 97..122; some letter has odd cnt; and some letter has positive even cnt. -/
theorem spec_8 (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val) :
    ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      ∃ k : Int, r.val = 2 * k + 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val), ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      ∃ k : Int, r.val = 2 * k + 1) := by
  sorry

/-- Whenever max_difference(s) returns r and max_difference(t) returns r_t, we have r_t = r.
  Preconditions: Let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Assume s satisfies 3 <= len(s) <= 100; all bytes of s are in 97..122; some letter has odd cnt; and some letter has positive even cnt. Let t be any byte slice satisfying the same assumptions and satisfying cnt(t,c) = cnt(s,c) for every byte c with 97 <= c <= 122. -/
theorem spec_9 (s t : Slice Std.U8)
    (hlen_low_s : 3 ≤ s.val.length) (hlen_high_s : s.val.length ≤ 100)
    (hall_s : AllLower s.val) (hodd_s : HasOdd s.val) (heven_s : HasPosEven s.val)
    (hlen_low_t : 3 ≤ t.val.length) (hlen_high_t : t.val.length ≤ 100)
    (hall_t : AllLower t.val) (hodd_t : HasOdd t.val) (heven_t : HasPosEven t.val)
    (hcnt : ∀ c : Nat, IsLower c → cnt t.val c = cnt s.val c) :
    ∀ r r_t : Std.I64, Aegis.MaxDifference.max_difference s = ok r →
      Aegis.MaxDifference.max_difference t = ok r_t → r_t = r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hlen_low_s : 3 ≤ s.val.length) (hlen_high_s : s.val.length ≤ 100)
    (hall_s : AllLower s.val) (hodd_s : HasOdd s.val) (heven_s : HasPosEven s.val)
    (hlen_low_t : 3 ≤ t.val.length) (hlen_high_t : t.val.length ≤ 100)
    (hall_t : AllLower t.val) (hodd_t : HasOdd t.val) (heven_t : HasPosEven t.val)
    (hcnt : ∀ c : Nat, IsLower c → cnt t.val c = cnt s.val c), ∀ r r_t : Std.I64, Aegis.MaxDifference.max_difference s = ok r →
      Aegis.MaxDifference.max_difference t = ok r_t → r_t = r) := by
  sorry

/-- The function returns a result r, and for every byte c with 97 <= c <= 122 and cnt(s,c) odd, and every byte d with 97 <= d <= 122, cnt(s,d) > 0, and cnt(s,d) even, if r = cnt(s,c) - cnt(s,d), then cnt(s,c) = O and cnt(s,d) = E.
  Preconditions: Let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Assume 3 <= len(s) <= 100; all bytes of s are in 97..122; some letter has odd cnt; and some letter has positive even cnt. Define O = max { cnt(s,c) | 97 <= c <= 122 and cnt(s,c) is odd } and E = min { cnt(s,d) | 97 <= d <= 122, cnt(s,d) > 0, and cnt(s,d) is even }. -/
theorem spec_10 (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val) :
    ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      ∀ c d : Nat, IsLower c → Odd (cnt s.val c) →
        IsLower d → 0 < cnt s.val d → Even (cnt s.val d) →
        r.val = (cnt s.val c : Int) - (cnt s.val d : Int) →
        IsGreatest (oddCounts s.val) (cnt s.val c) ∧
          IsLeast (posEvenCounts s.val) (cnt s.val d) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 3 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hall : AllLower s.val) (hodd : HasOdd s.val) (heven : HasPosEven s.val), ∃ r : Std.I64, Aegis.MaxDifference.max_difference s = ok r ∧
      ∀ c d : Nat, IsLower c → Odd (cnt s.val c) →
        IsLower d → 0 < cnt s.val d → Even (cnt s.val d) →
        r.val = (cnt s.val c : Int) - (cnt s.val d : Int) →
        IsGreatest (oddCounts s.val) (cnt s.val c) ∧
          IsLeast (posEvenCounts s.val) (cnt s.val d)) := by
  sorry

end AegisSpec.MaxDifference
