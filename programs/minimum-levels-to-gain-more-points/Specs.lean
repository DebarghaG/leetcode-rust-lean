import Aegis.MinimumLevels.Code.Funs

/-!
# Specifications of `Aegis.MinimumLevels.minimum_levels`

LeetCode problem `minimum-levels-to-gain-more-points`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumLevels

def weight (x : Std.I64) : Int := if x.val = 1 then 1 else -1

def W (l : List Std.I64) (a b : Nat) : Int :=
  (((l.drop a).take (b - a)).map weight).sum

def A (l : List Std.I64) (k : Nat) : Int := W l 0 k

def B (l : List Std.I64) (k : Nat) : Int := W l k l.length

def S (l : List Std.I64) : Int := W l 0 l.length

def Ai (l : List Std.I64) (k : Int) : Int := A l k.toNat

def Bi (l : List Std.I64) (k : Int) : Int := B l k.toNat

/-- Whenever minimum_levels returns a result r, r = -1 if and only if there is no integer k with 1 <= k <= n-1 and A(k) > B(k); and if such a k exists, then r is the least such k, so 1 <= r <= n-1, A(r) > B(r), and A(j) <= B(j) for every j with 1 <= j < r.
  Preconditions: Let n = len(possible). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, possible[i] is either 0 or 1. For 0 <= a <= b <= n let W(a,b) = sum over i from a to b-1 of (1 if possible[i] = 1 else -1). For 1 <= k <= n-1 let A(k) = W(0,k) and B(k) = W(k,n). Let S = W(0,n). -/
theorem spec_1 (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1) :
    ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      ((r.val = -1 ↔
          ¬ ∃ k : Int, 1 ≤ k ∧ k ≤ (possible.val.length : Int) - 1 ∧
            Ai possible.val k > Bi possible.val k) ∧
        ((∃ k : Int, 1 ≤ k ∧ k ≤ (possible.val.length : Int) - 1 ∧
            Ai possible.val k > Bi possible.val k) →
          1 ≤ r.val ∧ r.val ≤ (possible.val.length : Int) - 1 ∧
            Ai possible.val r.val > Bi possible.val r.val ∧
            ∀ j : Int, 1 ≤ j → j < r.val → Ai possible.val j ≤ Bi possible.val j)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1), ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      ((r.val = -1 ↔
          ¬ ∃ k : Int, 1 ≤ k ∧ k ≤ (possible.val.length : Int) - 1 ∧
            Ai possible.val k > Bi possible.val k) ∧
        ((∃ k : Int, 1 ≤ k ∧ k ≤ (possible.val.length : Int) - 1 ∧
            Ai possible.val k > Bi possible.val k) →
          1 ≤ r.val ∧ r.val ≤ (possible.val.length : Int) - 1 ∧
            Ai possible.val r.val > Bi possible.val r.val ∧
            ∀ j : Int, 1 ≤ j → j < r.val → Ai possible.val j ≤ Bi possible.val j))) := by
  sorry

/-- For every possible satisfying the preconditions, minimum_levels returns a result r; it does not fail, overflow, or panic.
  Preconditions: Let n = len(possible). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, possible[i] is either 0 or 1. -/
theorem spec_2 (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1) :
    ∃ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1), ∃ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r) := by
  sorry

/-- Whenever minimum_levels returns a result r, either r = -1 or 1 <= r <= n-1.
  Preconditions: Let n = len(possible). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, possible[i] is either 0 or 1. -/
theorem spec_3 (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1) :
    ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (possible.val.length : Int) - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1), ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (possible.val.length : Int) - 1)) := by
  sorry

/-- Whenever minimum_levels returns a result r with r != -1, r is a winning split: 1 <= r <= n-1 and A(r) > B(r).
  Preconditions: Let n = len(possible). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, possible[i] is either 0 or 1. Define A(k) = sum over i from 0 to k-1 of (1 if possible[i] = 1 else -1), and B(k) = sum over i from k to n-1 of (1 if possible[i] = 1 else -1). -/
theorem spec_4 (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1) :
    ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val ≠ -1 →
        1 ≤ r.val ∧ r.val ≤ (possible.val.length : Int) - 1 ∧
          Ai possible.val r.val > Bi possible.val r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1), ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val ≠ -1 →
        1 ≤ r.val ∧ r.val ≤ (possible.val.length : Int) - 1 ∧
          Ai possible.val r.val > Bi possible.val r.val) := by
  sorry

/-- Whenever minimum_levels returns a result r with r != -1, no smaller valid split is winning: for every j with 1 <= j < r, A(j) <= B(j).
  Preconditions: Let n = len(possible). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, possible[i] is either 0 or 1. Define A(k) = sum over i from 0 to k-1 of (1 if possible[i] = 1 else -1), and B(k) = sum over i from k to n-1 of (1 if possible[i] = 1 else -1). -/
theorem spec_5 (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1) :
    ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val ≠ -1 →
        ∀ j : Int, 1 ≤ j → j < r.val → Ai possible.val j ≤ Bi possible.val j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1), ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val ≠ -1 →
        ∀ j : Int, 1 ≤ j → j < r.val → Ai possible.val j ≤ Bi possible.val j) := by
  sorry

/-- Whenever minimum_levels returns -1, no valid split is winning: for every k with 1 <= k <= n-1, A(k) <= B(k).
  Preconditions: Let n = len(possible). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, possible[i] is either 0 or 1. Define A(k) = sum over i from 0 to k-1 of (1 if possible[i] = 1 else -1), and B(k) = sum over i from k to n-1 of (1 if possible[i] = 1 else -1). -/
theorem spec_6 (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1) :
    ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val = -1 →
        ∀ k : Int, 1 ≤ k → k ≤ (possible.val.length : Int) - 1 →
          Ai possible.val k ≤ Bi possible.val k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1), ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val = -1 →
        ∀ k : Int, 1 ≤ k → k ≤ (possible.val.length : Int) - 1 →
          Ai possible.val k ≤ Bi possible.val k) := by
  sorry

/-- Whenever minimum_levels returns a result r with r != -1, 2*r > S.
  Preconditions: Let n = len(possible). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, possible[i] is either 0 or 1. For 1 <= k <= n-1 let A(k) = sum over i from 0 to k-1 of (1 if possible[i] = 1 else -1), and let S = sum over i from 0 to n-1 of (1 if possible[i] = 1 else -1). -/
theorem spec_7 (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1) :
    ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val ≠ -1 → 2 * r.val > S possible.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1), ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val ≠ -1 → 2 * r.val > S possible.val) := by
  sorry

/-- Whenever minimum_levels returns a result r, r = 1 if and only if A(1) > B(1).
  Preconditions: Let n = len(possible). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, possible[i] is either 0 or 1. Define A(1) = 1 if possible[0] = 1 else -1, and B(1) = sum over i from 1 to n-1 of (1 if possible[i] = 1 else -1). -/
theorem spec_8 (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1) :
    ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      (r.val = 1 ↔ Ai possible.val 1 > Bi possible.val 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1), ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      (r.val = 1 ↔ Ai possible.val 1 > Bi possible.val 1)) := by
  sorry

/-- Whenever minimum_levels returns a result r, r = -1 if n = 2, and r = floor(n/2)+1 if n >= 3.
  Preconditions: Let n = len(possible). Assume 2 <= n <= 100000 and possible[i] = 1 for every i with 0 <= i < n. -/
theorem spec_9 (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hones : ∀ (i : Nat) (hi : i < possible.val.length), possible.val[i].val = 1) :
    ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      (possible.val.length = 2 → r.val = -1) ∧
        (3 ≤ possible.val.length →
          r.val = ((possible.val.length / 2 : Nat) : Int) + 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hones : ∀ (i : Nat) (hi : i < possible.val.length), possible.val[i].val = 1), ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      (possible.val.length = 2 → r.val = -1) ∧
        (3 ≤ possible.val.length →
          r.val = ((possible.val.length / 2 : Nat) : Int) + 1)) := by
  sorry

/-- Whenever minimum_levels returns a result r, r = -1 if n = 2, and r = 1 if n >= 3.
  Preconditions: Let n = len(possible). Assume 2 <= n <= 100000 and possible[i] = 0 for every i with 0 <= i < n. -/
theorem spec_10 (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hzeros : ∀ (i : Nat) (hi : i < possible.val.length), possible.val[i].val = 0) :
    ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      (possible.val.length = 2 → r.val = -1) ∧
        (3 ≤ possible.val.length → r.val = 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hzeros : ∀ (i : Nat) (hi : i < possible.val.length), possible.val[i].val = 0), ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      (possible.val.length = 2 → r.val = -1) ∧
        (3 ≤ possible.val.length → r.val = 1)) := by
  sorry

/-- Whenever minimum_levels returns a result r with r != -1, 2*A(r) > S.
  Preconditions: Let n = len(possible). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, possible[i] is either 0 or 1. For 1 <= k <= n-1 let A(k) = sum over i from 0 to k-1 of (1 if possible[i] = 1 else -1), and let S = sum over i from 0 to n-1 of (1 if possible[i] = 1 else -1). -/
theorem spec_11 (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1) :
    ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val ≠ -1 → 2 * Ai possible.val r.val > S possible.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (possible : Slice Std.I64)
    (hn_lo : 2 ≤ possible.val.length)
    (hn_hi : possible.val.length ≤ 100000)
    (hbits : ∀ (i : Nat) (hi : i < possible.val.length),
      possible.val[i].val = 0 ∨ possible.val[i].val = 1), ∀ r : Std.I64, Aegis.MinimumLevels.minimum_levels possible = ok r →
      r.val ≠ -1 → 2 * Ai possible.val r.val > S possible.val) := by
  sorry

end AegisSpec.MinimumLevels
