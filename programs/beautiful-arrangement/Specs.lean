import Aegis.CountArrangement.Code.Funs

/-!
# Specifications of `Aegis.CountArrangement.count_arrangement`

LeetCode problem `beautiful-arrangement`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountArrangement

  def rangeFromOne (n : Nat) : List Nat := (List.range n).map (fun k => k + 1)

  def IsArrangement (n : Nat) (perm : List Nat) : Prop :=
    perm.length = n ∧
    perm.Nodup ∧
    ∀ i : Fin n,
      perm.getD i.val 0 ≠ 0 ∧ perm.getD i.val 0 ≤ n ∧
        (perm.getD i.val 0 ∣ (i.val + 1) ∨ (i.val + 1) ∣ perm.getD i.val 0)

  instance (n : Nat) (perm : List Nat) : Decidable (IsArrangement n perm) := by
    unfold IsArrangement
    infer_instance

  def arrangementCount (n : Nat) : Nat :=
    ((rangeFromOne n).permutations.filter (fun perm => decide (IsArrangement n perm))).length

  def divisorCount (n : Nat) : Nat :=
    (rangeFromOne n).countP (fun d => decide (d ∣ n))

  /-- The function returns a result r, and r is the number of permutations perm of the integers 1,2,...,n such that perm is a sequence of length n, indexed from 1 to n, whose entries are exactly 1,2,...,n each once, and for every i with 1 <= i <= n, either perm[i] is divisible by i or i is divisible by perm[i]. Here divisibility means exact integer divisibility.
    Preconditions: n is an i64 with 1 <= n <= 15. -/
  theorem spec_1 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 15) :
      ∃ r : Std.I64,
        Aegis.CountArrangement.count_arrangement n = ok r ∧
          r.val = (arrangementCount n.val.toNat : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 15), ∃ r : Std.I64,
          Aegis.CountArrangement.count_arrangement n = ok r ∧
            r.val = (arrangementCount n.val.toNat : ℤ)) := by
    sorry

  /-- The function returns a result r rather than failing (no overflow, panic, or out-of-bounds condition occurs).
    Preconditions: 1 <= n <= 15. -/
  theorem spec_2 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 15) :
      ∃ r : Std.I64, Aegis.CountArrangement.count_arrangement n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 15), ∃ r : Std.I64, Aegis.CountArrangement.count_arrangement n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 1.
    Preconditions: 1 <= n <= 15. -/
  theorem spec_3 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 15) (r : Std.I64)
      (hr : Aegis.CountArrangement.count_arrangement n = ok r) : 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 15) (r : Std.I64)
        (hr : Aegis.CountArrangement.count_arrangement n = ok r), 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= n!, where n! denotes the product 1*2*...*n.
    Preconditions: 1 <= n <= 15. -/
  theorem spec_4 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 15) (r : Std.I64)
      (hr : Aegis.CountArrangement.count_arrangement n = ok r) :
      r.val ≤ ((Nat.factorial n.val.toNat : Nat) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 15) (r : Std.I64)
        (hr : Aegis.CountArrangement.count_arrangement n = ok r), r.val ≤ ((Nat.factorial n.val.toNat : Nat) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r <= d(n) * (n-1)!, where d(n) is the number of positive divisors of n and (n-1)! denotes the factorial of n-1 with 0! = 1.
    Preconditions: 1 <= n <= 15. -/
  theorem spec_5 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 15) (r : Std.I64)
      (hr : Aegis.CountArrangement.count_arrangement n = ok r) :
      r.val ≤ ((divisorCount n.val.toNat * Nat.factorial (n.val.toNat - 1) : Nat) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 15) (r : Std.I64)
        (hr : Aegis.CountArrangement.count_arrangement n = ok r), r.val ≤ ((divisorCount n.val.toNat * Nat.factorial (n.val.toNat - 1) : Nat) : ℤ)) := by
    sorry

  /-- If count_arrangement n returns r_n and count_arrangement m returns r_m, then r_n <= r_m.
    Preconditions: n and m are i64 values with 1 <= n <= m <= 15. -/
  theorem spec_6 (n m : Std.I64) (hn_lo : 1 ≤ n.val) (hnm : n.val ≤ m.val)
      (hm_hi : m.val ≤ 15) (rn rm : Std.I64)
      (hrn : Aegis.CountArrangement.count_arrangement n = ok rn)
      (hrm : Aegis.CountArrangement.count_arrangement m = ok rm) : rn.val ≤ rm.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n m : Std.I64) (hn_lo : 1 ≤ n.val) (hnm : n.val ≤ m.val)
        (hm_hi : m.val ≤ 15) (rn rm : Std.I64)
        (hrn : Aegis.CountArrangement.count_arrangement n = ok rn)
        (hrm : Aegis.CountArrangement.count_arrangement m = ok rm), rn.val ≤ rm.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= 2.
    Preconditions: 2 <= n <= 15. -/
  theorem spec_7 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15) (r : Std.I64)
      (hr : Aegis.CountArrangement.count_arrangement n = ok r) : 2 ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15) (r : Std.I64)
        (hr : Aegis.CountArrangement.count_arrangement n = ok r), 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= 3.
    Preconditions: 3 <= n <= 15. -/
  theorem spec_8 (n : Std.I64) (hn_lo : 3 ≤ n.val) (hn_hi : n.val ≤ 15) (r : Std.I64)
      (hr : Aegis.CountArrangement.count_arrangement n = ok r) : 3 ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 3 ≤ n.val) (hn_hi : n.val ≤ 15) (r : Std.I64)
        (hr : Aegis.CountArrangement.count_arrangement n = ok r), 3 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: n = 1. -/
  theorem spec_9 :
      ∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 1#i64 = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 1#i64 = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r and r = 2.
    Preconditions: n = 2. -/
  theorem spec_10 :
      ∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 2#i64 = ok r ∧ r.val = 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 2#i64 = ok r ∧ r.val = 2) := by
    sorry

  /-- The function returns a result r and r = 3.
    Preconditions: n = 3. -/
  theorem spec_11 :
      ∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 3#i64 = ok r ∧ r.val = 3 := by
    sorry

  theorem spec_11_neg :
      ¬ (∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 3#i64 = ok r ∧ r.val = 3) := by
    sorry

  /-- The function returns a result r and r = 8.
    Preconditions: n = 4. -/
  theorem spec_12 :
      ∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 4#i64 = ok r ∧ r.val = 8 := by
    sorry

  theorem spec_12_neg :
      ¬ (∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 4#i64 = ok r ∧ r.val = 8) := by
    sorry

  /-- The function returns a result r and r = 132.
    Preconditions: n = 8. -/
  theorem spec_13 :
      ∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 8#i64 = ok r ∧ r.val = 132 := by
    sorry

  theorem spec_13_neg :
      ¬ (∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 8#i64 = ok r ∧ r.val = 132) := by
    sorry

  /-- The function returns a result r and r = 750.
    Preconditions: n = 11. -/
  theorem spec_14 :
      ∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 11#i64 = ok r ∧ r.val = 750 := by
    sorry

  theorem spec_14_neg :
      ¬ (∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 11#i64 = ok r ∧ r.val = 750) := by
    sorry

  /-- The function returns a result r and r = 24679.
    Preconditions: n = 15. -/
  theorem spec_15 :
      ∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 15#i64 = ok r ∧ r.val = 24679 := by
    sorry

  theorem spec_15_neg :
      ¬ (∃ r : Std.I64, Aegis.CountArrangement.count_arrangement 15#i64 = ok r ∧ r.val = 24679) := by
    sorry

  end AegisSpec.CountArrangement
