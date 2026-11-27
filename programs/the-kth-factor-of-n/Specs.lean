import Aegis.KthFactor.Code.Funs

/-!
# Specifications of `Aegis.KthFactor.kth_factor`

LeetCode problem `the-kth-factor-of-n`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aeneas.Std.Result

  namespace AegisSpec.KthFactor

  def IsPosDivisor (n d : ℤ) : Prop :=
    1 ≤ d ∧ d ≤ n ∧ n % d = 0

  def posDivisors (n : ℤ) : List ℤ :=
    ((List.range n.toNat).map (fun i => (i : ℤ) + 1)).filter (fun d => decide (n % d = 0))

  def numPosDivisors (n : ℤ) : ℕ := (posDivisors n).length

  def numPosDivisorsLE (n r : ℤ) : ℕ :=
    ((posDivisors n).filter (fun d => decide (d ≤ r))).length

  def numPosDivisorsLT (n r : ℤ) : ℕ :=
    ((posDivisors n).filter (fun d => decide (d < r))).length

  def kthPosDivisor (n : ℤ) (k : ℕ) : Option ℤ := (posDivisors n)[k - 1]?

  def IsPrimePosDivisors (n : ℤ) : Prop :=
    ∀ d : ℤ, IsPosDivisor n d → d = 1 ∨ d = n

  /-- Let D = [d_1, d_2, ..., d_m] be the list of all positive divisors of n in strictly increasing order, i.e. each d_i is a positive integer with d_i <= n and n % d_i = 0, and d_1 < d_2 < ... < d_m. Then kth_factor n k returns a result r (it does not fail), and r = d_k if k <= m, while r = -1 if k > m.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000. -/
  theorem spec_1 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.KthFactor.kth_factor n k = ok r ∧
          (k.val ≤ (numPosDivisors n.val : ℤ) →
            kthPosDivisor n.val k.val.toNat = some r.val) ∧
          ((numPosDivisors n.val : ℤ) < k.val → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000), ∃ r : Std.I64,
          Aegis.KthFactor.kth_factor n k = ok r ∧
            (k.val ≤ (numPosDivisors n.val : ℤ) →
              kthPosDivisor n.val k.val.toNat = some r.val) ∧
            ((numPosDivisors n.val : ℤ) < k.val → r.val = -1)) := by
    sorry

  /-- For every n and k satisfying the preconditions, kth_factor n k returns a result r; it never fails.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000. -/
  theorem spec_2 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.KthFactor.kth_factor n k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000), ∃ r : Std.I64, Aegis.KthFactor.kth_factor n k = ok r) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, r = -1 if and only if the number of positive divisors d of n (that is, integers d with 1 <= d <= n and n % d = 0) is less than k.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000. -/
  theorem spec_3 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      (r.val = -1 ↔ (numPosDivisors n.val : ℤ) < k.val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), (r.val = -1 ↔ (numPosDivisors n.val : ℤ) < k.val)) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, if r != -1 then 1 <= r <= n.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000. -/
  theorem spec_4 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      r.val ≠ -1 → 1 ≤ r.val ∧ r.val ≤ n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), r.val ≠ -1 → 1 ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, if r != -1 then n % r = 0.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000. -/
  theorem spec_5 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      r.val ≠ -1 → n.val % r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), r.val ≠ -1 → n.val % r.val = 0) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, if r != -1 then the number of positive divisors d of n with d <= r is exactly k.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000. -/
  theorem spec_6 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      r.val ≠ -1 → (numPosDivisorsLE n.val r.val : ℤ) = k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), r.val ≠ -1 → (numPosDivisorsLE n.val r.val : ℤ) = k.val) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, if r != -1 then the number of positive divisors d of n with d < r is exactly k - 1.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000. -/
  theorem spec_7 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      r.val ≠ -1 → (numPosDivisorsLT n.val r.val : ℤ) = k.val - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), r.val ≠ -1 → (numPosDivisorsLT n.val r.val : ℤ) = k.val - 1) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, r = 1.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= n <= 1000 and k = 1. -/
  theorem spec_8 (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn : n.val ≤ 1000) (hk : k.val = 1)
      (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      r.val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn : n.val ≤ 1000) (hk : k.val = 1)
        (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), r.val = 1) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, if r = 1 then k = 1.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000. -/
  theorem spec_9 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      r.val = 1 → k.val = 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), r.val = 1 → k.val = 1) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, if k equals the number of positive divisors of n, then r = n.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000. -/
  theorem spec_10 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      k.val = (numPosDivisors n.val : ℤ) → r.val = n.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), k.val = (numPosDivisors n.val : ℤ) → r.val = n.val) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, if r = n then k equals the number of positive divisors of n.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000. -/
  theorem spec_11 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      r.val = n.val → k.val = (numPosDivisors n.val : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), r.val = n.val → k.val = (numPosDivisors n.val : ℤ)) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, if r != -1 then r >= k.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000. -/
  theorem spec_12 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      r.val ≠ -1 → k.val ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000) (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), r.val ≠ -1 → k.val ≤ r.val) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, r = n.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000, and suppose n is prime (its only positive divisors are 1 and n). Also k = 2. -/
  theorem spec_13 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) (hprime : IsPrimePosDivisors n.val) (hk2 : k.val = 2)
      (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      r.val = n.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000) (hprime : IsPrimePosDivisors n.val) (hk2 : k.val = 2)
        (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), r.val = n.val) := by
    sorry

  /-- Whenever kth_factor n k returns a result r, r = -1.
    Preconditions: Let n and k be the integer values of the two arguments, with 1 <= k <= n <= 1000, and suppose n is prime (its only positive divisors are 1 and n). Also k >= 3. -/
  theorem spec_14 (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
      (hn : n.val ≤ 1000) (hprime : IsPrimePosDivisors n.val) (hk3 : 3 ≤ k.val)
      (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r) :
      r.val = -1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n k : Std.I64) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
        (hn : n.val ≤ 1000) (hprime : IsPrimePosDivisors n.val) (hk3 : 3 ≤ k.val)
        (r : Std.I64) (hr : Aegis.KthFactor.kth_factor n k = ok r), r.val = -1) := by
    sorry

  /-- Whenever kth_factor n k1 returns a result r1 and kth_factor n k2 returns a result r2, if r1 != -1 and r2 != -1 then r1 < r2.
    Preconditions: Let n, k1, and k2 be integer values with 1 <= n <= 1000 and 1 <= k1 < k2 <= n. -/
  theorem spec_15 (n k1 k2 : Std.I64) (hn1 : 1 ≤ n.val) (hn : n.val ≤ 1000)
      (hk1 : 1 ≤ k1.val) (hk12 : k1.val < k2.val) (hk2 : k2.val ≤ n.val)
      (r1 r2 : Std.I64) (hr1 : Aegis.KthFactor.kth_factor n k1 = ok r1)
      (hr2 : Aegis.KthFactor.kth_factor n k2 = ok r2) :
      r1.val ≠ -1 → r2.val ≠ -1 → r1.val < r2.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n k1 k2 : Std.I64) (hn1 : 1 ≤ n.val) (hn : n.val ≤ 1000)
        (hk1 : 1 ≤ k1.val) (hk12 : k1.val < k2.val) (hk2 : k2.val ≤ n.val)
        (r1 r2 : Std.I64) (hr1 : Aegis.KthFactor.kth_factor n k1 = ok r1)
        (hr2 : Aegis.KthFactor.kth_factor n k2 = ok r2), r1.val ≠ -1 → r2.val ≠ -1 → r1.val < r2.val) := by
    sorry

  end AegisSpec.KthFactor
