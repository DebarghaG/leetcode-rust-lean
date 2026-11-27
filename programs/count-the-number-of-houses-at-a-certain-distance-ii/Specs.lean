import Aegis.CountOfPairs.Code.Funs
import Mathlib.Data.Int.Interval

/-!
# Specifications of `Aegis.CountOfPairs.count_of_pairs`

LeetCode problem `count-the-number-of-houses-at-a-certain-distance-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountOfPairs

  namespace AegisSpec.CountOfPairs

  def vecGet? (r : alloc.vec.Vec Std.I64) (i : ℤ) : Option ℤ :=
    if 0 ≤ i then (r.val[i.toNat]?).map (fun v => v.val) else none

  def pairDist (x y a b : ℤ) : ℤ :=
    min (|a - b|) (min (|a - x| + 1 + |y - b|) (|a - y| + 1 + |x - b|))

  def pairCount (n x y k : ℤ) : ℤ :=
    (((Finset.Icc (1 : ℤ) n).product (Finset.Icc (1 : ℤ) n)).filter
        (fun p : ℤ × ℤ => p.1 ≠ p.2 ∧ pairDist x y p.1 p.2 = k)).card

  /-- Whenever the function returns a result r, the vector r has length n, and for every integer k with 1 <= k <= n, r[k-1] equals the number of ordered pairs (a,b) of integers such that 1 <= a <= n, 1 <= b <= n, a != b, and dist(a,b) = k, where |.| denotes absolute value and dist(a,b) = min(|a-b|, |a-x| + 1 + |y-b|, |a-y| + 1 + |x-b|).
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_1 (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
      (h : count_of_pairs n x y = .ok r) :
      (r.val.length : ℤ) = n.val ∧
        ∀ k : ℤ, 1 ≤ k → k ≤ n.val →
          vecGet? r (k - 1) = some (pairCount n.val x.val y.val k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
        (h : count_of_pairs n x y = Result.ok r), (r.val.length : ℤ) = n.val ∧
          ∀ k : ℤ, 1 ≤ k → k ≤ n.val →
            vecGet? r (k - 1) = some (pairCount n.val x.val y.val k)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_2 (n x y : Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val) :
      ∃ r : alloc.vec.Vec Std.I64, count_of_pairs n x y = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n x y : Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val), ∃ r : alloc.vec.Vec Std.I64, count_of_pairs n x y = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, the sum of r[k-1] over all integers k with 1 <= k <= n equals n*(n-1).
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_3 (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
      (h : count_of_pairs n x y = .ok r) :
      (∑ k ∈ Finset.Icc (1 : ℤ) n.val, (vecGet? r (k - 1)).getD 0) = n.val * (n.val - 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
        (h : count_of_pairs n x y = Result.ok r), (∑ k ∈ Finset.Icc (1 : ℤ) n.val, (vecGet? r (k - 1)).getD 0) = n.val * (n.val - 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer i with 0 <= i < n, 0 <= r[i] <= n*(n-1).
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_4 (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
      (h : count_of_pairs n x y = .ok r) :
      ∀ i : ℤ, 0 ≤ i → i < n.val →
        ∃ v : ℤ, vecGet? r i = some v ∧ 0 ≤ v ∧ v ≤ n.val * (n.val - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
        (h : count_of_pairs n x y = Result.ok r), ∀ i : ℤ, 0 ≤ i → i < n.val →
          ∃ v : ℤ, vecGet? r i = some v ∧ 0 ≤ v ∧ v ≤ n.val * (n.val - 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 1 <= k <= n, r[k-1] is even.
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_5 (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
      (h : count_of_pairs n x y = .ok r) :
      ∀ k : ℤ, 1 ≤ k → k ≤ n.val →
        ∃ v : ℤ, vecGet? r (k - 1) = some v ∧ Even v := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
        (h : count_of_pairs n x y = Result.ok r), ∀ k : ℤ, 1 ≤ k → k ≤ n.val →
          ∃ v : ℤ, vecGet? r (k - 1) = some v ∧ Even v) := by
    sorry

  /-- Whenever the function returns a result r, r[n-1] = 0.
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_6 (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
      (h : count_of_pairs n x y = .ok r) :
      vecGet? r (n.val - 1) = some 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
        (h : count_of_pairs n x y = Result.ok r), vecGet? r (n.val - 1) = some 0) := by
    sorry

  /-- Whenever the function returns a result r, r[0] = 2 * ((n-1) + (if x != y and |x-y| >= 2 then 1 else 0)).
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_7 (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
      (h : count_of_pairs n x y = .ok r) :
      vecGet? r 0 =
        some (2 * ((n.val - 1) + (if x.val ≠ y.val ∧ 2 ≤ |x.val - y.val| then (1 : ℤ) else 0))) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
        (h : count_of_pairs n x y = Result.ok r), vecGet? r 0 =
          some (2 * ((n.val - 1) + (if x.val ≠ y.val ∧ 2 ≤ |x.val - y.val| then (1 : ℤ) else 0)))) := by
    sorry

  /-- Whenever the function returns a result r and x = y, for every integer k with 1 <= k <= n, r[k-1] = 2*(n-k).
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_8 (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
      (hxy : x.val = y.val)
      (h : count_of_pairs n x y = .ok r) :
      ∀ k : ℤ, 1 ≤ k → k ≤ n.val → vecGet? r (k - 1) = some (2 * (n.val - k)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
        (hxy : x.val = y.val)
        (h : count_of_pairs n x y = Result.ok r), ∀ k : ℤ, 1 ≤ k → k ≤ n.val → vecGet? r (k - 1) = some (2 * (n.val - k))) := by
    sorry

  /-- Whenever the function returns a result r and |x-y| = 1, for every integer k with 1 <= k <= n, r[k-1] = 2*(n-k).
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_9 (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
      (hxy : |x.val - y.val| = 1)
      (h : count_of_pairs n x y = .ok r) :
      ∀ k : ℤ, 1 ≤ k → k ≤ n.val → vecGet? r (k - 1) = some (2 * (n.val - k)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
        (hxy : |x.val - y.val| = 1)
        (h : count_of_pairs n x y = Result.ok r), ∀ k : ℤ, 1 ≤ k → k ≤ n.val → vecGet? r (k - 1) = some (2 * (n.val - k))) := by
    sorry

  /-- Whenever the function returns a result r and n >= 3 and ((x = 1 and y = n) or (x = n and y = 1)), for every integer k with 1 <= k <= n, r[k-1] = 2*n if 2*k < n, r[k-1] = n if 2*k = n, and r[k-1] = 0 if 2*k > n.
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_10 (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
      (hn3 : 3 ≤ n.val)
      (hends : (x.val = 1 ∧ y.val = n.val) ∨ (x.val = n.val ∧ y.val = 1))
      (h : count_of_pairs n x y = .ok r) :
      ∀ k : ℤ, 1 ≤ k → k ≤ n.val →
        vecGet? r (k - 1) =
          some (if 2 * k < n.val then 2 * n.val else if 2 * k = n.val then n.val else 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
        (hn3 : 3 ≤ n.val)
        (hends : (x.val = 1 ∧ y.val = n.val) ∨ (x.val = n.val ∧ y.val = 1))
        (h : count_of_pairs n x y = Result.ok r), ∀ k : ℤ, 1 ≤ k → k ≤ n.val →
          vecGet? r (k - 1) =
            some (if 2 * k < n.val then 2 * n.val else if 2 * k = n.val then n.val else 0)) := by
    sorry

  /-- Whenever the function returns a result r and x != y and |x-y| >= 2, r[n-2] = 0.
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_11 (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
      (hxy : x.val ≠ y.val)
      (hxy' : 2 ≤ |x.val - y.val|)
      (h : count_of_pairs n x y = .ok r) :
      vecGet? r (n.val - 2) = some 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n x y : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
        (hxy : x.val ≠ y.val)
        (hxy' : 2 ≤ |x.val - y.val|)
        (h : count_of_pairs n x y = Result.ok r), vecGet? r (n.val - 2) = some 0) := by
    sorry

  /-- For all integers n, x, y satisfying the preconditions, if the function returns a result r when called with (n, x, y) and a result r' when called with (n, y, x), then r = r'.
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_12 (n x y : Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val) :
      ∀ r r' : alloc.vec.Vec Std.I64,
        count_of_pairs n x y = .ok r → count_of_pairs n y x = .ok r' → r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n x y : Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val), ∀ r r' : alloc.vec.Vec Std.I64,
          count_of_pairs n x y = Result.ok r → count_of_pairs n y x = Result.ok r' → r = r') := by
    sorry

  /-- For all integers n, x, y satisfying the preconditions, if the function returns a result r when called with (n, x, y) and a result r' when called with (n, n+1-x, n+1-y), then r = r'.
    Preconditions: n, x, y are integers with 2 <= n <= 100000, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_13 (n x y sx sy : Std.I64)
      (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
      (hsx : sx.val = n.val + 1 - x.val)
      (hsy : sy.val = n.val + 1 - y.val) :
      ∀ r r' : alloc.vec.Vec Std.I64,
        count_of_pairs n x y = .ok r → count_of_pairs n sx sy = .ok r' → r = r' := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n x y sx sy : Std.I64)
        (hn : 2 ≤ n.val) (hn_max : n.val ≤ 100000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ n.val)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ n.val)
        (hsx : sx.val = n.val + 1 - x.val)
        (hsy : sy.val = n.val + 1 - y.val), ∀ r r' : alloc.vec.Vec Std.I64,
          count_of_pairs n x y = Result.ok r → count_of_pairs n sx sy = Result.ok r' → r = r') := by
    sorry

  end AegisSpec.CountOfPairs
