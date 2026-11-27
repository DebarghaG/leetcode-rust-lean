import Aegis.MaxValue.Code.Funs

/-!
# Specifications of `Aegis.MaxValue.max_value`

LeetCode problem `maximum-value-at-a-given-index-in-a-bounded-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxValue

def absDiff (a b : Int) : Int := if a ≤ b then b - a else a - b

def entry (nums : List Int) (i : Nat) : Int := nums.getD i 0

def sideSum (x k : Int) : Int :=
  ((List.range k.toNat).map (fun d => max 1 (x - ((d : Int) + 1)))).sum

def minSum (n index x : Int) : Int :=
  x + sideSum x index + sideSum x (n - 1 - index)

def witArray (n : Nat) (index x : Int) : List Int :=
  (List.range n).map (fun i => max 1 (x - absDiff (i : Int) index))

def Feasible (n : Nat) (maxSum : Int) (nums : List Int) : Prop :=
  nums.length = n ∧
  (∀ i : Nat, i < n → 1 ≤ entry nums i) ∧
  (∀ i : Nat, i + 1 < n → absDiff (entry nums i) (entry nums (i + 1)) ≤ 1) ∧
  nums.sum ≤ maxSum

/-- Whenever the function returns a result r, r is the maximum possible value of nums[index] among all integer arrays nums of length n satisfying: (i) nums[i] >= 1 for every 0 <= i < n; (ii) |nums[i] - nums[i+1]| <= 1 for every 0 <= i < n-1; (iii) the sum of nums[0], ..., nums[n-1] is at most maxSum. Equivalently, there exists such an array nums with nums[index] = r, and for every such array nums, nums[index] <= r.
  Preconditions: n, index, maxSum are integers with 1 <= n <= maxSum <= 10^9 and 0 <= index < n. -/
theorem spec_1 (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      (∃ nums : List Int,
          Feasible n.val.toNat maxSum.val nums ∧
            entry nums index.val.toNat = r.val) ∧
      (∀ nums : List Int,
          Feasible n.val.toNat maxSum.val nums → entry nums index.val.toNat ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      (∃ nums : List Int,
          Feasible n.val.toNat maxSum.val nums ∧
            entry nums index.val.toNat = r.val) ∧
      (∀ nums : List Int,
          Feasible n.val.toNat maxSum.val nums → entry nums index.val.toNat ≤ r.val)) := by
  sorry

/-- The function returns a result r; it does not fail on any input satisfying these preconditions.
  Preconditions: n, index, maxSum are integers with 1 <= n <= maxSum <= 10^9 and 0 <= index < n. -/
theorem spec_2 (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) :
    ∃ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val), ∃ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r) := by
  sorry

/-- Whenever the function returns a result r, we have r >= 1.
  Preconditions: n, index, maxSum are integers with 1 <= n <= maxSum <= 10^9 and 0 <= index < n. -/
theorem spec_3 (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, we have r <= maxSum - n + 1.
  Preconditions: n, index, maxSum are integers with 1 <= n <= maxSum <= 10^9 and 0 <= index < n. -/
theorem spec_4 (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      r.val ≤ maxSum.val - n.val + 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      r.val ≤ maxSum.val - n.val + 1) := by
  sorry

/-- Whenever the function returns a result r, we have r = maxSum.
  Preconditions: n = 1, 1 <= maxSum <= 10^9, and 0 <= index < n. -/
theorem spec_5 (n index maxSum : Std.I64)
    (hn : n.val = 1) (hmaxSum : 1 ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r → r.val = maxSum.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : n.val = 1) (hmaxSum : 1 ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r → r.val = maxSum.val) := by
  sorry

/-- Whenever the function returns a result r, we have r = 1.
  Preconditions: 1 <= n <= 10^9, 0 <= index < n, and maxSum = n. -/
theorem spec_6 (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hnub : n.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) (hmaxSum : maxSum.val = n.val) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r → r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hnub : n.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) (hmaxSum : maxSum.val = n.val), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, we have r = 2.
  Preconditions: 1 <= n <= 10^9 - 1, 0 <= index < n, and maxSum = n + 1. -/
theorem spec_7 (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hnub : n.val ≤ 999999999)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) (hmaxSum : maxSum.val = n.val + 1) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r → r.val = 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hnub : n.val ≤ 999999999)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) (hmaxSum : maxSum.val = n.val + 1), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r → r.val = 2) := by
  sorry

/-- Whenever the function returns a result r, we have r = floor((maxSum + 1) / 2), where floor is integer division by 2 after adding 1.
  Preconditions: n = 2, 0 <= index < 2, and 2 <= maxSum <= 10^9. -/
theorem spec_8 (n index maxSum : Std.I64)
    (hn : n.val = 2) (hindex : 0 ≤ index.val) (hidx : index.val < 2)
    (hmaxSum : 2 ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      r.val = (maxSum.val + 1) / 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : n.val = 2) (hindex : 0 ≤ index.val) (hidx : index.val < 2)
    (hmaxSum : 2 ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      r.val = (maxSum.val + 1) / 2) := by
  sorry

/-- Whenever max_value n index maxSum returns r and max_value n index' maxSum returns r', we have r = r'.
  Preconditions: n, index, maxSum are integers with 1 <= n <= maxSum <= 10^9 and 0 <= index < n. Let index' = n - 1 - index. -/
theorem spec_9 (n index index' maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val)
    (hidx' : index'.val = n.val - 1 - index.val) :
    ∀ r r' : Std.I64,
      Aegis.MaxValue.max_value n index maxSum = ok r →
        Aegis.MaxValue.max_value n index' maxSum = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n index index' maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val)
    (hidx' : index'.val = n.val - 1 - index.val), ∀ r r' : Std.I64,
      Aegis.MaxValue.max_value n index maxSum = ok r →
        Aegis.MaxValue.max_value n index' maxSum = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever max_value n index maxSum1 returns r1 and max_value n index maxSum2 returns r2, we have r1 <= r2.
  Preconditions: n, index, maxSum1, maxSum2 are integers with 1 <= n <= maxSum1 <= maxSum2 <= 10^9 and 0 <= index < n. -/
theorem spec_10 (n index maxSum1 maxSum2 : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum1 : n.val ≤ maxSum1.val) (hmaxSum12 : maxSum1.val ≤ maxSum2.val)
    (hmaxSum2 : maxSum2.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) :
    ∀ r1 r2 : Std.I64,
      Aegis.MaxValue.max_value n index maxSum1 = ok r1 →
        Aegis.MaxValue.max_value n index maxSum2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n index maxSum1 maxSum2 : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum1 : n.val ≤ maxSum1.val) (hmaxSum12 : maxSum1.val ≤ maxSum2.val)
    (hmaxSum2 : maxSum2.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val), ∀ r1 r2 : Std.I64,
      Aegis.MaxValue.max_value n index maxSum1 = ok r1 →
        Aegis.MaxValue.max_value n index maxSum2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever max_value n1 index maxSum returns r1 and max_value n2 index maxSum returns r2, we have r2 <= r1.
  Preconditions: index, maxSum, n1, n2 are integers with 0 <= index < n1 <= n2 <= maxSum <= 10^9 and 1 <= n1. -/
theorem spec_11 (n1 n2 index maxSum : Std.I64)
    (hn1 : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn2 : n2.val ≤ maxSum.val)
    (hmaxSum : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx1 : index.val < n1.val) (hidx2 : index.val < n2.val) :
    ∀ r1 r2 : Std.I64,
      Aegis.MaxValue.max_value n1 index maxSum = ok r1 →
        Aegis.MaxValue.max_value n2 index maxSum = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n1 n2 index maxSum : Std.I64)
    (hn1 : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn2 : n2.val ≤ maxSum.val)
    (hmaxSum : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx1 : index.val < n1.val) (hidx2 : index.val < n2.val), ∀ r1 r2 : Std.I64,
      Aegis.MaxValue.max_value n1 index maxSum = ok r1 →
        Aegis.MaxValue.max_value n2 index maxSum = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer x >= 1 we have x <= r if and only if M(x) <= maxSum, where M(x) = x + sum_{d=1}^{index} max(1, x-d) + sum_{d=1}^{n-1-index} max(1, x-d). Here sums over empty ranges are 0 and max(1,y) denotes the larger of 1 and y.
  Preconditions: n, index, maxSum are integers with 1 <= n <= maxSum <= 10^9 and 0 <= index < n. -/
theorem spec_12 (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      ∀ x : Int, 1 ≤ x →
        (x ≤ r.val ↔ minSum n.val index.val x ≤ maxSum.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      ∀ x : Int, 1 ≤ x →
        (x ≤ r.val ↔ minSum n.val index.val x ≤ maxSum.val)) := by
  sorry

/-- Whenever the function returns a result r, the array nums of length n defined by nums[i] = max(1, r - |i - index|) for 0 <= i < n has positive entries, satisfies |nums[i] - nums[i+1]| <= 1 for every 0 <= i < n-1, has total sum at most maxSum, and has nums[index] = r.
  Preconditions: n, index, maxSum are integers with 1 <= n <= maxSum <= 10^9 and 0 <= index < n. -/
theorem spec_13 (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      (∀ i : Nat, i < n.val.toNat → 1 ≤ entry (witArray n.val.toNat index.val r.val) i) ∧
      (∀ i : Nat,
          i + 1 < n.val.toNat →
            absDiff (entry (witArray n.val.toNat index.val r.val) i)
              (entry (witArray n.val.toNat index.val r.val) (i + 1)) ≤ 1) ∧
      (witArray n.val.toNat index.val r.val).sum ≤ maxSum.val ∧
      entry (witArray n.val.toNat index.val r.val) index.val.toNat = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      (∀ i : Nat, i < n.val.toNat → 1 ≤ entry (witArray n.val.toNat index.val r.val) i) ∧
      (∀ i : Nat,
          i + 1 < n.val.toNat →
            absDiff (entry (witArray n.val.toNat index.val r.val) i)
              (entry (witArray n.val.toNat index.val r.val) (i + 1)) ≤ 1) ∧
      (witArray n.val.toNat index.val r.val).sum ≤ maxSum.val ∧
      entry (witArray n.val.toNat index.val r.val) index.val.toNat = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer x with 1 <= x <= r, the array nums of length n defined by nums[i] = max(1, x - |i - index|) for 0 <= i < n has positive entries, satisfies |nums[i] - nums[i+1]| <= 1 for every 0 <= i < n-1, has total sum at most maxSum, and has nums[index] = x.
  Preconditions: n, index, maxSum are integers with 1 <= n <= maxSum <= 10^9 and 0 <= index < n. -/
theorem spec_14 (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      ∀ x : Int, 1 ≤ x → x ≤ r.val →
        (∀ i : Nat, i < n.val.toNat → 1 ≤ entry (witArray n.val.toNat index.val x) i) ∧
        (∀ i : Nat,
            i + 1 < n.val.toNat →
              absDiff (entry (witArray n.val.toNat index.val x) i)
                (entry (witArray n.val.toNat index.val x) (i + 1)) ≤ 1) ∧
        (witArray n.val.toNat index.val x).sum ≤ maxSum.val ∧
        entry (witArray n.val.toNat index.val x) index.val.toNat = x := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      ∀ x : Int, 1 ≤ x → x ≤ r.val →
        (∀ i : Nat, i < n.val.toNat → 1 ≤ entry (witArray n.val.toNat index.val x) i) ∧
        (∀ i : Nat,
            i + 1 < n.val.toNat →
              absDiff (entry (witArray n.val.toNat index.val x) i)
                (entry (witArray n.val.toNat index.val x) (i + 1)) ≤ 1) ∧
        (witArray n.val.toNat index.val x).sum ≤ maxSum.val ∧
        entry (witArray n.val.toNat index.val x) index.val.toNat = x) := by
  sorry

/-- Whenever the function returns a result r, we have 2*r <= maxSum - n + 3.
  Preconditions: n, index, maxSum are integers with 2 <= n <= maxSum <= 10^9 and 0 <= index < n. -/
theorem spec_15 (n index maxSum : Std.I64)
    (hn : 2 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      2 * r.val ≤ maxSum.val - n.val + 3 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 2 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      2 * r.val ≤ maxSum.val - n.val + 3) := by
  sorry

/-- Whenever the function returns a result r, we have 3*r <= maxSum - n + 5.
  Preconditions: n, index, maxSum are integers with 3 <= n <= maxSum <= 10^9 and 0 < index < n-1. -/
theorem spec_16 (n index maxSum : Std.I64)
    (hn : 3 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex0 : 0 < index.val) (hidx : index.val < n.val - 1) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      3 * r.val ≤ maxSum.val - n.val + 5 := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 3 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex0 : 0 < index.val) (hidx : index.val < n.val - 1), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      3 * r.val ≤ maxSum.val - n.val + 5) := by
  sorry

/-- Whenever the function returns a result r, we have r = maxSum if and only if n = 1.
  Preconditions: n, index, maxSum are integers with 1 <= n <= maxSum <= 10^9 and 0 <= index < n. -/
theorem spec_17 (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val) :
    ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      (r.val = maxSum.val ↔ n.val = 1) := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (n index maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hindex : 0 ≤ index.val) (hidx : index.val < n.val), ∀ r : Std.I64, Aegis.MaxValue.max_value n index maxSum = ok r →
      (r.val = maxSum.val ↔ n.val = 1)) := by
  sorry

/-- Whenever max_value n index1 maxSum returns r1 and max_value n index2 maxSum returns r2, we have r1 >= r2.
  Preconditions: n, index1, index2, maxSum are integers with 1 <= n <= maxSum <= 10^9, 0 <= index1 <= index2 < n, and 2*index2 <= n-1. -/
theorem spec_18 (n index1 index2 maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hi1 : 0 ≤ index1.val) (hi12 : index1.val ≤ index2.val) (hi2 : index2.val < n.val)
    (hhalf : 2 * index2.val ≤ n.val - 1) :
    ∀ r1 r2 : Std.I64,
      Aegis.MaxValue.max_value n index1 maxSum = ok r1 →
        Aegis.MaxValue.max_value n index2 maxSum = ok r2 → r1.val ≥ r2.val := by
  sorry

theorem spec_18_neg :
    ¬ (∀ (n index1 index2 maxSum : Std.I64)
    (hn : 1 ≤ n.val) (hmaxSum : n.val ≤ maxSum.val) (hmaxSumub : maxSum.val ≤ 1000000000)
    (hi1 : 0 ≤ index1.val) (hi12 : index1.val ≤ index2.val) (hi2 : index2.val < n.val)
    (hhalf : 2 * index2.val ≤ n.val - 1), ∀ r1 r2 : Std.I64,
      Aegis.MaxValue.max_value n index1 maxSum = ok r1 →
        Aegis.MaxValue.max_value n index2 maxSum = ok r2 → r1.val ≥ r2.val) := by
  sorry

end AegisSpec.MaxValue
