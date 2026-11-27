import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `visit-array-positions-to-maximize-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxScore

open Aegis.MaxScore (max_score)

def valAt (nums : Slice Std.I64) (i : Nat) : Int :=
  (nums.val.getD i (⟨0⟩ : Std.I64)).val

def total (nums : Slice Std.I64) : Int :=
  (nums.val.map (fun v => v.val)).sum

def totalWhere (nums : Slice Std.I64) (P : Nat → Prop) [DecidablePred P] : Int :=
  (((List.range nums.val.length).filter P).map (fun i => valAt nums i)).sum

def adjParityChanges (nums : Slice Std.I64) : Nat :=
  ((List.range (nums.val.length - 1)).filter
    (fun i => valAt nums i % 2 ≠ valAt nums (i + 1) % 2)).length

def parityChanges : List Int → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a % 2 = b % 2 then 0 else 1) + parityChanges (b :: t)

def valsAt (nums : Slice Std.I64) (p : List Nat) : List Int :=
  p.map (fun i => valAt nums i)

def IndexSeq (nums : Slice Std.I64) (p : List Nat) : Prop :=
  p ≠ [] ∧ p.head? = some 0 ∧ p.Pairwise (· < ·) ∧ ∀ i ∈ p, i < nums.val.length

def score (nums : Slice Std.I64) (x : Int) (p : List Nat) : Int :=
  (valsAt nums p).sum - x * ((parityChanges (valsAt nums p) : Nat) : Int)

def IsMaxScore (nums : Slice Std.I64) (x : Int) (r : Int) : Prop :=
  (∃ p, IndexSeq nums p ∧ score nums x p = r) ∧ ∀ q, IndexSeq nums q → score nums x q ≤ r

def Pre (nums : Slice Std.I64) (x : Std.I64) : Prop :=
  2 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
    (∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000) ∧
    1 ≤ x.val ∧ x.val ≤ 1000000

/-- Whenever the function returns a result r, r equals the maximum, over all finite strictly increasing index sequences p_0 < p_1 < ... < p_{m-1} with m >= 1, p_0 = 0, and p_{m-1} < len(nums), of (sum_{k=0}^{m-1} nums[p_k]) - x * (the number of k with 0 <= k < m-1 and nums[p_k] mod 2 != nums[p_{k+1}] mod 2). Such a maximum exists because there are finitely many such sequences and every score is an integer.
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_1 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r → IsMaxScore nums x.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r → IsMaxScore nums x.val r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite strictly increasing index sequence p_0 < ... < p_{m-1} with m >= 1, p_0 = 0, and p_{m-1} < len(nums) such that r = (sum_{k=0}^{m-1} nums[p_k]) - x * (the number of k with 0 <= k < m-1 and nums[p_k] mod 2 != nums[p_{k+1}] mod 2).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_2 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r → ∃ p, IndexSeq nums p ∧ score nums x.val p = r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r → ∃ p, IndexSeq nums p ∧ score nums x.val p = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every finite strictly increasing index sequence p_0 < ... < p_{m-1} with m >= 1, p_0 = 0, and p_{m-1} < len(nums), (sum_{k=0}^{m-1} nums[p_k]) - x * (the number of k with 0 <= k < m-1 and nums[p_k] mod 2 != nums[p_{k+1}] mod 2) <= r.
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_3 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r → ∀ p, IndexSeq nums p → score nums x.val p ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r → ∀ p, IndexSeq nums p → score nums x.val p ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{len(nums)-1} nums[i].
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_4 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r → r.val ≤ total nums := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r → r.val ≤ total nums) := by
  sorry

/-- Whenever the function returns a result r, r >= sum over all i with 0 <= i < len(nums) and nums[i] mod 2 = nums[0] mod 2 of nums[i].
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_5 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r →
      totalWhere nums (fun i => valAt nums i % 2 = valAt nums 0 % 2) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r →
      totalWhere nums (fun i => valAt nums i % 2 = valAt nums 0 % 2) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if for every i with 0 <= i < len(nums) we have nums[i] mod 2 = nums[0] mod 2, then r = sum_{i=0}^{len(nums)-1} nums[i].
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_6 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r →
      (∀ i, i < nums.val.length → valAt nums i % 2 = valAt nums 0 % 2) → r.val = total nums := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r →
      (∀ i, i < nums.val.length → valAt nums i % 2 = valAt nums 0 % 2) → r.val = total nums) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) = 2 then r = max(nums[0], nums[0] + nums[1] - (if nums[0] mod 2 != nums[1] mod 2 then x else 0)).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_7 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r → nums.val.length = 2 →
      r.val = max (valAt nums 0)
        (valAt nums 0 + valAt nums 1 -
          (if valAt nums 0 % 2 = valAt nums 1 % 2 then 0 else x.val)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r → nums.val.length = 2 →
      r.val = max (valAt nums 0)
        (valAt nums 0 + valAt nums 1 -
          (if valAt nums 0 % 2 = valAt nums 1 % 2 then 0 else x.val))) := by
  sorry

/-- Whenever the function returns a result r, if x >= sum_{i=1}^{len(nums)-1} nums[i], then r = sum over all i with 0 <= i < len(nums) and nums[i] mod 2 = nums[0] mod 2 of nums[i].
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_8 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r →
      totalWhere nums (fun i => 1 ≤ i) ≤ x.val →
        r.val = totalWhere nums (fun i => valAt nums i % 2 = valAt nums 0 % 2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r →
      totalWhere nums (fun i => 1 ≤ i) ≤ x.val →
        r.val = totalWhere nums (fun i => valAt nums i % 2 = valAt nums 0 % 2)) := by
  sorry

/-- Whenever the function returns a result r, if there exist a and b with 0 <= a < len(nums), 0 <= b < len(nums), and nums[a] mod 2 != nums[b] mod 2, then r < sum_{k=0}^{len(nums)-1} nums[k].
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_9 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r →
      (∃ a b, a < nums.val.length ∧ b < nums.val.length ∧
        valAt nums a % 2 ≠ valAt nums b % 2) →
        r.val < total nums := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r →
      (∃ a b, a < nums.val.length ∧ b < nums.val.length ∧
        valAt nums a % 2 ≠ valAt nums b % 2) →
        r.val < total nums) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 < j < len(nums), r >= nums[0] + nums[j] - (if nums[0] mod 2 != nums[j] mod 2 then x else 0).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_10 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r → ∀ j, 0 < j → j < nums.val.length →
      valAt nums 0 + valAt nums j -
        (if valAt nums 0 % 2 = valAt nums j % 2 then 0 else x.val) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r → ∀ j, 0 < j → j < nums.val.length →
      valAt nums 0 + valAt nums j -
        (if valAt nums 0 % 2 = valAt nums j % 2 then 0 else x.val) ≤ r.val) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; in particular, it does not panic, access an out-of-bounds index, or overflow a 64-bit integer, and the returned r is a 64-bit integer.
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_11 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∃ r : Std.I64, max_score nums x = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∃ r : Std.I64, max_score nums x = ok r) := by
  sorry

/-- Whenever the function returns a result r for inputs (nums, x), for every integer x' with x <= x' <= 1000000, r is greater than or equal to the maximum over all finite strictly increasing index sequences p_0 < ... < p_{m-1} with m >= 1, p_0 = 0, and p_{m-1} < len(nums) of (sum_{k=0}^{m-1} nums[p_k]) - x' * (the number of k with 0 <= k < m-1 and nums[p_k] mod 2 != nums[p_{k+1}] mod 2).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_12 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r → ∀ x' : Int, x.val ≤ x' → x' ≤ 1000000 →
      ∀ m, IsMaxScore nums x' m → m ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r → ∀ x' : Int, x.val ≤ x' → x' ≤ 1000000 →
      ∀ m, IsMaxScore nums x' m → m ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= sum_{i=0}^{len(nums)-1} nums[i] - x * (the number of i with 0 <= i < len(nums)-1 and nums[i] mod 2 != nums[i+1] mod 2).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_13 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r →
      total nums - x.val * ((adjParityChanges nums : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r →
      total nums - x.val * ((adjParityChanges nums : Nat) : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= max( sum over all i with 0 <= i < len(nums) and nums[i] mod 2 = nums[0] mod 2 of nums[i], sum_{i=0}^{len(nums)-1} nums[i] - x ).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_14 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r →
      r.val ≤ max (totalWhere nums (fun i => valAt nums i % 2 = valAt nums 0 % 2))
        (total nums - x.val) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r →
      r.val ≤ max (totalWhere nums (fun i => valAt nums i % 2 = valAt nums 0 % 2))
        (total nums - x.val)) := by
  sorry

/-- Whenever the function returns a result r, if x >= sum over all i with 0 <= i < len(nums) and nums[i] mod 2 != nums[0] mod 2 of nums[i], then r = sum over all i with 0 <= i < len(nums) and nums[i] mod 2 = nums[0] mod 2 of nums[i].
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; x is a 64-bit integer with 1 <= x <= 1000000. All indices are 0-based and all arithmetic is exact (no wrap-around). -/
theorem spec_15 (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x) :
    ∀ r, max_score nums x = ok r →
      totalWhere nums (fun i => valAt nums i % 2 ≠ valAt nums 0 % 2) ≤ x.val →
        r.val = totalWhere nums (fun i => valAt nums i % 2 = valAt nums 0 % 2) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (hpre : Pre nums x), ∀ r, max_score nums x = ok r →
      totalWhere nums (fun i => valAt nums i % 2 ≠ valAt nums 0 % 2) ≤ x.val →
        r.val = totalWhere nums (fun i => valAt nums i % 2 = valAt nums 0 % 2)) := by
  sorry

end AegisSpec.MaxScore
