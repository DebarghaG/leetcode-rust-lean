import Aegis.MaxOperations.Code.Funs

/-!
# Specifications of `Aegis.MaxOperations.max_operations`

LeetCode problem `maximum-number-of-operations-with-the-same-score-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxOperations

namespace AegisSpec.MaxOperations

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def elem (a : List ℤ) (i : Nat) : ℤ := a.getD i 0

inductive delStep (a : List ℤ) : Nat → Nat → ℤ → Nat → Nat → Prop where

  | left {L R : Nat} (h : L + 2 ≤ R) :
      delStep a L R (elem a L + elem a (L + 1)) (L + 2) R

  | right {L R : Nat} (h : L + 2 ≤ R) :
      delStep a L R (elem a (R - 2) + elem a (R - 1)) L (R - 2)

  | both {L R : Nat} (h : L + 2 ≤ R) :
      delStep a L R (elem a L + elem a (R - 1)) (L + 1) (R - 1)

inductive delSeq (a : List ℤ) : Nat → Nat → Nat → ℤ → Prop where

  | nil {L R : Nat} (S : ℤ) : delSeq a 0 L R S

  | step {L R L' R' : Nat} {S : ℤ} {k : Nat}
      (h : delStep a L R S L' R') (t : delSeq a k L' R' S) :
      delSeq a (k + 1) L R S

def feasible (a : List ℤ) (k : Nat) : Prop := ∃ S, delSeq a k 0 a.length S

def IsMaxFeasible (a : List ℤ) (k : Nat) : Prop :=
  k ≤ a.length / 2 ∧ feasible a k ∧ ∀ k', feasible a k' → k' ≤ k

/-- The function returns a result r and does not fail. Let n = len(nums). For k >= 0, call k feasible if k = 0, or if there exist an integer S and a sequence of k operations starting from the current interval [L,R) = [0,n) such that each operation uses the current interval and is exactly one of: (a) delete the two leftmost elements, add nums[L]+nums[L+1] to the scores, and set L := L+2; (b) delete the two rightmost elements, add nums[R-2]+nums[R-1] to the scores, and set R := R-2; (c) delete the leftmost and rightmost elements, add nums[L]+nums[R-1] to the scores, and set L := L+1, R := R-1; each operation is allowed only when R-L >= 2; and all k operation scores are equal to S. Then r = max { k | 0 <= k <= floor(n/2) and k is feasible }.
  Preconditions: nums is a slice of i64 with n = len(nums), 2 <= n <= 2000, and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_1 (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000) :
    ∃ r, max_operations nums = ok r ∧
      ∃ k : Nat, r.val = (k : ℤ) ∧ IsMaxFeasible (vals nums) k := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000), ∃ r, max_operations nums = ok r ∧
      ∃ k : Nat, r.val = (k : ℤ) ∧ IsMaxFeasible (vals nums) k) := by
  sorry

/-- For every call satisfying the preconditions, the function returns a result r of type Result.ok; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: nums is a slice of i64 with n = len(nums), 2 <= n <= 2000, and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_2 (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000) :
    ∃ r, max_operations nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000), ∃ r, max_operations nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: nums is a slice of i64 with n = len(nums), 2 <= n <= 2000, and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_3 (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000) :
    ∀ r, max_operations nums = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000), ∀ r, max_operations nums = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= floor(len(nums)/2).
  Preconditions: nums is a slice of i64 with n = len(nums), 2 <= n <= 2000, and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_4 (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000) :
    ∀ r, max_operations nums = ok r → r.val ≤ ((n / 2 : Nat) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000), ∀ r, max_operations nums = ok r → r.val ≤ ((n / 2 : Nat) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: n = len(nums) = 2, and 1 <= nums[0], nums[1] <= 1000. -/
theorem spec_5 (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n) (hn_eq : n = 2)
    (hrange : 1 ≤ elem (vals nums) 0 ∧ elem (vals nums) 0 ≤ 1000 ∧
      1 ≤ elem (vals nums) 1 ∧ elem (vals nums) 1 ≤ 1000) :
    ∀ r, max_operations nums = ok r → r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n) (hn_eq : n = 2)
    (hrange : 1 ≤ elem (vals nums) 0 ∧ elem (vals nums) 0 ≤ 1000 ∧
      1 ≤ elem (vals nums) 1 ∧ elem (vals nums) 1 ≤ 1000), ∀ r, max_operations nums = ok r → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, r = 2 if (nums[0]+nums[1] = nums[2]+nums[3] or nums[0]+nums[3] = nums[1]+nums[2]); otherwise r = 1.
  Preconditions: n = len(nums) = 4, and 1 <= nums[i] <= 1000 for every i with 0 <= i < 4. -/
theorem spec_6 (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n) (hn_eq : n = 4)
    (hrange : ∀ i, i < 4 → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000) :
    ∀ r, max_operations nums = ok r →
      (if elem (vals nums) 0 + elem (vals nums) 1 = elem (vals nums) 2 + elem (vals nums) 3 ∨
          elem (vals nums) 0 + elem (vals nums) 3 = elem (vals nums) 1 + elem (vals nums) 2
       then r.val = 2 else r.val = 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n) (hn_eq : n = 4)
    (hrange : ∀ i, i < 4 → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000), ∀ r, max_operations nums = ok r →
      (if elem (vals nums) 0 + elem (vals nums) 1 = elem (vals nums) 2 + elem (vals nums) 3 ∨
          elem (vals nums) 0 + elem (vals nums) 3 = elem (vals nums) 1 + elem (vals nums) 2
       then r.val = 2 else r.val = 1)) := by
  sorry

/-- Whenever the function returns a result r, r = floor(len(nums)/2).
  Preconditions: nums is a slice of i64 with n = len(nums), 2 <= n <= 2000, 1 <= nums[i] <= 1000 for every i, and there exists an integer c such that nums[i] = c for every i with 0 <= i < n. -/
theorem spec_7 (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hconst : ∃ c : ℤ, ∀ i, i < n → elem (vals nums) i = c) :
    ∀ r, max_operations nums = ok r → r.val = ((n / 2 : Nat) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hconst : ∃ c : ℤ, ∀ i, i < n → elem (vals nums) i = c), ∀ r, max_operations nums = ok r → r.val = ((n / 2 : Nat) : ℤ)) := by
  sorry

/-- Let rev be the slice of length n with rev[i] = nums[n-1-i] for every i with 0 <= i < n. If the function returns r on nums and returns r' on rev, then r = r'.
  Preconditions: nums is a slice of i64 with n = len(nums), 2 <= n <= 2000, and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_8 (nums rev : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hrev : vals rev = (vals nums).reverse) :
    ∀ r r', max_operations nums = ok r → max_operations rev = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums rev : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hrev : vals rev = (vals nums).reverse), ∀ r r', max_operations nums = ok r → max_operations rev = ok r' → r = r') := by
  sorry

/-- If the function returns r on nums and returns r' on shifted, then r = r'.
  Preconditions: nums is a slice of i64 with n = len(nums), 2 <= n <= 2000, 1 <= nums[i] <= 1000 for every i, c is an integer such that 1 <= nums[i]+c <= 1000 for every i, and shifted[i] = nums[i]+c for every i with 0 <= i < n. -/
theorem spec_9 (nums shifted : Slice I64) (n : Nat) (c : ℤ)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hc : ∀ i, i < n → 1 ≤ elem (vals nums) i + c ∧ elem (vals nums) i + c ≤ 1000)
    (hshift : vals shifted = (vals nums).map (fun v => v + c)) :
    ∀ r r', max_operations nums = ok r → max_operations shifted = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums shifted : Slice I64) (n : Nat) (c : ℤ)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hc : ∀ i, i < n → 1 ≤ elem (vals nums) i + c ∧ elem (vals nums) i + c ≤ 1000)
    (hshift : vals shifted = (vals nums).map (fun v => v + c)), ∀ r r', max_operations nums = ok r → max_operations shifted = ok r' → r = r') := by
  sorry

/-- If the function returns r on nums and returns r' on scaled, then r = r'.
  Preconditions: nums is a slice of i64 with n = len(nums), 2 <= n <= 2000, 1 <= nums[i] <= 1000 for every i, c is a positive integer such that 1 <= c*nums[i] <= 1000 for every i, and scaled[i] = c*nums[i] for every i with 0 <= i < n. -/
theorem spec_10 (nums scaled : Slice I64) (n : Nat) (c : ℤ)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hc_pos : 0 < c)
    (hc : ∀ i, i < n → 1 ≤ c * elem (vals nums) i ∧ c * elem (vals nums) i ≤ 1000)
    (hscale : vals scaled = (vals nums).map (fun v => c * v)) :
    ∀ r r', max_operations nums = ok r → max_operations scaled = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums scaled : Slice I64) (n : Nat) (c : ℤ)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hc_pos : 0 < c)
    (hc : ∀ i, i < n → 1 ≤ c * elem (vals nums) i ∧ c * elem (vals nums) i ≤ 1000)
    (hscale : vals scaled = (vals nums).map (fun v => c * v)), ∀ r r', max_operations nums = ok r → max_operations scaled = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r, there exist an integer S and a sequence of exactly r allowed current-interval deletions starting from [0,len(nums)), where the current interval starts as [0,len(nums)) and a deletion removes either the first two, the last two, or the first and last elements of the current interval, then updates the interval by removing exactly those indices, and every deletion has score S.
  Preconditions: nums is a slice of i64 with n = len(nums), 2 <= n <= 2000, and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_11 (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000) :
    ∀ r, max_operations nums = ok r →
      ∃ k : Nat, r.val = (k : ℤ) ∧
        ∃ S : ℤ, delSeq (vals nums) k 0 (vals nums).length S := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000), ∀ r, max_operations nums = ok r →
      ∃ k : Nat, r.val = (k : ℤ) ∧
        ∃ S : ℤ, delSeq (vals nums) k 0 (vals nums).length S) := by
  sorry

/-- Whenever the function returns a result r, there is no integer k with r < k <= floor(len(nums)/2) for which there exist an integer S and a sequence of k allowed current-interval deletions starting from [0,len(nums)), each deletion having score S.
  Preconditions: nums is a slice of i64 with n = len(nums), 2 <= n <= 2000, and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_12 (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000) :
    ∀ r, max_operations nums = ok r →
      ¬ ∃ k : Nat, r.val < (k : ℤ) ∧ (k : ℤ) ≤ ((n / 2 : Nat) : ℤ) ∧
        ∃ S : ℤ, delSeq (vals nums) k 0 (vals nums).length S := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000), ∀ r, max_operations nums = ok r →
      ¬ ∃ k : Nat, r.val < (k : ℤ) ∧ (k : ℤ) ≤ ((n / 2 : Nat) : ℤ) ∧
        ∃ S : ℤ, delSeq (vals nums) k 0 (vals nums).length S) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exist S in the set { nums[0]+nums[1], nums[len(nums)-2]+nums[len(nums)-1], nums[0]+nums[len(nums)-1] } and a sequence of exactly r allowed current-interval deletions starting from [0,len(nums)), each deletion having score S.
  Preconditions: nums is a slice of i64 with n = len(nums), 2 <= n <= 2000, and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_13 (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000) :
    ∀ r, max_operations nums = ok r → 0 < r.val →
      ∃ k : Nat, r.val = (k : ℤ) ∧
        ∃ S : ℤ,
          (S = elem (vals nums) 0 + elem (vals nums) 1 ∨
              S = elem (vals nums) (n - 2) + elem (vals nums) (n - 1) ∨
              S = elem (vals nums) 0 + elem (vals nums) (n - 1)) ∧
            delSeq (vals nums) k 0 (vals nums).length S := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 2000)
    (hrange : ∀ i, i < n → 1 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000), ∀ r, max_operations nums = ok r → 0 < r.val →
      ∃ k : Nat, r.val = (k : ℤ) ∧
        ∃ S : ℤ,
          (S = elem (vals nums) 0 + elem (vals nums) 1 ∨
              S = elem (vals nums) (n - 2) + elem (vals nums) (n - 1) ∨
              S = elem (vals nums) 0 + elem (vals nums) (n - 1)) ∧
            delSeq (vals nums) k 0 (vals nums).length S) := by
  sorry

end AegisSpec.MaxOperations
