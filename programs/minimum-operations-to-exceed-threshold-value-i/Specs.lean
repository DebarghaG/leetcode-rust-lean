import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-exceed-threshold-value-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinOperations (min_operations)

namespace AegisSpec.MinOperations

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def len (nums : Slice Std.I64) : Nat := nums.val.length

def elem (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

def elemL (l : List Int) (i : Nat) : Int := l.getD i 0

def countLt (k : Int) (l : List Int) : Nat := l.countP (fun x => decide (x < k))

def countGe (k : Int) (l : List Int) : Nat := l.countP (fun x => decide (k ≤ x))

def countEq (v : Int) (l : List Int) : Nat := l.countP (fun x => decide (x = v))

def Nondecreasing (a : List Int) : Prop := a.Pairwise (fun x y => x ≤ y)

def SameMultiset (a : List Int) (nums : Slice Std.I64) : Prop :=
  a.length = len nums ∧ ∀ v : Int, countEq v a = countEq v (vals nums)

def removeMin (l : List Int) : List Int :=
  match l with
  | [] => []
  | x :: xs => (x :: xs).erase (List.foldr min x xs)

def removeMins : Nat → List Int → List Int
  | 0, l => l
  | n + 1, l => removeMins n (removeMin l)

def InsertAt (nums nums' : Slice Std.I64) (x : Int) : Prop :=
  ∃ i, i ≤ len nums ∧ vals nums' = (vals nums).take i ++ [x] ++ (vals nums).drop i

def UniqueGe (nums : Slice Std.I64) (k : Int) : Prop :=
  ∃ j, j < len nums ∧ k ≤ elem nums j ∧ ∀ j', j' < len nums → k ≤ elem nums j' → j' = j

/-- The function returns a result r (it does not fail), and r equals the number of indices i with 0 <= i < len(nums) such that nums[i] < k. This is the minimum number of operations needed to make every remaining element of nums greater than or equal to k, where each operation removes one occurrence of the current smallest element.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; there exists j with 0 <= j < len(nums) and nums[j] >= k. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j) :
    ∃ r, min_operations nums k = ok r ∧ r.val = (countLt k.val (vals nums) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j), ∃ r, min_operations nums k = ok r ∧ r.val = (countLt k.val (vals nums) : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail due to arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; there exists j with 0 <= j < len(nums) and nums[j] >= k. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j) :
    ∃ r, min_operations nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j), ∃ r, min_operations nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums). In addition, because some index j satisfies nums[j] >= k, r <= len(nums) - 1.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; there exists j with 0 <= j < len(nums) and nums[j] >= k. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j) :
    ∀ r, min_operations nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (len nums : Int) ∧ r.val ≤ (len nums : Int) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j), ∀ r, min_operations nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (len nums : Int) ∧ r.val ≤ (len nums : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every index i with 0 <= i < len(nums), nums[i] >= k.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; there exists j with 0 <= j < len(nums) and nums[j] >= k. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j) :
    ∀ r, min_operations nums k = ok r →
      (r.val = 0 ↔ ∀ i, i < len nums → k.val ≤ elem nums i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j), ∀ r, min_operations nums k = ok r →
      (r.val = 0 ↔ ∀ i, i < len nums → k.val ≤ elem nums i)) := by
  sorry

/-- If there is exactly one index j with 0 <= j < len(nums) such that nums[j] >= k, then whenever the function returns a result r, r = len(nums) - 1.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; there is exactly one index j with 0 <= j < len(nums) and nums[j] >= k. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (huniq : UniqueGe nums k.val) :
    ∀ r, min_operations nums k = ok r → r.val = (len nums : Int) - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (huniq : UniqueGe nums k.val), ∀ r, min_operations nums k = ok r → r.val = (len nums : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums) - m, where m is the number of indices i with 0 <= i < len(nums) and nums[i] >= k.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; there exists j with 0 <= j < len(nums) and nums[j] >= k. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j) :
    ∀ r, min_operations nums k = ok r →
      r.val = (len nums : Int) - (countGe k.val (vals nums) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j), ∀ r, min_operations nums k = ok r →
      r.val = (len nums : Int) - (countGe k.val (vals nums) : Int)) := by
  sorry

/-- If min_operations(nums, k) returns r and min_operations(nums', k) returns r', then r = r'.
  Preconditions: Consider two slices nums and nums' of the same length and an integer k such that the preconditions hold for nums and k and also for nums' and k. Suppose that for every integer v, the number of indices i with 0 <= i < len(nums) and nums[i] = v equals the number of indices i with 0 <= i < len(nums') and nums'[i] = v. -/
theorem spec_7 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j)
    (hlen'_lo : 1 ≤ len nums') (hlen'_hi : len nums' ≤ 50)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 1000000000)
    (hge' : ∃ j, j < len nums' ∧ k.val ≤ elem nums' j)
    (hlen_eq : len nums = len nums')
    (hperm : ∀ v : Int, countEq v (vals nums) = countEq v (vals nums')) :
    ∀ r r', min_operations nums k = ok r → min_operations nums' k = ok r' → r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j)
    (hlen'_lo : 1 ≤ len nums') (hlen'_hi : len nums' ≤ 50)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 1000000000)
    (hge' : ∃ j, j < len nums' ∧ k.val ≤ elem nums' j)
    (hlen_eq : len nums = len nums')
    (hperm : ∀ v : Int, countEq v (vals nums) = countEq v (vals nums')), ∀ r r', min_operations nums k = ok r → min_operations nums' k = ok r' → r.val = r'.val) := by
  sorry

/-- If min_operations(nums, k1) returns r1 and min_operations(nums, k2) returns r2, then r1 <= r2.
  Preconditions: Let nums be a slice and k1, k2 be integers such that nums and k1 satisfy the preconditions, nums and k2 satisfy the preconditions, and k1 <= k2. -/
theorem spec_8 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk1_lo : 1 ≤ k1.val) (hk1_hi : k1.val ≤ 1000000000)
    (hge1 : ∃ j, j < len nums ∧ k1.val ≤ elem nums j)
    (hk2_lo : 1 ≤ k2.val) (hk2_hi : k2.val ≤ 1000000000)
    (hge2 : ∃ j, j < len nums ∧ k2.val ≤ elem nums j)
    (hle : k1.val ≤ k2.val) :
    ∀ r1 r2, min_operations nums k1 = ok r1 → min_operations nums k2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk1_lo : 1 ≤ k1.val) (hk1_hi : k1.val ≤ 1000000000)
    (hge1 : ∃ j, j < len nums ∧ k1.val ≤ elem nums j)
    (hk2_lo : 1 ≤ k2.val) (hk2_hi : k2.val ≤ 1000000000)
    (hge2 : ∃ j, j < len nums ∧ k2.val ≤ elem nums j)
    (hle : k1.val ≤ k2.val), ∀ r1 r2, min_operations nums k1 = ok r1 → min_operations nums k2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- If min_operations(nums, k) returns r and min_operations(nums', k) returns r', then r' = r + 1.
  Preconditions: Let nums be a slice and k an integer satisfying the preconditions, with len(nums) <= 49. Let nums' be any slice obtained by inserting one extra element x at any position of nums, where 1 <= x < k, and suppose nums' and k satisfy the preconditions, in particular len(nums') <= 50. -/
theorem spec_9 (nums nums' : Slice Std.I64) (k : Std.I64) (x : Int)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j)
    (hlen49 : len nums ≤ 49)
    (hx_lo : 1 ≤ x) (hx_lt : x < k.val)
    (hins : InsertAt nums nums' x)
    (hlen'_lo : 1 ≤ len nums') (hlen'_hi : len nums' ≤ 50)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 1000000000)
    (hge' : ∃ j, j < len nums' ∧ k.val ≤ elem nums' j) :
    ∀ r r', min_operations nums k = ok r → min_operations nums' k = ok r' →
      r'.val = r.val + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (x : Int)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j)
    (hlen49 : len nums ≤ 49)
    (hx_lo : 1 ≤ x) (hx_lt : x < k.val)
    (hins : InsertAt nums nums' x)
    (hlen'_lo : 1 ≤ len nums') (hlen'_hi : len nums' ≤ 50)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 1000000000)
    (hge' : ∃ j, j < len nums' ∧ k.val ≤ elem nums' j), ∀ r r', min_operations nums k = ok r → min_operations nums' k = ok r' →
      r'.val = r.val + 1) := by
  sorry

/-- If min_operations(nums, k) returns r and min_operations(nums', k) returns r', then r' = r.
  Preconditions: Let nums be a slice and k an integer satisfying the preconditions, with len(nums) <= 49. Let nums' be any slice obtained by inserting one extra element x at any position of nums, where k <= x <= 10^9, and suppose nums' and k satisfy the preconditions. -/
theorem spec_10 (nums nums' : Slice Std.I64) (k : Std.I64) (x : Int)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j)
    (hlen49 : len nums ≤ 49)
    (hx_lo : k.val ≤ x) (hx_hi : x ≤ 1000000000)
    (hins : InsertAt nums nums' x)
    (hlen'_lo : 1 ≤ len nums') (hlen'_hi : len nums' ≤ 50)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 1000000000)
    (hge' : ∃ j, j < len nums' ∧ k.val ≤ elem nums' j) :
    ∀ r r', min_operations nums k = ok r → min_operations nums' k = ok r' → r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (x : Int)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j)
    (hlen49 : len nums ≤ 49)
    (hx_lo : k.val ≤ x) (hx_hi : x ≤ 1000000000)
    (hins : InsertAt nums nums' x)
    (hlen'_lo : 1 ≤ len nums') (hlen'_hi : len nums' ≤ 50)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 1000000000)
    (hge' : ∃ j, j < len nums' ∧ k.val ≤ elem nums' j), ∀ r r', min_operations nums k = ok r → min_operations nums' k = ok r' → r'.val = r.val) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exists an index i with 0 <= i < len(nums) such that nums[i] < k.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; there exists j with 0 <= j < len(nums) and nums[j] >= k. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j) :
    ∀ r, min_operations nums k = ok r → 0 < r.val →
      ∃ i, i < len nums ∧ elem nums i < k.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j), ∀ r, min_operations nums k = ok r → 0 < r.val →
      ∃ i, i < len nums ∧ elem nums i < k.val) := by
  sorry

/-- Let a be any nondecreasing list of length len(nums) whose multiset of entries is the same as the multiset of entries of nums (equivalently, a is obtained by sorting nums). Whenever the function returns a result r, 0 <= r <= len(nums), for every i with 0 <= i < r we have a[i] < k, and for every i with r <= i < len(nums) we have a[i] >= k.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; there exists j with 0 <= j < len(nums) and nums[j] >= k. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j)
    (a : List Int) (hsorted : Nondecreasing a) (hmult : SameMultiset a nums) :
    ∀ r, min_operations nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (len nums : Int) ∧
        (∀ i, i < r.val.toNat → elemL a i < k.val) ∧
        (∀ i, r.val.toNat ≤ i → i < len nums → k.val ≤ elemL a i) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j)
    (a : List Int) (hsorted : Nondecreasing a) (hmult : SameMultiset a nums), ∀ r, min_operations nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (len nums : Int) ∧
        (∀ i, i < r.val.toNat → elemL a i < k.val) ∧
        (∀ i, r.val.toNat ≤ i → i < len nums → k.val ≤ elemL a i)) := by
  sorry

/-- Whenever the function returns a result r, after performing r operations, where each operation removes one occurrence of the current smallest element of nums, every remaining element is at least k.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; there exists j with 0 <= j < len(nums) and nums[j] >= k. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j) :
    ∀ r, min_operations nums k = ok r →
      ∀ v, v ∈ removeMins r.val.toNat (vals nums) → k.val ≤ v := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j), ∀ r, min_operations nums k = ok r →
      ∀ v, v ∈ removeMins r.val.toNat (vals nums) → k.val ≤ v) := by
  sorry

/-- Whenever the function returns a result r, for every t with 0 <= t < r, after performing t operations, where each operation removes one occurrence of the current smallest element of nums, at least one element strictly smaller than k remains.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; there exists j with 0 <= j < len(nums) and nums[j] >= k. -/
theorem spec_14 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j) :
    ∀ r, min_operations nums k = ok r →
      ∀ t : Nat, (t : Int) < r.val → ∃ v, v ∈ removeMins t (vals nums) ∧ v < k.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 50)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hge : ∃ j, j < len nums ∧ k.val ≤ elem nums j), ∀ r, min_operations nums k = ok r →
      ∀ t : Nat, (t : Int) < r.val → ∃ v, v ∈ removeMins t (vals nums) ∧ v < k.val) := by
  sorry

end AegisSpec.MinOperations
