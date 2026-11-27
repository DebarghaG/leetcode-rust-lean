import Aegis.CountSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountSubarrays.count_subarrays`

LeetCode problem `count-strictly-increasing-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountSubarrays

open Aegis.CountSubarrays (count_subarrays)

def contents (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def Pre (nums : Slice Std.I64) : Prop :=
  1 ≤ nums.length ∧ nums.length ≤ 100000 ∧ ∀ v ∈ contents nums, 1 ≤ v ∧ v ≤ 1000000

def StrictlyIncr : List Int → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => a < b ∧ StrictlyIncr (b :: t)

def AdjLt (l : List Int) (k : Nat) : Prop :=
  ∃ a b : Int, l[k]? = some a ∧ l[k + 1]? = some b ∧ a < b

noncomputable def countIncPairs (l : List Int) : Nat := by
  classical
  exact ((Finset.range l.length).product (Finset.range l.length)).filter
    (fun p : Nat × Nat =>
      p.1 ≤ p.2 ∧ StrictlyIncr ((l.drop p.1).take (p.2 + 1 - p.1))) |>.card

def incPrefixLen : List Int → Nat
  | [] => 0
  | [_] => 1
  | a :: b :: t => if a < b then 1 + incPrefixLen (b :: t) else 1

def sumRunLens (l : List Int) : Nat :=
  ((List.range l.length).map (fun i => incPrefixLen (l.drop i))).sum

def IsMaximalIncRun (l : List Int) (a b : Nat) : Prop :=
  a ≤ b ∧ b < l.length ∧
    (∀ k, a ≤ k → k < b → AdjLt l k) ∧
    (a = 0 ∨ ¬ AdjLt l (a - 1)) ∧
    (b + 1 = l.length ∨ ¬ AdjLt l b)

def SegsFrom (n : Nat) : Nat → List (Nat × Nat) → Prop
  | start, [] => start = n
  | start, (a, _b) :: rest => a = start ∧ SegsFrom n (_b + 1) rest

def IsMaximalRunSegs (l : List Int) (segs : List (Nat × Nat)) : Prop :=
  SegsFrom l.length 0 segs ∧ ∀ p ∈ segs, IsMaximalIncRun l p.1 p.2

def triSum (segs : List (Nat × Nat)) : Nat :=
  (segs.map (fun p => (p.2 + 1 - p.1) * (p.2 + 2 - p.1) / 2)).sum

noncomputable def countAdjLt (l : List Int) : Nat := by
  classical
  exact ((Finset.range (l.length - 1)).filter (fun i => AdjLt l i)).card

def takeSlice (nums : Slice Std.I64) (p : Nat) : Slice Std.I64 :=
  Slice.from (nums.val.take p) (by
    have hlen : nums.val.length = nums.leng := Aeneas.Data.ListN.ListN_length nums.list
    have hbound : nums.leng ≤ Usize.max := nums.bound
    have htake : (nums.val.take p).length ≤ nums.val.length := by
      rw [List.length_take]
      exact Nat.min_le_right _ _
    omega)

def dropSlice (nums : Slice Std.I64) (p : Nat) : Slice Std.I64 :=
  Slice.from (nums.val.drop p) (by
    have hlen : nums.val.length = nums.leng := Aeneas.Data.ListN.ListN_length nums.list
    have hbound : nums.leng ≤ Usize.max := nums.bound
    have hdrop : (nums.val.drop p).length ≤ nums.val.length := by
      rw [List.length_drop]
      exact Nat.sub_le _ _
    omega)

/-- Whenever count_subarrays returns a result r, r equals the number of pairs (i, j) of integers such that 0 <= i <= j < len(nums) and, for every k with i <= k < j, nums[k] < nums[k+1].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_1 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r) :
    r.val = (countIncPairs (contents nums) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r), r.val = (countIncPairs (contents nums) : Int)) := by
  sorry

/-- For every nums satisfying the preconditions, count_subarrays returns a result r; it does not fail due to overflow, out-of-bounds access, or panic.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_2 (nums : Slice Std.I64) (hpre : Pre nums) :
    ∃ r : Std.I64, count_subarrays nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums), ∃ r : Std.I64, count_subarrays nums = ok r) := by
  sorry

/-- Whenever count_subarrays returns a result r, r >= len(nums).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_3 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r) :
    (nums.length : Int) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r), (nums.length : Int) ≤ r.val) := by
  sorry

/-- Whenever count_subarrays returns a result r, r <= len(nums) * (len(nums) + 1) / 2, where the arithmetic is in mathematical integers.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_4 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r) :
    r.val ≤ ((nums.length : Int) * ((nums.length : Int) + 1)) / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r), r.val ≤ ((nums.length : Int) * ((nums.length : Int) + 1)) / 2) := by
  sorry

/-- Whenever count_subarrays returns a result r, r = len(nums) * (len(nums) + 1) / 2 if and only if for every i with 0 <= i < len(nums) - 1, nums[i] < nums[i+1].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_5 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r) :
    r.val = ((nums.length : Int) * ((nums.length : Int) + 1)) / 2 ↔
      ∀ i : Nat, i < nums.length - 1 → AdjLt (contents nums) i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r), r.val = ((nums.length : Int) * ((nums.length : Int) + 1)) / 2 ↔
      ∀ i : Nat, i < nums.length - 1 → AdjLt (contents nums) i) := by
  sorry

/-- Whenever count_subarrays returns a result r, r = len(nums) if and only if for every i with 0 <= i < len(nums) - 1, nums[i] >= nums[i+1].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_6 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r) :
    r.val = (nums.length : Int) ↔
      ∀ i : Nat, i < nums.length - 1 → ¬ AdjLt (contents nums) i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r), r.val = (nums.length : Int) ↔
      ∀ i : Nat, i < nums.length - 1 → ¬ AdjLt (contents nums) i) := by
  sorry

/-- Whenever count_subarrays returns a result r, if the maximal strictly increasing runs of nums are the intervals [l_1, r_1], ..., [l_m, r_m] in increasing index order, where an interval [l, r] satisfies 0 <= l <= r < len(nums), nums[k] < nums[k+1] for every k with l <= k < r, and is maximal (l = 0 or nums[l-1] >= nums[l], and r = len(nums)-1 or nums[r] >= nums[r+1]), then r = sum_{t=1}^m ((r_t - l_t + 1) * (r_t - l_t + 2) / 2).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_7 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r) (segs : List (Nat × Nat))
    (hsegs : IsMaximalRunSegs (contents nums) segs) :
    r.val = (triSum segs : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r) (segs : List (Nat × Nat))
    (hsegs : IsMaximalRunSegs (contents nums) segs), r.val = (triSum segs : Int)) := by
  sorry

/-- Whenever count_subarrays returns a result r, for each i with 0 <= i < len(nums), let L_i be the largest integer m such that 1 <= m <= len(nums) - i and for every k with i <= k < i + m - 1, nums[k] < nums[k+1]. Then r = sum_{i=0}^{len(nums)-1} L_i.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_8 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r) :
    r.val = (sumRunLens (contents nums) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r), r.val = (sumRunLens (contents nums) : Int)) := by
  sorry

/-- Whenever count_subarrays returns a result r on nums, for every p with 1 <= p < len(nums) and nums[p-1] >= nums[p], if the function returns r_left on the prefix nums[0..p-1] and r_right on the suffix nums[p..len(nums)-1], then r = r_left + r_right.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_9 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r) (p : Nat) (hp1 : 1 ≤ p) (hp2 : p < nums.length)
    (hbreak : ¬ AdjLt (contents nums) (p - 1)) (r_left r_right : Std.I64)
    (hl : count_subarrays (takeSlice nums p) = ok r_left)
    (hr : count_subarrays (dropSlice nums p) = ok r_right) :
    r.val = r_left.val + r_right.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r) (p : Nat) (hp1 : 1 ≤ p) (hp2 : p < nums.length)
    (hbreak : ¬ AdjLt (contents nums) (p - 1)) (r_left r_right : Std.I64)
    (hl : count_subarrays (takeSlice nums p) = ok r_left)
    (hr : count_subarrays (dropSlice nums p) = ok r_right), r.val = r_left.val + r_right.val) := by
  sorry

/-- If for every i with 0 <= i < len(x) - 1, x[i] < x[i+1] if and only if y[i] < y[i+1], then whenever count_subarrays returns r_x on x and r_y on y, r_x = r_y.
  Preconditions: Both x and y satisfy 1 <= len(x) = len(y) <= 100000 and all elements of x and y are between 1 and 1000000. -/
theorem spec_10 (x y : Slice Std.I64) (hx_pre : Pre x) (hy_pre : Pre y)
    (hlen : x.length = y.length)
    (hmono : ∀ i : Nat, i < x.length - 1 → (AdjLt (contents x) i ↔ AdjLt (contents y) i))
    (r_x r_y : Std.I64) (hx : count_subarrays x = ok r_x)
    (hy : count_subarrays y = ok r_y) :
    r_x.val = r_y.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (x y : Slice Std.I64) (hx_pre : Pre x) (hy_pre : Pre y)
    (hlen : x.length = y.length)
    (hmono : ∀ i : Nat, i < x.length - 1 → (AdjLt (contents x) i ↔ AdjLt (contents y) i))
    (r_x r_y : Std.I64) (hx : count_subarrays x = ok r_x)
    (hy : count_subarrays y = ok r_y), r_x.val = r_y.val) := by
  sorry

/-- Whenever count_subarrays returns a result r, r >= len(nums) + (the number of indices i with 0 <= i < len(nums) - 1 and nums[i] < nums[i+1]).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_11 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r) :
    (nums.length : Int) + (countAdjLt (contents nums) : Int) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (h : count_subarrays nums = ok r), (nums.length : Int) + (countAdjLt (contents nums) : Int) ≤ r.val) := by
  sorry

end AegisSpec.CountSubarrays
