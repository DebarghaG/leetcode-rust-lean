import Aegis.MaxEqualFreq.Code.Funs

/-!
# Specifications of `Aegis.MaxEqualFreq.max_equal_freq`

LeetCode problem `maximum-equal-frequency`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxEqualFreq

namespace AegisSpec.MaxEqualFreq

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def occCount (l : List Int) (v : Int) : Nat := (l.filter (fun x => decide (x = v))).length

def Balanced (l : List Int) : Prop :=
  ∀ v w : Int, 0 < occCount l v → 0 < occCount l w → occCount l v = occCount l w

def Unbalanced (l : List Int) : Prop :=
  ∃ v w : Int, 0 < occCount l v ∧ 0 < occCount l w ∧ occCount l v ≠ occCount l w

def delPrefix (l : List Int) (k j : Nat) : List Int := (l.take k).eraseIdx j

def AdmissiblePrefix (l : List Int) (k : Nat) : Prop :=
  ∃ j : Nat, j < k ∧ Balanced (delPrefix l k j)

def AdmissibleWhole (l : List Int) : Prop :=
  ∃ j : Nat, j < l.length ∧ Balanced (l.eraseIdx j)

def IsMaxAdmissiblePrefix (l : List Int) (k : Nat) : Prop :=
  1 ≤ k ∧ k ≤ l.length ∧ AdmissiblePrefix l k ∧
    ∀ k' : Nat, 1 ≤ k' → k' ≤ l.length → AdmissiblePrefix l k' → k' ≤ k

noncomputable def maxAdmissible (l : List Int) : Nat :=
  @Nat.findGreatest (fun k => 1 ≤ k ∧ k ≤ l.length ∧ AdmissiblePrefix l k)
    (Classical.decPred _) l.length

/-- Let n = len(nums). For an integer k with 1 <= k <= n, call the prefix nums[0..k) admissible if there exists an index j with 0 <= j < k such that, after deleting the single entry nums[j] from this prefix, every integer value that still occurs among the remaining k-1 entries occurs the same positive number of times (the condition is vacuously true when nothing remains, i.e. when k=1). The function returns a result r and r = max { k | 1 <= k <= n and nums[0..k) is admissible }.
  Preconditions: nums is a slice of i64 with 2 <= len(nums) <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000) :
    ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      IsMaxAdmissiblePrefix (vals nums) r.val.toNat ∧
      r.val = (maxAdmissible (vals nums) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000), ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      IsMaxAdmissiblePrefix (vals nums) r.val.toNat ∧
      r.val = (maxAdmissible (vals nums) : Int)) := by
  sorry

/-- The function returns a result r, and 1 <= r <= len(nums).
  Preconditions: nums is a slice of i64 with 2 <= len(nums) <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000) :
    ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      1 ≤ r.val ∧ r.val ≤ ((vals nums).length : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000), ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      1 ≤ r.val ∧ r.val ≤ ((vals nums).length : Int)) := by
  sorry

/-- The function returns a result r, and r >= min(len(nums), 3). Equivalently, r >= len(nums) when len(nums) <= 3, and r >= 3 when len(nums) >= 3.
  Preconditions: nums is a slice of i64 with 2 <= len(nums) <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000) :
    ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      (((min (vals nums).length 3 : Nat) : Int) ≤ r.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000), ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      (((min (vals nums).length 3 : Nat) : Int) ≤ r.val)) := by
  sorry

/-- The function returns a result r, and there exists an index j with 0 <= j < r such that, after deleting nums[j] from the prefix nums[0..r), every integer value still occurring among the remaining r-1 entries occurs the same positive number of times.
  Preconditions: nums is a slice of i64 with 2 <= len(nums) <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000) :
    ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      ∃ j : Nat, j < r.val.toNat ∧
        Balanced (delPrefix (vals nums) r.val.toNat j) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000), ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      ∃ j : Nat, j < r.val.toNat ∧
        Balanced (delPrefix (vals nums) r.val.toNat j)) := by
  sorry

/-- The function returns a result r, and for every integer k with r < k <= len(nums), the prefix nums[0..k) is not admissible: that is, for every index j with 0 <= j < k, after deleting nums[j] from nums[0..k) there exist two integer values that still occur among the remaining k-1 entries with different positive occurrence counts.
  Preconditions: nums is a slice of i64 with 2 <= len(nums) <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000) :
    ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      ∀ k : Nat, r.val < (k : Int) → k ≤ (vals nums).length →
        ∀ j : Nat, j < k → Unbalanced (delPrefix (vals nums) k j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000), ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      ∀ k : Nat, r.val < (k : Int) → k ≤ (vals nums).length →
        ∀ j : Nat, j < k → Unbalanced (delPrefix (vals nums) k j)) := by
  sorry

/-- If nums[i] = nums[0] for every i with 0 <= i < len(nums), then the function returns a result r with r = len(nums).
  Preconditions: nums is a slice of i64 with 2 <= len(nums) <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000)
    (hconst : ∀ i : Nat, i < (vals nums).length →
      (vals nums).getD i 0 = (vals nums).getD 0 0) :
    ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      r.val = ((vals nums).length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000)
    (hconst : ∀ i : Nat, i < (vals nums).length →
      (vals nums).getD i 0 = (vals nums).getD 0 0), ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      r.val = ((vals nums).length : Int)) := by
  sorry

/-- If nums[i] != nums[j] for every pair of indices i,j with 0 <= i < j < len(nums), then the function returns a result r with r = len(nums).
  Preconditions: nums is a slice of i64 with 2 <= len(nums) <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000)
    (hdistinct : ∀ i j : Nat, i < j → j < (vals nums).length →
      (vals nums).getD i 0 ≠ (vals nums).getD j 0) :
    ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      r.val = ((vals nums).length : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000)
    (hdistinct : ∀ i j : Nat, i < j → j < (vals nums).length →
      (vals nums).getD i 0 ≠ (vals nums).getD j 0), ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      r.val = ((vals nums).length : Int)) := by
  sorry

/-- The function returns a result r, and r = len(nums) if and only if there exists an index j with 0 <= j < len(nums) such that, after deleting nums[j] from the whole array nums[0..len(nums)), every integer value still occurring among the remaining len(nums)-1 entries occurs the same positive number of times. Equivalently, if no such j exists then r < len(nums).
  Preconditions: nums is a slice of i64 with 2 <= len(nums) <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000) :
    ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      (r.val = ((vals nums).length : Int) ↔ AdmissibleWhole (vals nums)) ∧
      (¬ AdmissibleWhole (vals nums) →
        r.val < ((vals nums).length : Int)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000), ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      (r.val = ((vals nums).length : Int) ↔ AdmissibleWhole (vals nums)) ∧
      (¬ AdmissibleWhole (vals nums) →
        r.val < ((vals nums).length : Int))) := by
  sorry

/-- Whenever max_equal_freq(nums) returns r and max_equal_freq(nums') returns r', we have r = r'.
  Preconditions: nums and nums' are slices of i64, each satisfying 2 <= len <= 100000 and all entries between 1 and 100000, with len(nums)=len(nums'), and for all i,j with 0 <= i,j < len(nums), nums[i]=nums[j] if and only if nums'[i]=nums'[j]. -/
theorem spec_9 (nums nums' : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000)
    (hlen' : 2 ≤ (vals nums').length) (hlen_le' : (vals nums').length ≤ 100000)
    (hbound' : ∀ i : Nat, i < (vals nums').length →
      1 ≤ (vals nums').getD i 0 ∧ (vals nums').getD i 0 ≤ 100000)
    (hlen_eq : (vals nums).length = (vals nums').length)
    (hpattern : ∀ i j : Nat, i < (vals nums).length → j < (vals nums).length →
      ((vals nums).getD i 0 = (vals nums).getD j 0 ↔
        (vals nums').getD i 0 = (vals nums').getD j 0)) :
    ∀ r r' : Std.I64, max_equal_freq nums = ok r → max_equal_freq nums' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000)
    (hlen' : 2 ≤ (vals nums').length) (hlen_le' : (vals nums').length ≤ 100000)
    (hbound' : ∀ i : Nat, i < (vals nums').length →
      1 ≤ (vals nums').getD i 0 ∧ (vals nums').getD i 0 ≤ 100000)
    (hlen_eq : (vals nums).length = (vals nums').length)
    (hpattern : ∀ i j : Nat, i < (vals nums).length → j < (vals nums).length →
      ((vals nums).getD i 0 = (vals nums).getD j 0 ↔
        (vals nums').getD i 0 = (vals nums').getD j 0)), ∀ r r' : Std.I64, max_equal_freq nums = ok r → max_equal_freq nums' = ok r' →
      r.val = r'.val) := by
  sorry

/-- The function returns a result r for every nums satisfying the preconditions; it never fails, i.e. it does not panic, access out of bounds, or overflow the i64 arithmetic.
  Preconditions: nums is a slice of i64 with 2 <= len(nums) <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000) :
    ∃ r : Std.I64, max_equal_freq nums = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000), ∃ r : Std.I64, max_equal_freq nums = ok r) := by
  sorry

/-- If len(nums) = 4, then the function returns r = 3 exactly when there are exactly two distinct values v and w (v != w) such that v occurs exactly twice and w occurs exactly twice among the four entries; in every other length-4 case it returns r = 4.
  Preconditions: nums is a slice of i64 with 2 <= len(nums) <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000)
    (hlen4 : (vals nums).length = 4) :
    ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      (r.val = 3 ↔ ∃ v w : Int, v ≠ w ∧
        occCount (vals nums) v = 2 ∧ occCount (vals nums) w = 2) ∧
      ((¬ ∃ v w : Int, v ≠ w ∧
        occCount (vals nums) v = 2 ∧ occCount (vals nums) w = 2) →
        r.val = 4) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hbound : ∀ i : Nat, i < (vals nums).length →
      1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 100000)
    (hlen4 : (vals nums).length = 4), ∃ r : Std.I64, max_equal_freq nums = ok r ∧
      (r.val = 3 ↔ ∃ v w : Int, v ≠ w ∧
        occCount (vals nums) v = 2 ∧ occCount (vals nums) w = 2) ∧
      ((¬ ∃ v w : Int, v ≠ w ∧
        occCount (vals nums) v = 2 ∧ occCount (vals nums) w = 2) →
        r.val = 4)) := by
  sorry

end AegisSpec.MaxEqualFreq
