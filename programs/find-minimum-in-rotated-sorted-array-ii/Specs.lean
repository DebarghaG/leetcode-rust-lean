import Aegis.FindMin.Code.Funs

/-!
# Specifications of `Aegis.FindMin.find_min`

LeetCode problem `find-minimum-in-rotated-sorted-array-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindMin

open Aegis.FindMin

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def get (nums : Slice Std.I64) (i : ℕ) : Int := (vals nums).getD i 0

theorem get_eq (nums : Slice Std.I64) (i : ℕ) (h : i < nums.val.length) :
    get nums i = (nums.val[i]).val := by
  simp [get, vals, h]

theorem mem_vals_iff (nums : Slice Std.I64) (x : Int) :
    x ∈ vals nums ↔ ∃ i, i < nums.val.length ∧ get nums i = x := by
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp h
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hy
    refine ⟨i, hi, ?_⟩
    simp [get, vals, hi, hget, hxy]
  · rintro ⟨i, hi, rfl⟩
    refine List.mem_map.mpr ⟨nums.val[i], ?_, ?_⟩
    · simp
    · simp [get, vals, hi]

def Nondecreasing (l : List Int) : Prop := l.Pairwise (· ≤ ·)

def rotateAt (l : List Int) (k : ℕ) : List Int := l.drop k ++ l.take k

def IsRotatedNondecreasing (l : List Int) : Prop :=
  ∃ k, k < l.length ∧ Nondecreasing (rotateAt l k)

/-- Whenever find_min(nums) returns a result r, r is the minimum element of nums: there exists an index j with 0 <= j < len(nums) such that r = nums[j], and for every index i with 0 <= i < len(nums), r <= nums[i].
  Preconditions: The array nums satisfies the problem constraints: 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), -5000 <= nums[i] <= 5000; and nums is a cyclic rotation of a nondecreasing list, i.e. there exists k with 0 <= k < len(nums) such that the concatenation nums[k], nums[k+1], ..., nums[len(nums)-1], nums[0], ..., nums[k-1] is nondecreasing. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums)) :
    ∀ r, find_min nums = ok r →
      (∃ j, j < nums.val.length ∧ r.val = get nums j) ∧
      (∀ i, i < nums.val.length → r.val ≤ get nums i) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums)), ∀ r, find_min nums = ok r →
      (∃ j, j < nums.val.length ∧ r.val = get nums j) ∧
      (∀ i, i < nums.val.length → r.val ≤ get nums i)) := by
  sorry

/-- For every nums satisfying the preconditions, find_min(nums) returns a result r; it does not fail, overflow, go out of bounds, or panic.
  Preconditions: The array nums satisfies the problem constraints: 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), -5000 <= nums[i] <= 5000; and nums is a cyclic rotation of a nondecreasing list, i.e. there exists k with 0 <= k < len(nums) such that the concatenation nums[k], nums[k+1], ..., nums[len(nums)-1], nums[0], ..., nums[k-1] is nondecreasing. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums)) :
    ∃ r, find_min nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums)), ∃ r, find_min nums = ok r) := by
  sorry

/-- Whenever find_min(nums) returns a result r, r = nums[0].
  Preconditions: The array nums satisfies the problem constraints: 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), -5000 <= nums[i] <= 5000; nums is a cyclic rotation of a nondecreasing list, i.e. there exists k with 0 <= k < len(nums) such that the concatenation nums[k], nums[k+1], ..., nums[len(nums)-1], nums[0], ..., nums[k-1] is nondecreasing; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums))
    (hsorted : ∀ i, i < nums.val.length - 1 → get nums i ≤ get nums (i + 1)) :
    ∀ r, find_min nums = ok r → r.val = get nums 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums))
    (hsorted : ∀ i, i < nums.val.length - 1 → get nums i ≤ get nums (i + 1)), ∀ r, find_min nums = ok r → r.val = get nums 0) := by
  sorry

/-- Let d be the unique index with 0 <= d < len(nums)-1 and nums[d] > nums[d+1]. Whenever find_min(nums) returns a result r, r = nums[d+1].
  Preconditions: The array nums satisfies the problem constraints: 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), -5000 <= nums[i] <= 5000; nums is a cyclic rotation of a nondecreasing list, i.e. there exists k with 0 <= k < len(nums) such that the concatenation nums[k], nums[k+1], ..., nums[len(nums)-1], nums[0], ..., nums[k-1] is nondecreasing; and there exists an index d with 0 <= d < len(nums)-1 and nums[d] > nums[d+1]. Under the rotation condition this d is unique. -/
theorem spec_4 (nums : Slice Std.I64) (d : ℕ)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums))
    (hd : d + 1 < nums.val.length)
    (hdesc : get nums d > get nums (d + 1))
    (huniq : ∀ d', d' + 1 < nums.val.length → get nums d' > get nums (d' + 1) → d' = d) :
    ∀ r, find_min nums = ok r → r.val = get nums (d + 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (d : ℕ)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums))
    (hd : d + 1 < nums.val.length)
    (hdesc : get nums d > get nums (d + 1))
    (huniq : ∀ d', d' + 1 < nums.val.length → get nums d' > get nums (d' + 1) → d' = d), ∀ r, find_min nums = ok r → r.val = get nums (d + 1)) := by
  sorry

/-- Whenever find_min(nums) returns a result r and find_min(nums') returns a result r', we have r <= r'.
  Preconditions: The arrays nums and nums' both satisfy the problem constraints: each has length between 1 and 5000, all entries lie in [-5000,5000], and each is a cyclic rotation of a nondecreasing list. Also len(nums) = len(nums'), and for every i with 0 <= i < len(nums), nums[i] <= nums'[i]. -/
theorem spec_5 (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums))
    (hlen1' : 1 ≤ nums'.val.length)
    (hlen2' : nums'.val.length ≤ 5000)
    (hbounds' : ∀ x ∈ vals nums', -5000 ≤ x ∧ x ≤ 5000)
    (hrot' : IsRotatedNondecreasing (vals nums'))
    (hlen : nums.val.length = nums'.val.length)
    (hle : ∀ i, i < nums.val.length → get nums i ≤ get nums' i) :
    ∀ r r', find_min nums = ok r → find_min nums' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums))
    (hlen1' : 1 ≤ nums'.val.length)
    (hlen2' : nums'.val.length ≤ 5000)
    (hbounds' : ∀ x ∈ vals nums', -5000 ≤ x ∧ x ≤ 5000)
    (hrot' : IsRotatedNondecreasing (vals nums'))
    (hlen : nums.val.length = nums'.val.length)
    (hle : ∀ i, i < nums.val.length → get nums i ≤ get nums' i), ∀ r r', find_min nums = ok r → find_min nums' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- Whenever find_min(nums) returns a result r and find_min(nums') returns a result r', we have r = r'.
  Preconditions: The arrays nums and nums' both satisfy the problem constraints: each has length between 1 and 5000, all entries lie in [-5000,5000], and each is a cyclic rotation of a nondecreasing list. Also len(nums) = len(nums'), and nums' is a cyclic rotation of nums, i.e. there exists s with 0 <= s < len(nums) such that for every i with 0 <= i < len(nums), nums'[i] = nums[(i+s) mod len(nums)]. -/
theorem spec_6 (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums))
    (hlen1' : 1 ≤ nums'.val.length)
    (hlen2' : nums'.val.length ≤ 5000)
    (hbounds' : ∀ x ∈ vals nums', -5000 ≤ x ∧ x ≤ 5000)
    (hrot' : IsRotatedNondecreasing (vals nums'))
    (hlen : nums.val.length = nums'.val.length)
    (hshift : ∃ s, s < nums.val.length ∧
      ∀ i, i < nums.val.length → get nums' i = get nums ((i + s) % nums.val.length)) :
    ∀ r r', find_min nums = ok r → find_min nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums))
    (hlen1' : 1 ≤ nums'.val.length)
    (hlen2' : nums'.val.length ≤ 5000)
    (hbounds' : ∀ x ∈ vals nums', -5000 ≤ x ∧ x ≤ 5000)
    (hrot' : IsRotatedNondecreasing (vals nums'))
    (hlen : nums.val.length = nums'.val.length)
    (hshift : ∃ s, s < nums.val.length ∧
      ∀ i, i < nums.val.length → get nums' i = get nums ((i + s) % nums.val.length)), ∀ r r', find_min nums = ok r → find_min nums' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever find_min(nums) returns a result r, for every index k with 0 <= k < len(nums) such that the concatenation nums[k], nums[k+1], ..., nums[len(nums)-1], nums[0], ..., nums[k-1] is nondecreasing, we have r = nums[k].
  Preconditions: The array nums satisfies the problem constraints: 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), -5000 <= nums[i] <= 5000; and nums is a cyclic rotation of a nondecreasing list, i.e. there exists k with 0 <= k < len(nums) such that the concatenation nums[k], nums[k+1], ..., nums[len(nums)-1], nums[0], ..., nums[k-1] is nondecreasing. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums)) :
    ∀ r, find_min nums = ok r →
      ∀ k, k < nums.val.length → Nondecreasing (rotateAt (vals nums) k) →
        r.val = get nums k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums)), ∀ r, find_min nums = ok r →
      ∀ k, k < nums.val.length → Nondecreasing (rotateAt (vals nums) k) →
        r.val = get nums k) := by
  sorry

/-- Whenever find_min(nums) returns a result r and find_min(nums') returns a result r', we have r' = r + c.
  Preconditions: The array nums satisfies the problem constraints: 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), -5000 <= nums[i] <= 5000; and nums is a cyclic rotation of a nondecreasing list. Let c be an integer such that for every i with 0 <= i < len(nums), -5000 <= nums[i] + c <= 5000, and let nums' be the array with len(nums') = len(nums) and nums'[i] = nums[i] + c for every i. Then nums' also satisfies the problem constraints. -/
theorem spec_8 (nums nums' : Slice Std.I64) (c : Int)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums))
    (hc : ∀ i, i < nums.val.length → -5000 ≤ get nums i + c ∧ get nums i + c ≤ 5000)
    (hlen : nums'.val.length = nums.val.length)
    (hadd : ∀ i, i < nums.val.length → get nums' i = get nums i + c) :
    ∀ r r', find_min nums = ok r → find_min nums' = ok r' → r'.val = r.val + c := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : Int)
    (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 5000)
    (hbounds : ∀ x ∈ vals nums, -5000 ≤ x ∧ x ≤ 5000)
    (hrot : IsRotatedNondecreasing (vals nums))
    (hc : ∀ i, i < nums.val.length → -5000 ≤ get nums i + c ∧ get nums i + c ≤ 5000)
    (hlen : nums'.val.length = nums.val.length)
    (hadd : ∀ i, i < nums.val.length → get nums' i = get nums i + c), ∀ r r', find_min nums = ok r → find_min nums' = ok r' → r'.val = r.val + c) := by
  sorry

end AegisSpec.FindMin
