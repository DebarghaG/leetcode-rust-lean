import Aegis.ThirdMax.Code.Funs

/-!
# Specifications of `Aegis.ThirdMax.third_max`

LeetCode problem `third-maximum-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ThirdMax

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def D (nums : Slice Std.I64) : Finset Int := (vals nums).toFinset

  noncomputable def maxD (nums : Slice Std.I64) : Int :=
    if h : (D nums).Nonempty then (D nums).max' h else 0

  noncomputable def minD (nums : Slice Std.I64) : Int :=
    if h : (D nums).Nonempty then (D nums).min' h else 0

  def IsThirdLargest (nums : Slice Std.I64) (r : Int) : Prop :=
    r ∈ D nums ∧
      ((D nums).filter (fun d => r < d)).card = 2 ∧
      ∀ d ∈ D nums, ((D nums).filter (fun e => d < e)).card = 2 → d = r

  /-- Let D = { nums[i] | 0 <= i < len(nums) } be the set of distinct values occurring in nums. The function returns a result r and: if |D| >= 3, then r is the unique element of D such that the set { d in D | d > r } has exactly 2 elements; if |D| < 3, then r = max(D), the largest element of D.
    Preconditions: len(nums) >= 1, len(nums) <= 10000, and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 10000)
      (h_range : ∀ (i : Nat) (h : i < nums.val.length),
        -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647) :
      ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r ∧
        (if 3 ≤ (D nums).card then IsThirdLargest nums r.val
         else r.val = maxD nums) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 10000)
        (h_range : ∀ (i : Nat) (h : i < nums.val.length),
          -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647), ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r ∧
          (if 3 ≤ (D nums).card then IsThirdLargest nums r.val
           else r.val = maxD nums)) := by
    sorry

  /-- The function returns a result r; it does not fail.
    Preconditions: len(nums) >= 1, len(nums) <= 10000, and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 10000)
      (h_range : ∀ (i : Nat) (h : i < nums.val.length),
        -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647) :
      ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 10000)
        (h_range : ∀ (i : Nat) (h : i < nums.val.length),
          -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647), ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(nums) such that r = nums[i].
    Preconditions: len(nums) >= 1, len(nums) <= 10000, and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 10000)
      (h_range : ∀ (i : Nat) (h : i < nums.val.length),
        -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647) :
      ∀ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r →
        ∃ (i : Nat) (h : i < nums.val.length), r.val = (nums.val[i]'h).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 10000)
        (h_range : ∀ (i : Nat) (h : i < nums.val.length),
          -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647), ∀ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r →
          ∃ (i : Nat) (h : i < nums.val.length), r.val = (nums.val[i]'h).val) := by
    sorry

  /-- Whenever the function returns a result r, min(D) <= r <= max(D), where D = { nums[i] | 0 <= i < len(nums) }.
    Preconditions: len(nums) >= 1, len(nums) <= 10000, and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 10000)
      (h_range : ∀ (i : Nat) (h : i < nums.val.length),
        -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647) :
      ∀ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r →
        minD nums ≤ r.val ∧ r.val ≤ maxD nums := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 10000)
        (h_range : ∀ (i : Nat) (h : i < nums.val.length),
          -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647), ∀ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r →
          minD nums ≤ r.val ∧ r.val ≤ maxD nums) := by
    sorry

  /-- If the number of distinct values occurring in nums is less than 3, then the function returns a result r and r = max(D), where D = { nums[i] | 0 <= i < len(nums) }.
    Preconditions: len(nums) >= 1, len(nums) <= 10000, and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 10000)
      (h_range : ∀ (i : Nat) (h : i < nums.val.length),
        -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647) :
      (D nums).card < 3 →
        ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r ∧ r.val = maxD nums := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 10000)
        (h_range : ∀ (i : Nat) (h : i < nums.val.length),
          -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647), (D nums).card < 3 →
          ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r ∧ r.val = maxD nums) := by
    sorry

  /-- If the number of distinct values occurring in nums is at least 3, then the function returns a result r and r is the unique element of D for which the set { d in D | d > r } has exactly 2 elements, where D = { nums[i] | 0 <= i < len(nums) }.
    Preconditions: len(nums) >= 1, len(nums) <= 10000, and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 10000)
      (h_range : ∀ (i : Nat) (h : i < nums.val.length),
        -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647) :
      3 ≤ (D nums).card →
        ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r ∧ IsThirdLargest nums r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 10000)
        (h_range : ∀ (i : Nat) (h : i < nums.val.length),
          -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647), 3 ≤ (D nums).card →
          ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r ∧ IsThirdLargest nums r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = max(D) if and only if the number of distinct values occurring in nums is less than 3, where D = { nums[i] | 0 <= i < len(nums) }.
    Preconditions: len(nums) >= 1, len(nums) <= 10000, and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_7 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 10000)
      (h_range : ∀ (i : Nat) (h : i < nums.val.length),
        -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647) :
      ∀ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r →
        (r.val = maxD nums ↔ (D nums).card < 3) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 10000)
        (h_range : ∀ (i : Nat) (h : i < nums.val.length),
          -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647), ∀ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r →
          (r.val = maxD nums ↔ (D nums).card < 3)) := by
    sorry

  /-- If the number of distinct values occurring in nums is at least 3, then the function returns a result r and, for every d in D with d < r, the set { e in D | e > d } has at least 3 elements, where D = { nums[i] | 0 <= i < len(nums) }.
    Preconditions: len(nums) >= 1, len(nums) <= 10000, and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_8 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 10000)
      (h_range : ∀ (i : Nat) (h : i < nums.val.length),
        -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647) :
      3 ≤ (D nums).card →
        ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r ∧
          ∀ d ∈ D nums, d < r.val → 3 ≤ ((D nums).filter (fun e => d < e)).card := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 10000)
        (h_range : ∀ (i : Nat) (h : i < nums.val.length),
          -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647), 3 ≤ (D nums).card →
          ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r ∧
            ∀ d ∈ D nums, d < r.val → 3 ≤ ((D nums).filter (fun e => d < e)).card) := by
    sorry

  /-- For any two such arrays nums1 and nums2, if the set of distinct values occurring in nums1 equals the set of distinct values occurring in nums2, then whenever the function returns r1 on nums1 and r2 on nums2, r1 = r2.
    Preconditions: nums1 and nums2 each satisfy the problem constraints: their lengths are between 1 and 10000 and every element is in the range -2147483648 through 2147483647. -/
  theorem spec_9 (nums1 nums2 : Slice Std.I64)
      (h_len_ge1 : 1 ≤ nums1.val.length)
      (h_len_le1 : nums1.val.length ≤ 10000)
      (h_range1 : ∀ (i : Nat) (h : i < nums1.val.length),
        -2147483648 ≤ (nums1.val[i]'h).val ∧ (nums1.val[i]'h).val ≤ 2147483647)
      (h_len_ge2 : 1 ≤ nums2.val.length)
      (h_len_le2 : nums2.val.length ≤ 10000)
      (h_range2 : ∀ (i : Nat) (h : i < nums2.val.length),
        -2147483648 ≤ (nums2.val[i]'h).val ∧ (nums2.val[i]'h).val ≤ 2147483647)
      (h_same : D nums1 = D nums2) :
      ∀ (r1 r2 : Std.I64),
        Aegis.ThirdMax.third_max nums1 = ok r1 →
        Aegis.ThirdMax.third_max nums2 = ok r2 →
        r1.val = r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h_len_ge1 : 1 ≤ nums1.val.length)
        (h_len_le1 : nums1.val.length ≤ 10000)
        (h_range1 : ∀ (i : Nat) (h : i < nums1.val.length),
          -2147483648 ≤ (nums1.val[i]'h).val ∧ (nums1.val[i]'h).val ≤ 2147483647)
        (h_len_ge2 : 1 ≤ nums2.val.length)
        (h_len_le2 : nums2.val.length ≤ 10000)
        (h_range2 : ∀ (i : Nat) (h : i < nums2.val.length),
          -2147483648 ≤ (nums2.val[i]'h).val ∧ (nums2.val[i]'h).val ≤ 2147483647)
        (h_same : D nums1 = D nums2), ∀ (r1 r2 : Std.I64),
          Aegis.ThirdMax.third_max nums1 = ok r1 →
          Aegis.ThirdMax.third_max nums2 = ok r2 →
          r1.val = r2.val) := by
    sorry

  /-- If the number of distinct values occurring in nums is at least 3, then the function returns a result r and there exist indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums) such that nums[i] > nums[j] > r, and every index k with 0 <= k < len(nums) and nums[k] > r satisfies nums[k] = nums[i] or nums[k] = nums[j].
    Preconditions: len(nums) >= 1, len(nums) <= 10000, and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_10 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 10000)
      (h_range : ∀ (i : Nat) (h : i < nums.val.length),
        -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647) :
      3 ≤ (D nums).card →
        ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r ∧
          ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
            (nums.val[j]'hj).val < (nums.val[i]'hi).val ∧
            r.val < (nums.val[j]'hj).val ∧
            ∀ (k : Nat) (hk : k < nums.val.length),
              r.val < (nums.val[k]'hk).val →
                (nums.val[k]'hk).val = (nums.val[i]'hi).val ∨
                  (nums.val[k]'hk).val = (nums.val[j]'hj).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 10000)
        (h_range : ∀ (i : Nat) (h : i < nums.val.length),
          -2147483648 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 2147483647), 3 ≤ (D nums).card →
          ∃ r : Std.I64, Aegis.ThirdMax.third_max nums = ok r ∧
            ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
              (nums.val[j]'hj).val < (nums.val[i]'hi).val ∧
              r.val < (nums.val[j]'hj).val ∧
              ∀ (k : Nat) (hk : k < nums.val.length),
                r.val < (nums.val[k]'hk).val →
                  (nums.val[k]'hk).val = (nums.val[i]'hi).val ∨
                    (nums.val[k]'hk).val = (nums.val[j]'hj).val) := by
    sorry

  end AegisSpec.ThirdMax
