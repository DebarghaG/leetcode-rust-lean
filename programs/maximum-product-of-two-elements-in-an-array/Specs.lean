import Aegis.MaxProduct.Code.Funs

/-!
# Specifications of `Aegis.MaxProduct.max_product`

LeetCode problem `maximum-product-of-two-elements-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxProduct

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def nth (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

  def IsMaxEntry (M : Int) (l : List Int) : Prop := M ∈ l ∧ ∀ x ∈ l, x ≤ M

  def Pre (nums : Slice Std.I64) : Prop :=
    2 ≤ (vals nums).length ∧ (vals nums).length ≤ 500 ∧
      ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000

  /-- The function returns a result r, and r is the maximum of the set { (nums[i]-1)*(nums[j]-1) | 0 <= i < len(nums), 0 <= j < len(nums), i != j }. Equivalently, r is the largest value of (nums[i]-1)*(nums[j]-1) over all choices of two different indices i and j.
    Preconditions: 2 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
      (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000) :
      ∃ r, Aegis.MaxProduct.max_product nums = ok r ∧
        (∃ i j, i < (vals nums).length ∧ j < (vals nums).length ∧ i ≠ j ∧
          r.val = (nth nums i - 1) * (nth nums j - 1)) ∧
        (∀ i j, i < (vals nums).length → j < (vals nums).length → i ≠ j →
          (nth nums i - 1) * (nth nums j - 1) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
        (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000), ∃ r, Aegis.MaxProduct.max_product nums = ok r ∧
          (∃ i j, i < (vals nums).length ∧ j < (vals nums).length ∧ i ≠ j ∧
            r.val = (nth nums i - 1) * (nth nums j - 1)) ∧
          (∀ i j, i < (vals nums).length → j < (vals nums).length → i ≠ j →
            (nth nums i - 1) * (nth nums j - 1) ≤ r.val)) := by
    sorry

  /-- The function returns a result r; under these preconditions it does not fail from 64-bit arithmetic overflow, out-of-bounds indexing, or panic.
    Preconditions: 2 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
      (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000) :
      ∃ r, Aegis.MaxProduct.max_product nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
        (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000), ∃ r, Aegis.MaxProduct.max_product nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 998001.
    Preconditions: 2 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
      (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000) :
      ∀ r, Aegis.MaxProduct.max_product nums = ok r → 0 ≤ r.val ∧ r.val ≤ 998001 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
        (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000), ∀ r, Aegis.MaxProduct.max_product nums = ok r → 0 ≤ r.val ∧ r.val ≤ 998001) := by
    sorry

  /-- Whenever the function returns a result r, if M = max { nums[i] | 0 <= i < len(nums) }, then r <= (M-1)*(M-1).
    Preconditions: 2 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
      (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000) :
      ∀ r, Aegis.MaxProduct.max_product nums = ok r →
        ∀ M, IsMaxEntry M (vals nums) → r.val ≤ (M - 1) * (M - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
        (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000), ∀ r, Aegis.MaxProduct.max_product nums = ok r →
          ∀ M, IsMaxEntry M (vals nums) → r.val ≤ (M - 1) * (M - 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < len(nums), 0 <= j < len(nums), and i != j, we have (nums[i]-1)*(nums[j]-1) <= r.
    Preconditions: 2 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
      (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000) :
      ∀ r, Aegis.MaxProduct.max_product nums = ok r →
        ∀ i j, i < (vals nums).length → j < (vals nums).length → i ≠ j →
          (nth nums i - 1) * (nth nums j - 1) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
        (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000), ∀ r, Aegis.MaxProduct.max_product nums = ok r →
          ∀ i j, i < (vals nums).length → j < (vals nums).length → i ≠ j →
            (nth nums i - 1) * (nth nums j - 1) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i and j such that 0 <= i < len(nums), 0 <= j < len(nums), i != j, and r = (nums[i]-1)*(nums[j]-1).
    Preconditions: 2 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
      (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000) :
      ∀ r, Aegis.MaxProduct.max_product nums = ok r →
        ∃ i j, i < (vals nums).length ∧ j < (vals nums).length ∧ i ≠ j ∧
          r.val = (nth nums i - 1) * (nth nums j - 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
        (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000), ∀ r, Aegis.MaxProduct.max_product nums = ok r →
          ∃ i j, i < (vals nums).length ∧ j < (vals nums).length ∧ i ≠ j ∧
            r.val = (nth nums i - 1) * (nth nums j - 1)) := by
    sorry

  /-- Whenever the function returns a result r, let M1 be the largest value among the entries of nums, and let M2 be the largest value among the entries of nums after removing one occurrence of M1 (so if M1 occurs at least twice, M2 = M1). Then r = (M1-1)*(M2-1).
    Preconditions: 2 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
      (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000) :
      ∀ r, Aegis.MaxProduct.max_product nums = ok r →
        ∀ M1 M2, IsMaxEntry M1 (vals nums) → IsMaxEntry M2 ((vals nums).erase M1) →
          r.val = (M1 - 1) * (M2 - 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
        (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000), ∀ r, Aegis.MaxProduct.max_product nums = ok r →
          ∀ M1 M2, IsMaxEntry M1 (vals nums) → IsMaxEntry M2 ((vals nums).erase M1) →
            r.val = (M1 - 1) * (M2 - 1)) := by
    sorry

  /-- For every slice nums' with 2 <= len(nums') <= 500, every entry of nums' in [1,1000], and the same multiset of entries as nums, the result returned on nums' equals the result returned on nums.
    Preconditions: 2 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_8 (nums nums' : Slice Std.I64)
      (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
      (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (hlen2 : 2 ≤ (vals nums').length) (hlen2' : (vals nums').length ≤ 500)
      (hrange2 : ∀ i, i < (vals nums').length → 1 ≤ nth nums' i ∧ nth nums' i ≤ 1000)
      (hperm : (vals nums').Perm (vals nums)) :
      ∀ r, Aegis.MaxProduct.max_product nums = ok r →
        Aegis.MaxProduct.max_product nums' = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
        (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (hlen2 : 2 ≤ (vals nums').length) (hlen2' : (vals nums').length ≤ 500)
        (hrange2 : ∀ i, i < (vals nums').length → 1 ≤ nth nums' i ∧ nth nums' i ≤ 1000)
        (hperm : (vals nums').Perm (vals nums)), ∀ r, Aegis.MaxProduct.max_product nums = ok r →
          Aegis.MaxProduct.max_product nums' = ok r) := by
    sorry

  /-- For every slice nums' with len(nums') = len(nums), 1 <= nums'[i] <= 1000 for every i, and nums[i] <= nums'[i] for every i with 0 <= i < len(nums), the result returned on nums' is greater than or equal to the result returned on nums.
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_9 (nums nums' : Slice Std.I64)
      (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
      (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (hlen2 : (vals nums').length = (vals nums).length)
      (hrange2 : ∀ i, i < (vals nums').length → 1 ≤ nth nums' i ∧ nth nums' i ≤ 1000)
      (hmono : ∀ i, i < (vals nums).length → nth nums i ≤ nth nums' i) :
      ∀ r r', Aegis.MaxProduct.max_product nums = ok r →
        Aegis.MaxProduct.max_product nums' = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen : 2 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 500)
        (hrange : ∀ i, i < (vals nums).length → 1 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (hlen2 : (vals nums').length = (vals nums).length)
        (hrange2 : ∀ i, i < (vals nums').length → 1 ≤ nth nums' i ∧ nth nums' i ≤ 1000)
        (hmono : ∀ i, i < (vals nums).length → nth nums i ≤ nth nums' i), ∀ r r', Aegis.MaxProduct.max_product nums = ok r →
          Aegis.MaxProduct.max_product nums' = ok r' → r.val ≤ r'.val) := by
    sorry

  end AegisSpec.MaxProduct
