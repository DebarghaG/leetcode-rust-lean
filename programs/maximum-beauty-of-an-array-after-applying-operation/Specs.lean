import Aegis.MaximumBeauty.Code.Funs

/-!
# Specifications of `Aegis.MaximumBeauty.maximum_beauty`

LeetCode problem `maximum-beauty-of-an-array-after-applying-operation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumBeauty

  def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

  def valAt (nums : Slice I64) (i : Fin nums.val.length) : ℤ := (nums.val[i.val]'i.isLt).val

  def SpreadLE (nums : Slice I64) (d : ℤ) (S : Finset (Fin nums.val.length)) : Prop :=
    ∀ i ∈ S, ∀ j ∈ S, valAt nums i - valAt nums j ≤ d

  def RangeLE (nums : Slice I64) (d : ℤ) : Prop :=
    ∀ i (hi : i < nums.val.length), ∀ j (hj : j < nums.val.length),
      (nums.val[i]'hi).val - (nums.val[j]'hj).val ≤ d

  noncomputable def maxCard (nums : Slice I64) (d : ℤ) : ℕ := by
    classical
    exact ((Finset.univ : Finset (Finset (Fin nums.val.length))).filter
      (fun S => S.Nonempty ∧ SpreadLE nums d S)).sup (fun S => S.card)

  def countEq (nums : Slice I64) (v : ℤ) : ℕ :=
    (nums.val.filter (fun x => x.val = v)).length

  noncomputable def maxMult (nums : Slice I64) : ℕ :=
    (vals nums).toFinset.sup (fun v => countEq nums v)

  def countNear (nums : Slice I64) (k v : ℤ) : ℕ :=
    (nums.val.filter (fun x => x.val - k ≤ v ∧ v ≤ x.val + k)).length

  noncomputable def maxWindow (a : List ℤ) (d : ℤ) : ℕ := by
    classical
    exact ((Finset.univ : Finset (Fin a.length × Fin a.length)).filter
      (fun p => p.1 ≤ p.2 ∧ a.get p.2 - a.get p.1 ≤ d)).sup
      (fun p => p.2.val - p.1.val + 1)

  /-- The function returns a result r and r equals the maximum cardinality |S| over all nonempty sets S of indices with S ⊆ {0, 1, ..., len(nums)-1} such that (max_{i in S} nums[i]) - (min_{i in S} nums[i]) <= 2*k.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
  theorem spec_1 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        r.val = (maxCard nums (2 * k.val) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          r.val = (maxCard nums (2 * k.val) : ℤ)) := by
    sorry

  /-- The function returns a result r and 1 <= r <= len(nums).
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
  theorem spec_2 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not panic, does not overflow a 64-bit integer, and does not access memory out of bounds.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
  theorem spec_3 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r) := by
    sorry

  /-- The function returns a result r and r = max { |{i : 0 <= i < len(nums) and nums[i] = v}| : v is an integer }.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; k = 0. -/
  theorem spec_4 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk : k.val = 0) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        r.val = (maxMult nums : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk : k.val = 0), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          r.val = (maxMult nums : ℤ)) := by
    sorry

  /-- The function returns a result r and r = len(nums).
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000; (max_{0 <= i < len(nums)} nums[i]) - (min_{0 <= i < len(nums)} nums[i]) <= 2*k. -/
  theorem spec_5 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hrange : RangeLE nums (2 * k.val)) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        r.val = (nums.val.length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hrange : RangeLE nums (2 * k.val)), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          r.val = (nums.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r and r <= len(nums) - 1.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000; (max_{0 <= i < len(nums)} nums[i]) - (min_{0 <= i < len(nums)} nums[i]) > 2*k. -/
  theorem spec_6 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hrange : ¬ RangeLE nums (2 * k.val)) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        r.val ≤ (nums.val.length : ℤ) - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hrange : ¬ RangeLE nums (2 * k.val)), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          r.val ≤ (nums.val.length : ℤ) - 1) := by
    sorry

  /-- The function returns a result r and there exists an integer v such that r = |{i : 0 <= i < len(nums) and nums[i] - k <= v <= nums[i] + k}|.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
  theorem spec_7 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        ∃ v : ℤ, r.val = (countNear nums k.val v : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          ∃ v : ℤ, r.val = (countNear nums k.val v : ℤ)) := by
    sorry

  /-- The function returns a result r and for every nonempty set S ⊆ {0, 1, ..., len(nums)-1}, if (max_{i in S} nums[i]) - (min_{i in S} nums[i]) <= 2*k then |S| <= r.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
  theorem spec_8 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        ∀ S : Finset (Fin nums.val.length), S.Nonempty →
          SpreadLE nums (2 * k.val) S → (S.card : ℤ) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          ∀ S : Finset (Fin nums.val.length), S.Nonempty →
            SpreadLE nums (2 * k.val) S → (S.card : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r and there exists a nonempty set S ⊆ {0, 1, ..., len(nums)-1} with |S| = r and (max_{i in S} nums[i]) - (min_{i in S} nums[i]) <= 2*k.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
  theorem spec_9 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        ∃ S : Finset (Fin nums.val.length), S.Nonempty ∧
          SpreadLE nums (2 * k.val) S ∧ (S.card : ℤ) = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          ∃ S : Finset (Fin nums.val.length), S.Nonempty ∧
            SpreadLE nums (2 * k.val) S ∧ (S.card : ℤ) = r.val) := by
    sorry

  /-- The function returns a result r and r >= max { |{i : 0 <= i < len(nums) and nums[i] = v}| : v is an integer }.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
  theorem spec_10 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        (maxMult nums : ℤ) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          (maxMult nums : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r = 1 if and only if for every pair of distinct indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), |nums[i] - nums[j]| > 2*k.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
  theorem spec_11 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        (r.val = 1 ↔ ∀ i (hi : i < nums.val.length), ∀ j (hj : j < nums.val.length),
          i ≠ j → 2 * k.val < |(nums.val[i]'hi).val - (nums.val[j]'hj).val|) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          (r.val = 1 ↔ ∀ i (hi : i < nums.val.length), ∀ j (hj : j < nums.val.length),
            i ≠ j → 2 * k.val < |(nums.val[i]'hi).val - (nums.val[j]'hj).val|)) := by
    sorry

  /-- The function returns a result r and, letting a[0..len(nums)-1] be the nondecreasing rearrangement of nums (so a is a permutation of nums with a[0] <= a[1] <= ... <= a[len(nums)-1]), r = max { j - i + 1 : 0 <= i <= j < len(nums) and a[j] - a[i] <= 2*k }.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
  theorem spec_12 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        ∃ a : List ℤ, a.Perm (nums.val.map (fun x => x.val)) ∧ a.Pairwise (· ≤ ·) ∧
          r.val = (maxWindow a (2 * k.val) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          ∃ a : List ℤ, a.Perm (nums.val.map (fun x => x.val)) ∧ a.Pairwise (· ≤ ·) ∧
            r.val = (maxWindow a (2 * k.val) : ℤ)) := by
    sorry

  /-- The function returns a result r and for every integer v, |{i : 0 <= i < len(nums) and nums[i] - k <= v <= nums[i] + k}| <= r.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
  theorem spec_13 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
        ∀ v : ℤ, (countNear nums k.val v : ℤ) ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ r : I64, Aegis.MaximumBeauty.maximum_beauty nums k = ok r ∧
          ∀ v : ℤ, (countNear nums k.val v : ℤ) ≤ r.val) := by
    sorry

  /-- The calls maximum_beauty(nums, k1) and maximum_beauty(nums, k2) both return results r1 and r2, and r1 <= r2.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k1 <= 100000; 0 <= k2 <= 100000; k1 <= k2. -/
  theorem spec_14 (nums : Slice I64) (k1 k2 : I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbounds : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hk1_nonneg : 0 ≤ k1.val) (hk1_le : k1.val ≤ 100000)
      (hk2_nonneg : 0 ≤ k2.val) (hk2_le : k2.val ≤ 100000)
      (hk12 : k1.val ≤ k2.val) :
      ∃ r1 r2 : I64, Aegis.MaximumBeauty.maximum_beauty nums k1 = ok r1 ∧
        Aegis.MaximumBeauty.maximum_beauty nums k2 = ok r2 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64) (k1 k2 : I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbounds : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hk1_nonneg : 0 ≤ k1.val) (hk1_le : k1.val ≤ 100000)
        (hk2_nonneg : 0 ≤ k2.val) (hk2_le : k2.val ≤ 100000)
        (hk12 : k1.val ≤ k2.val), ∃ r1 r2 : I64, Aegis.MaximumBeauty.maximum_beauty nums k1 = ok r1 ∧
          Aegis.MaximumBeauty.maximum_beauty nums k2 = ok r2 ∧ r1.val ≤ r2.val) := by
    sorry

  end AegisSpec.MaximumBeauty
