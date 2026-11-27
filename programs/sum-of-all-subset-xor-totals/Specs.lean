import Aegis.SubsetXorSum.Code.Funs

/-!
# Specifications of `Aegis.SubsetXorSum.subset_xor_sum`

LeetCode problem `sum-of-all-subset-xor-totals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SubsetXorSum

  open Aegis.SubsetXorSum

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def i64Or (a b : ℤ) : ℤ := (BitVec.ofInt 64 a ||| BitVec.ofInt 64 b).toInt

  def i64Xor (a b : ℤ) : ℤ := (BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 b).toInt

  def orAll (l : List ℤ) : ℤ := l.foldr i64Or 0

  def xorAll (l : List ℤ) : ℤ := l.foldr i64Xor 0

  def xorOfMask (l : List ℤ) (m : ℕ) : ℤ :=
    ((List.range l.length).filter (fun i => m.testBit i)).foldr
      (fun i acc => i64Xor (l.getD i 0) acc) 0

  def subsetXorSum (l : List ℤ) : ℤ :=
    (Finset.range (2 ^ l.length)).sum (fun m => xorOfMask l m)

  /-- Whenever subset_xor_sum nums returns a result r, r equals the sum, over all subsets S of the index set {0,1,...,len(nums)-1}, of the bitwise XOR of nums[i] for i in S. The XOR of the empty subset is 0. Each subset of indices is counted exactly once, so equal values at different indices are treated as distinct choices.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r → r.val = subsetXorSum (vals nums) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20), ∀ r : Std.I64, subset_xor_sum nums = ok r → r.val = subsetXorSum (vals nums)) := by
    sorry

  /-- The function subset_xor_sum returns a result (does not fail) for every input satisfying the preconditions.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20) :
      ∃ r : Std.I64, subset_xor_sum nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20), ∃ r : Std.I64, subset_xor_sum nums = ok r) := by
    sorry

  /-- Whenever subset_xor_sum nums returns a result r, r >= 0.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20), ∀ r : Std.I64, subset_xor_sum nums = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever subset_xor_sum nums returns a result r, r <= 31 * 2^(len(nums)-1).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r →
        r.val ≤ 31 * (2 : ℤ) ^ ((vals nums).length - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20), ∀ r : Std.I64, subset_xor_sum nums = ok r →
          r.val ≤ 31 * (2 : ℤ) ^ ((vals nums).length - 1)) := by
    sorry

  /-- Whenever subset_xor_sum nums returns a result r, r >= nums[0] + nums[1] + ... + nums[len(nums)-1].
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r → (vals nums).sum ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20), ∀ r : Std.I64, subset_xor_sum nums = ok r → (vals nums).sum ≤ r.val) := by
    sorry

  /-- Whenever subset_xor_sum nums returns a result r, there exists an integer q such that r = q * 2^(len(nums)-1). Equivalently, r is divisible by 2^(len(nums)-1).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r →
        ∃ q : ℤ, r.val = q * (2 : ℤ) ^ ((vals nums).length - 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20), ∀ r : Std.I64, subset_xor_sum nums = ok r →
          ∃ q : ℤ, r.val = q * (2 : ℤ) ^ ((vals nums).length - 1)) := by
    sorry

  /-- Whenever subset_xor_sum nums returns a result r, r >= 2^(len(nums)-1).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r →
        (2 : ℤ) ^ ((vals nums).length - 1) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20), ∀ r : Std.I64, subset_xor_sum nums = ok r →
          (2 : ℤ) ^ ((vals nums).length - 1) ≤ r.val) := by
    sorry

  /-- Let OR(nums) = nums[0] | nums[1] | ... | nums[len(nums)-1] (bitwise OR). Whenever subset_xor_sum nums returns a result r, r = 2^(len(nums)-1) * OR(nums).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r →
        r.val = (2 : ℤ) ^ ((vals nums).length - 1) * orAll (vals nums) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20), ∀ r : Std.I64, subset_xor_sum nums = ok r →
          r.val = (2 : ℤ) ^ ((vals nums).length - 1) * orAll (vals nums)) := by
    sorry

  /-- Whenever subset_xor_sum nums returns a result r and subset_xor_sum nums' returns a result r', we have r = r'.
    Preconditions: nums and nums' are slices of 64-bit integers, each with 1 <= length <= 12 and all entries in [1,20]. They have len(nums') = len(nums) and the same bitwise OR: nums[0] | ... | nums[len(nums)-1] = nums'[0] | ... | nums'[len(nums')-1]. -/
  theorem spec_9 (nums nums' : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20)
      (hlen' : 1 ≤ (vals nums').length ∧ (vals nums').length ≤ 12)
      (hval' : ∀ (i : ℕ) (hi : i < (vals nums').length),
        1 ≤ (vals nums').get ⟨i, hi⟩ ∧ (vals nums').get ⟨i, hi⟩ ≤ 20)
      (hlen_eq : (vals nums').length = (vals nums).length)
      (hor : orAll (vals nums) = orAll (vals nums')) :
      ∀ r r' : Std.I64, subset_xor_sum nums = ok r → subset_xor_sum nums' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20)
        (hlen' : 1 ≤ (vals nums').length ∧ (vals nums').length ≤ 12)
        (hval' : ∀ (i : ℕ) (hi : i < (vals nums').length),
          1 ≤ (vals nums').get ⟨i, hi⟩ ∧ (vals nums').get ⟨i, hi⟩ ≤ 20)
        (hlen_eq : (vals nums').length = (vals nums).length)
        (hor : orAll (vals nums) = orAll (vals nums')), ∀ r r' : Std.I64, subset_xor_sum nums = ok r → subset_xor_sum nums' = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Whenever subset_xor_sum nums returns a result r and subset_xor_sum nums' returns a result r', we have r' = 2 * r.
    Preconditions: nums is a slice with 1 <= len(nums) <= 11 and all entries in [1,20]. Let OR(nums) = nums[0] | ... | nums[len(nums)-1]. Let x be an integer with 1 <= x <= 20 and x | OR(nums) = OR(nums). Let nums' be the slice obtained by appending x to nums: len(nums') = len(nums)+1, nums'[i] = nums[i] for 0 <= i < len(nums), and nums'[len(nums)] = x. -/
  theorem spec_10 (nums nums' : Slice Std.I64) (x : ℤ)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 11)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20)
      (hx_lo : 1 ≤ x) (hx_hi : x ≤ 20)
      (hx_or : i64Or x (orAll (vals nums)) = orAll (vals nums))
      (happend : vals nums' = vals nums ++ [x]) :
      ∀ r r' : Std.I64, subset_xor_sum nums = ok r → subset_xor_sum nums' = ok r' →
        r'.val = 2 * r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (x : ℤ)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 11)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20)
        (hx_lo : 1 ≤ x) (hx_hi : x ≤ 20)
        (hx_or : i64Or x (orAll (vals nums)) = orAll (vals nums))
        (happend : vals nums' = vals nums ++ [x]), ∀ r r' : Std.I64, subset_xor_sum nums = ok r → subset_xor_sum nums' = ok r' →
          r'.val = 2 * r.val) := by
    sorry

  /-- Whenever subset_xor_sum nums returns a result r, r = 2^(len(nums)-1) * x.
    Preconditions: nums is a slice with 1 <= len(nums) <= 12 and all entries in [1,20]. There is an integer x such that nums[i] = x for every i with 0 <= i < len(nums). -/
  theorem spec_11 (nums : Slice Std.I64) (x : ℤ)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20)
      (hconst : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums).get ⟨i, hi⟩ = x) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r →
        r.val = (2 : ℤ) ^ ((vals nums).length - 1) * x := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : ℤ)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20)
        (hconst : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums).get ⟨i, hi⟩ = x), ∀ r : Std.I64, subset_xor_sum nums = ok r →
          r.val = (2 : ℤ) ^ ((vals nums).length - 1) * x) := by
    sorry

  /-- Let xorAll = nums[0] XOR nums[1] XOR ... XOR nums[len(nums)-1] and sumAll = nums[0] + nums[1] + ... + nums[len(nums)-1]. Whenever subset_xor_sum nums returns a result r, r >= sumAll + xorAll.
    Preconditions: nums is a slice with 2 <= len(nums) <= 12 and all entries in [1,20]. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen : 2 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r →
        (vals nums).sum + xorAll (vals nums) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20), ∀ r : Std.I64, subset_xor_sum nums = ok r →
          (vals nums).sum + xorAll (vals nums) ≤ r.val) := by
    sorry

  /-- Whenever subset_xor_sum nums returns a result r, r <= 15 * 2^(len(nums)-1).
    Preconditions: nums is a slice with 1 <= len(nums) <= 12, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 15. -/
  theorem spec_13 (nums : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 15) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r →
        r.val ≤ 15 * (2 : ℤ) ^ ((vals nums).length - 1) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 15), ∀ r : Std.I64, subset_xor_sum nums = ok r →
          r.val ≤ 15 * (2 : ℤ) ^ ((vals nums).length - 1)) := by
    sorry

  /-- Whenever subset_xor_sum nums returns a result r, there exists an integer q such that r = q * 2^(len(nums)). Equivalently, 2^(len(nums)) divides r.
    Preconditions: nums is a slice with 1 <= len(nums) <= 12, and for every i with 0 <= i < len(nums), nums[i] is even and 1 <= nums[i] <= 20. -/
  theorem spec_14 (nums : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20)
      (heven : ∀ (i : ℕ) (hi : i < (vals nums).length), ∃ k : ℤ, (vals nums).get ⟨i, hi⟩ = 2 * k) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r →
        ∃ q : ℤ, r.val = q * (2 : ℤ) ^ ((vals nums).length) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20)
        (heven : ∀ (i : ℕ) (hi : i < (vals nums).length), ∃ k : ℤ, (vals nums).get ⟨i, hi⟩ = 2 * k), ∀ r : Std.I64, subset_xor_sum nums = ok r →
          ∃ q : ℤ, r.val = q * (2 : ℤ) ^ ((vals nums).length)) := by
    sorry

  /-- Whenever subset_xor_sum nums returns a result r, there exists an odd integer q such that r = q * 2^(len(nums)-1). In particular, r is divisible by 2^(len(nums)-1) but not by 2^(len(nums)).
    Preconditions: nums is a slice with 1 <= len(nums) <= 12, and for every i with 0 <= i < len(nums), nums[i] is odd and 1 <= nums[i] <= 20. -/
  theorem spec_15 (nums : Slice Std.I64)
      (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
      (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
        1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20)
      (hodd : ∀ (i : ℕ) (hi : i < (vals nums).length), Odd ((vals nums).get ⟨i, hi⟩)) :
      ∀ r : Std.I64, subset_xor_sum nums = ok r →
        ∃ q : ℤ, Odd q ∧ r.val = q * (2 : ℤ) ^ ((vals nums).length - 1) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 12)
        (hval : ∀ (i : ℕ) (hi : i < (vals nums).length),
          1 ≤ (vals nums).get ⟨i, hi⟩ ∧ (vals nums).get ⟨i, hi⟩ ≤ 20)
        (hodd : ∀ (i : ℕ) (hi : i < (vals nums).length), Odd ((vals nums).get ⟨i, hi⟩)), ∀ r : Std.I64, subset_xor_sum nums = ok r →
          ∃ q : ℤ, Odd q ∧ r.val = q * (2 : ℤ) ^ ((vals nums).length - 1)) := by
    sorry

  end AegisSpec.SubsetXorSum
