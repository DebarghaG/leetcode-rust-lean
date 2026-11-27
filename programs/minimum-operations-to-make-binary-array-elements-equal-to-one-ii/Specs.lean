import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-binary-array-elements-equal-to-one-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinOperations

  def IsBit (x : Int) : Prop := x = 0 ∨ x = 1

  def valAt (nums : Slice I64) (i : Nat) (h : i < nums.val.length) : Int :=
    (nums.val.get ⟨i, h⟩).val

  def valFirst (nums : Slice I64) (h : 0 < nums.val.length) : Int :=
    valAt nums 0 h

  def valLast (nums : Slice I64) (h : 0 < nums.val.length) : Int :=
    valAt nums (nums.val.length - 1) (by omega)

  def AllBits (nums : Slice I64) : Prop :=
    ∀ i (h : i < nums.val.length), IsBit (valAt nums i h)

  def numChanges (nums : Slice I64) : Nat :=
    (nums.val.zip nums.val.tail).countP (fun p => decide (p.1.val ≠ p.2.val))

  def vals (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

  def flipFrom (i : Nat) (l : List Int) : List Int :=
    l.mapIdx (fun j x => if i ≤ j then 1 - x else x)

  def applyFlips (l : List Int) : List Nat → List Int
    | [] => l
    | i :: is => applyFlips (flipFrom i l) is

  /-- Whenever the function returns a result r, r equals (if nums[0] = 0 then 1 else 0) plus the number of indices i with 1 <= i < len(nums) such that nums[i] != nums[i-1]. For len(nums) = 1 the number of such i is 0.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_1 (nums : Slice I64)
      (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hbits : AllBits nums) :
      ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
        r.val = (if valFirst nums (by omega) = 0 then 1 else 0) + (numChanges nums : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hbits : AllBits nums), ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
          r.val = (if valFirst nums (by omega) = 0 then 1 else 0) + (numChanges nums : Int)) := by
    sorry

  /-- The function returns Result.ok r for some r; it does not fail.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_2 (nums : Slice I64)
      (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hbits : AllBits nums) :
      ∃ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hbits : AllBits nums), ∃ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 1 - nums[0].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_3 (nums : Slice I64)
      (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hbits : AllBits nums) :
      ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
        1 - valFirst nums (by omega) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hbits : AllBits nums), ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
          1 - valFirst nums (by omega) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(nums) - nums[0].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_4 (nums : Slice I64)
      (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hbits : AllBits nums) :
      ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
        r.val ≤ (nums.val.length : Int) - valFirst nums (by omega) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hbits : AllBits nums), ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
          r.val ≤ (nums.val.length : Int) - valFirst nums (by omega)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(nums), nums[i] = 1.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_5 (nums : Slice I64)
      (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hbits : AllBits nums) :
      ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
        (r.val = 0 ↔ ∀ i (h : i < nums.val.length), valAt nums i h = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hbits : AllBits nums), ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
          (r.val = 0 ↔ ∀ i (h : i < nums.val.length), valAt nums i h = 1)) := by
    sorry

  /-- Whenever the function returns a result r, r mod 2 = 1 - nums[len(nums)-1].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_6 (nums : Slice I64)
      (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hbits : AllBits nums) :
      ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
        r.val % 2 = 1 - valLast nums (by omega) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hbits : AllBits nums), ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
          r.val % 2 = 1 - valLast nums (by omega)) := by
    sorry

  /-- Let nums2 be the array of length len(nums)+1 with nums2[i] = nums[i] for 0 <= i < len(nums) and nums2[len(nums)] = b. Whenever min_operations(nums) returns Result.ok r and min_operations(nums2) returns Result.ok r2, r2 = r + 1 if b != nums[len(nums)-1], and r2 = r if b = nums[len(nums)-1].
    Preconditions: 1 <= len(nums) < 100000; for every i with 0 <= i < len(nums), nums[i] is either 0 or 1; b is either 0 or 1. -/
  theorem spec_7 (nums nums2 : Slice I64) (b : I64)
      (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length < 100000)
      (hbits : AllBits nums) (hb : IsBit b.val)
      (hnums2 : nums2.val = nums.val ++ [b]) :
      ∀ r r2 : I64,
        Aegis.MinOperations.min_operations nums = Result.ok r →
        Aegis.MinOperations.min_operations nums2 = Result.ok r2 →
        ((b.val ≠ valLast nums (by omega) → r2.val = r.val + 1) ∧
          (b.val = valLast nums (by omega) → r2.val = r.val)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums2 : Slice I64) (b : I64)
        (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length < 100000)
        (hbits : AllBits nums) (hb : IsBit b.val)
        (hnums2 : nums2.val = nums.val ++ [b]), ∀ r r2 : I64,
          Aegis.MinOperations.min_operations nums = Result.ok r →
          Aegis.MinOperations.min_operations nums2 = Result.ok r2 →
          ((b.val ≠ valLast nums (by omega) → r2.val = r.val + 1) ∧
            (b.val = valLast nums (by omega) → r2.val = r.val))) := by
    sorry

  /-- Let nums2 be the array of length len(nums)+1 with nums2[0] = 1 and nums2[i+1] = nums[i] for every i with 0 <= i < len(nums). Whenever min_operations(nums) returns Result.ok r and min_operations(nums2) returns Result.ok r2, r2 = r.
    Preconditions: 1 <= len(nums) < 100000; for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_8 (nums nums2 : Slice I64)
      (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length < 100000)
      (hbits : AllBits nums)
      (hnums2 : nums2.val = [1#i64] ++ nums.val) :
      ∀ r r2 : I64,
        Aegis.MinOperations.min_operations nums = Result.ok r →
        Aegis.MinOperations.min_operations nums2 = Result.ok r2 →
        r2.val = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums2 : Slice I64)
        (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length < 100000)
        (hbits : AllBits nums)
        (hnums2 : nums2.val = [1#i64] ++ nums.val), ∀ r r2 : I64,
          Aegis.MinOperations.min_operations nums = Result.ok r →
          Aegis.MinOperations.min_operations nums2 = Result.ok r2 →
          r2.val = r.val) := by
    sorry

  /-- Whenever the function returns a result r, r is nonnegative and there exists a finite sequence of exactly r indices i_1, ..., i_r, each satisfying 0 <= i_k < len(nums), such that starting from nums and successively flipping, for k = 1, ..., r, all elements with index at least i_k, the resulting array has every element equal to 1. If r = 0 this is the empty sequence.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_9 (nums : Slice I64)
      (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hbits : AllBits nums) :
      ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
        0 ≤ r.val ∧ ∃ is : List Nat,
          (is.length : Int) = r.val ∧
            (∀ i ∈ is, i < nums.val.length) ∧
              applyFlips (vals nums) is = List.replicate nums.val.length 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hbits : AllBits nums), ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
          0 ≤ r.val ∧ ∃ is : List Nat,
            (is.length : Int) = r.val ∧
              (∀ i ∈ is, i < nums.val.length) ∧
                applyFlips (vals nums) is = List.replicate nums.val.length 1) := by
    sorry

  /-- Let nums2 be the array of the same length as nums with nums2[j] = 1 - nums[j] for every j with i <= j < len(nums), and nums2[j] = nums[j] for every j with 0 <= j < i. Whenever min_operations(nums) returns Result.ok r and min_operations(nums2) returns Result.ok r2, either r2 = r + 1 or r2 = r - 1.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is either 0 or 1; 0 <= i < len(nums). -/
  theorem spec_10 (nums nums2 : Slice I64) (i : Nat)
      (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hbits : AllBits nums) (hi : i < nums.val.length)
      (hnums2 : nums2.val.length = nums.val.length ∧ vals nums2 = flipFrom i (vals nums)) :
      ∀ r r2 : I64,
        Aegis.MinOperations.min_operations nums = Result.ok r →
        Aegis.MinOperations.min_operations nums2 = Result.ok r2 →
        (r2.val = r.val + 1 ∨ r2.val = r.val - 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums2 : Slice I64) (i : Nat)
        (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hbits : AllBits nums) (hi : i < nums.val.length)
        (hnums2 : nums2.val.length = nums.val.length ∧ vals nums2 = flipFrom i (vals nums)), ∀ r r2 : I64,
          Aegis.MinOperations.min_operations nums = Result.ok r →
          Aegis.MinOperations.min_operations nums2 = Result.ok r2 →
          (r2.val = r.val + 1 ∨ r2.val = r.val - 1)) := by
    sorry

  /-- Whenever the function returns Result.ok r, for every finite sequence of indices i_1, ..., i_k with k < r and each 0 <= i_j < len(nums), starting from nums and successively flipping, for j = 1, ..., k, all elements with index at least i_j, the resulting array is not all ones.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_11 (nums : Slice I64)
      (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hbits : AllBits nums) :
      ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
        ∀ is : List Nat, (is.length : Int) < r.val →
          (∀ i ∈ is, i < nums.val.length) →
          applyFlips (vals nums) is ≠ List.replicate nums.val.length 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hbits : AllBits nums), ∀ r : I64, Aegis.MinOperations.min_operations nums = Result.ok r →
          ∀ is : List Nat, (is.length : Int) < r.val →
            (∀ i ∈ is, i < nums.val.length) →
            applyFlips (vals nums) is ≠ List.replicate nums.val.length 1) := by
    sorry

  end AegisSpec.MinOperations
