import Aegis.MaximumStrongPairXor.Code.Funs

/-!
# Specifications of `Aegis.MaximumStrongPairXor.maximum_strong_pair_xor`

LeetCode problem `maximum-strong-pair-xor-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumStrongPairXor

  namespace AegisSpec.MaximumStrongPairXor

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def valAt (nums : Slice Std.I64) (i : Nat) : Int := (nums.val.getD i 0#i64).val

  def xorAt (nums : Slice Std.I64) (i j : Nat) : Int :=
    (nums.val.getD i 0#i64 ^^^ nums.val.getD j 0#i64).val

  def IsStrongPair (nums : Slice Std.I64) (i j : Nat) : Prop :=
    |valAt nums i - valAt nums j| ≤ min (valAt nums i) (valAt nums j)

  def strongPairXors (nums : Slice Std.I64) : Set Int :=
    { v | ∃ i j : Nat,
        i < nums.val.length ∧ j < nums.val.length ∧ IsStrongPair nums i j ∧
          v = xorAt nums i j }

  def Occurs (nums : Slice Std.I64) (v : Int) : Prop := v ∈ vals nums

  /-- Let S = { nums[i] XOR nums[j] | 0 <= i < len(nums) and 0 <= j < len(nums) and |nums[i] - nums[j]| <= min(nums[i], nums[j]) }. The function returns a result r (it does not fail) and r = max(S). The set S is nonempty because i = j = 0 satisfies the condition (len(nums) >= 1 and |nums[0] - nums[0]| = 0 <= min(nums[0], nums[0])).
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100) :
      ∃ r : Std.I64, maximum_strong_pair_xor nums = ok r ∧ IsGreatest (strongPairXors nums) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100), ∃ r : Std.I64, maximum_strong_pair_xor nums = ok r ∧ IsGreatest (strongPairXors nums) r.val) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, overflow, or panic.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100) :
      ∃ r : Std.I64, maximum_strong_pair_xor nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100), ∃ r : Std.I64, maximum_strong_pair_xor nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100) :
      ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100), ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 127.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100) :
      ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r → r.val ≤ 127 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100), ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r → r.val ≤ 127) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i and j with 0 <= i < len(nums), 0 <= j < len(nums), |nums[i] - nums[j]| <= min(nums[i], nums[j]), and r = nums[i] XOR nums[j].
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100) :
      ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r →
        ∃ i j : Nat, i < nums.val.length ∧ j < nums.val.length ∧ IsStrongPair nums i j ∧
          r.val = xorAt nums i j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100), ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r →
          ∃ i j : Nat, i < nums.val.length ∧ j < nums.val.length ∧ IsStrongPair nums i j ∧
            r.val = xorAt nums i j) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < len(nums), 0 <= j < len(nums), if |nums[i] - nums[j]| <= min(nums[i], nums[j]) then nums[i] XOR nums[j] <= r.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100) :
      ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r →
        ∀ i j : Nat, i < nums.val.length → j < nums.val.length → IsStrongPair nums i j →
          xorAt nums i j ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100), ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r →
          ∀ i j : Nat, i < nums.val.length → j < nums.val.length → IsStrongPair nums i j →
            xorAt nums i j ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i and j with 0 <= i < len(nums), 0 <= j < len(nums), if |nums[i] - nums[j]| <= min(nums[i], nums[j]) then nums[i] = nums[j].
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100) :
      ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r →
        (r.val = 0 ↔
          ∀ i j : Nat, i < nums.val.length → j < nums.val.length → IsStrongPair nums i j →
            valAt nums i = valAt nums j) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100), ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r →
          (r.val = 0 ↔
            ∀ i j : Nat, i < nums.val.length → j < nums.val.length → IsStrongPair nums i j →
              valAt nums i = valAt nums j)) := by
    sorry

  /-- For every slice nums2 of 64-bit integers with len(nums2) >= 1 and 1 <= nums2[i] <= 100 for all 0 <= i < len(nums2), if for every integer v, v occurs in nums2 if and only if v occurs in nums, then if the function returns r on nums, the function returns r on nums2 (and does not fail).
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_8 (nums nums2 : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100)
      (hlen2 : 1 ≤ nums2.val.length)
      (hbound2 : ∀ i : Nat, i < nums2.val.length → 1 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 100)
      (hocc : ∀ v : Int, Occurs nums2 v ↔ Occurs nums v) :
      ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r →
        maximum_strong_pair_xor nums2 = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100)
        (hlen2 : 1 ≤ nums2.val.length)
        (hbound2 : ∀ i : Nat, i < nums2.val.length → 1 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 100)
        (hocc : ∀ v : Int, Occurs nums2 v ↔ Occurs nums v), ∀ r : Std.I64, maximum_strong_pair_xor nums = ok r →
          maximum_strong_pair_xor nums2 = ok r) := by
    sorry

  end AegisSpec.MaximumStrongPairXor
