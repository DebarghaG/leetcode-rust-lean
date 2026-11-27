import Aegis.MaxValue.Code.Funs

/-!
# Specifications of `Aegis.MaxValue.max_value`

LeetCode problem `find-the-maximum-sequence-value-of-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxValue

  def elemAt (nums : Slice I64) (i : Nat) : I64 := nums.val.getD i 0#i64

  def orAll : List I64 → I64
    | [] => 0#i64
    | x :: xs => x ||| orAll xs

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldr max x

  def idxCombos : Nat → Nat → List (List Nat)
    | 0, _ => [[]]
    | m + 1, n => (List.range n).flatMap (fun i => (idxCombos m i).map (fun is => is ++ [i]))

  def subseqValue (nums : Slice I64) (k : Nat) (is : List Nat) : I64 :=
    orAll ((is.take k).map (elemAt nums)) ^^^ orAll ((is.drop k).map (elemAt nums))

  def IsIndexSeq (nums : Slice I64) (m : Nat) (is : List Nat) : Prop :=
    is.length = m ∧ is.Pairwise (· < ·) ∧ ∀ i ∈ is, i < nums.val.length

  def maxSubseqValue (nums : Slice I64) (k : Nat) : Int :=
    listMax ((idxCombos (2 * k) nums.val.length).map (fun is => (subseqValue nums k is).val))

  def pairIdx (n : Nat) : List (Nat × Nat) :=
    (List.range n).flatMap (fun i =>
      ((List.range n).filter (fun j => decide (i < j))).map (fun j => (i, j)))

  def pairXor (nums : Slice I64) (p : Nat × Nat) : Int :=
    (elemAt nums p.1 ^^^ elemAt nums p.2).val

  def maxPairXor (nums : Slice I64) : Int :=
    listMax ((pairIdx nums.val.length).map (pairXor nums))

  def bitAt (x : Int) (b : Nat) : Int := (x / 2 ^ b) % 2

  /-- Whenever the function returns a result r, r equals the maximum over all subsequences of nums of size 2k of the value (nums[i0] OR nums[i1] OR ... OR nums[i_{k-1}]) XOR (nums[i_k] OR nums[i_{k+1}] OR ... OR nums[i_{2k-1}]), where the subsequence is given by indices i0 < i1 < ... < i_{2k-1} with 0 <= i_j < len(nums).
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. -/
  theorem spec_1 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
        r.val = maxSubseqValue nums k.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
          r.val = maxSubseqValue nums k.val.toNat) := by
    sorry

  /-- The function returns a result r (it does not fail) for all inputs satisfying the preconditions.
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. -/
  theorem spec_2 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2) :
      ∃ r : I64, Aegis.MaxValue.max_value nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2), ∃ r : I64, Aegis.MaxValue.max_value nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every bit position b (0 <= b < 64), if the b-th bit of r is 1, then there exists an index i with 0 <= i < len(nums) such that the b-th bit of nums[i] is 1. Equivalently, r bitwise AND (bitwise NOT of the bitwise OR of all elements of nums) equals 0.
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. -/
  theorem spec_3 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
        (∀ b : Nat, b < 64 → bitAt r.val b = 1 →
          ∃ i, i < nums.val.length ∧ bitAt (elemAt nums i).val b = 1) ∧
        (r &&& ~~~ (orAll nums.val)) = 0#i64 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
          (∀ b : Nat, b < 64 → bitAt r.val b = 1 →
            ∃ i, i < nums.val.length ∧ bitAt (elemAt nums i).val b = 1) ∧
          (r &&& ~~~ (orAll nums.val)) = 0#i64) := by
    sorry

  /-- Whenever the function returns a result r, for every subsequence of nums of size 2k with indices i0 < i1 < ... < i_{2k-1}, the value (nums[i0] OR ... OR nums[i_{k-1}]) XOR (nums[i_k] OR ... OR nums[i_{2k-1}]) is less than or equal to r.
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. -/
  theorem spec_4 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
        ∀ is : List Nat, IsIndexSeq nums (2 * k.val.toNat) is →
          (subseqValue nums k.val.toNat is).val ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
          ∀ is : List Nat, IsIndexSeq nums (2 * k.val.toNat) is →
            (subseqValue nums k.val.toNat is).val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a subsequence of nums of size 2k with indices i0 < i1 < ... < i_{2k-1} such that (nums[i0] OR ... OR nums[i_{k-1}]) XOR (nums[i_k] OR ... OR nums[i_{2k-1}]) = r.
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. -/
  theorem spec_5 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
        ∃ is : List Nat, IsIndexSeq nums (2 * k.val.toNat) is ∧
          (subseqValue nums k.val.toNat is).val = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
          ∃ is : List Nat, IsIndexSeq nums (2 * k.val.toNat) is ∧
            (subseqValue nums k.val.toNat is).val = r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = max_{0 <= i < j < len(nums)} (nums[i] XOR nums[j]).
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2 and k = 1. -/
  theorem spec_6 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
      (hk1 : k.val = 1) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
        r.val = maxPairXor nums := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
        (hk1 : k.val = 1), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
          r.val = maxPairXor nums) := by
    sorry

  /-- Whenever the function returns a result r, r = (nums[0] OR nums[1] OR ... OR nums[k-1]) XOR (nums[k] OR nums[k+1] OR ... OR nums[2k-1]).
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2 and len(nums) = 2*k. -/
  theorem spec_7 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
      (hlenk : nums.val.length = 2 * k.val.toNat) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
        r.val = (orAll ((List.range k.val.toNat).map (elemAt nums)) ^^^
          orAll ((List.range k.val.toNat).map (fun i => elemAt nums (k.val.toNat + i)))).val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
        (hlenk : nums.val.length = 2 * k.val.toNat), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
          r.val = (orAll ((List.range k.val.toNat).map (elemAt nums)) ^^^
            orAll ((List.range k.val.toNat).map (fun i => elemAt nums (k.val.toNat + i)))).val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. There exists an integer c such that for every i with 0 <= i < len(nums), nums[i] = c. -/
  theorem spec_8 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
      (hconst : ∃ c : Int, ∀ i, i < nums.val.length → (elemAt nums i).val = c) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r → r.val = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
        (hconst : ∃ c : Int, ∀ i, i < nums.val.length → (elemAt nums i).val = c), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r for nums, the function max_value on the reversed slice rev (where rev has length len(nums) and rev[i] = nums[len(nums)-1-i] for all 0 <= i < len(nums)) with the same k returns the same result r.
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. -/
  theorem spec_9 (nums rev : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
      (hrev : rev.val = nums.val.reverse) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
        Aegis.MaxValue.max_value rev k = ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums rev : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
        (hrev : rev.val = nums.val.reverse), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
          Aegis.MaxValue.max_value rev k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= (nums[0] OR nums[1] OR ... OR nums[k-1]) XOR (nums[len(nums)-k] OR nums[len(nums)-k+1] OR ... OR nums[len(nums)-1]).
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. -/
  theorem spec_10 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
        (orAll ((List.range k.val.toNat).map (elemAt nums)) ^^^
          orAll ((List.range k.val.toNat).map
            (fun i => elemAt nums (nums.val.length - k.val.toNat + i)))).val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
          (orAll ((List.range k.val.toNat).map (elemAt nums)) ^^^
            orAll ((List.range k.val.toNat).map
              (fun i => elemAt nums (nums.val.length - k.val.toNat + i)))).val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= (nums[0] OR nums[1] OR ... OR nums[k-1]) XOR (nums[k] OR nums[k+1] OR ... OR nums[2k-1]).
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. -/
  theorem spec_11 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
        (orAll ((List.range k.val.toNat).map (elemAt nums)) ^^^
          orAll ((List.range k.val.toNat).map (fun i => elemAt nums (k.val.toNat + i)))).val
          ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
          (orAll ((List.range k.val.toNat).map (elemAt nums)) ^^^
            orAll ((List.range k.val.toNat).map (fun i => elemAt nums (k.val.toNat + i)))).val
            ≤ r.val) := by
    sorry

  /-- Let nums' be the slice of length len(nums)+1 with nums'[i] = nums[i] for 0 <= i < len(nums) and nums'[len(nums)] = x. Whenever max_value(nums, k) returns a result r, max_value(nums', k) returns a result r' and r' >= r.
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) < 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. x is an integer with 1 <= x < 27. -/
  theorem spec_12 (nums nums' : Slice I64) (k x : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length < 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
      (hx : 1 ≤ x.val ∧ x.val < 27)
      (hnums' : nums'.val = nums.val ++ [x]) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
        ∃ r' : I64, Aegis.MaxValue.max_value nums' k = ok r' ∧ r.val ≤ r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums' : Slice I64) (k x : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length < 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
        (hx : 1 ≤ x.val ∧ x.val < 27)
        (hnums' : nums'.val = nums.val ++ [x]), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r →
          ∃ r' : I64, Aegis.MaxValue.max_value nums' k = ok r' ∧ r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function returns a result r, r mod 2^b = 0.
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. Let b >= 0 be an integer such that for every i with 0 <= i < len(nums), nums[i] mod 2^b = 0. -/
  theorem spec_13 (nums : Slice I64) (k : I64) (b : Nat)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
      (hb : ∀ i, i < nums.val.length → (elemAt nums i).val % 2 ^ b = 0) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r → r.val % 2 ^ b = 0 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64) (k : I64) (b : Nat)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
        (hb : ∀ i, i < nums.val.length → (elemAt nums i).val % 2 ^ b = 0), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r → r.val % 2 ^ b = 0) := by
    sorry

  /-- Whenever the function returns a result r, r is even (i.e., r mod 2 = 0).
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. For every i with 0 <= i < len(nums), nums[i] is odd (i.e., nums[i] mod 2 = 1). -/
  theorem spec_14 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
      (hodd : ∀ i, i < nums.val.length → (elemAt nums i).val % 2 = 1) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r → r.val % 2 = 0 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
        (hodd : ∀ i, i < nums.val.length → (elemAt nums i).val % 2 = 1), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r → r.val % 2 = 0) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 32.
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. -/
  theorem spec_15 (nums : Slice I64) (k : I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r → 0 ≤ r.val ∧ r.val < 32 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r → 0 ≤ r.val ∧ r.val < 32) := by
    sorry

  /-- Whenever the function returns a result r, the b-th bit of r is 0.
    Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 400, and for every i with 0 <= i < len(nums), 1 <= nums[i] < 27. k is an integer with 1 <= k <= len(nums)/2. Let b satisfy 0 <= b < 64, and suppose that for every i with 0 <= i < len(nums), the b-th bit of nums[i] is 1. -/
  theorem spec_16 (nums : Slice I64) (k : I64) (b : Nat)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
      (hval : ∀ i, i < nums.val.length →
        1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
      (hb64 : b < 64)
      (hbit : ∀ i, i < nums.val.length → bitAt (elemAt nums i).val b = 1) :
      ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r → bitAt r.val b = 0 := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (nums : Slice I64) (k : I64) (b : Nat)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 400)
        (hval : ∀ i, i < nums.val.length →
          1 ≤ (elemAt nums i).val ∧ (elemAt nums i).val < 27)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ (nums.val.length : Int) / 2)
        (hb64 : b < 64)
        (hbit : ∀ i, i < nums.val.length → bitAt (elemAt nums i).val b = 1), ∀ r : I64, Aegis.MaxValue.max_value nums k = ok r → bitAt r.val b = 0) := by
    sorry

  end AegisSpec.MaxValue
