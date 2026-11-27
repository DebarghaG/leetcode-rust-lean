import Aegis.XorBeauty.Code.Funs

/-!
# Specifications of `Aegis.XorBeauty.xor_beauty`

LeetCode problem `find-xor-beauty-of-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.XorBeauty

def bitAt (x : Int) (b : Nat) : Bool := x.testBit b

def bitCount (l : List I64) (b : Nat) : Nat := (l.filter (fun x => bitAt x.val b)).length

def occursOdd (l : List I64) (v : Int) : Prop :=
  (l.filter (fun x => decide (x.val = v))).length % 2 = 1

noncomputable def oddValueBitSet (l : List I64) (b : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc 1 1000000000).filter (fun v => occursOdd l (v : Int) ∧ bitAt (v : Int) b = true)

noncomputable def oddValueBitCount (l : List I64) (b : Nat) : Nat := (oddValueBitSet l b).card

def xorInt (a b : Int) : Int := (BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 b).toInt

/-- For every slice nums satisfying the preconditions, whenever xor_beauty(nums) returns a result r, r is the bitwise XOR of all elements of nums: for every bit position b with 0 <= b < 63, the b-th bit of r is 1 if and only if the number of indices i with 0 <= i < len(nums) and with the b-th bit of nums[i] equal to 1 is odd. Equivalently, r = nums[0] XOR nums[1] XOR ... XOR nums[len(nums)-1], where XOR denotes bitwise exclusive or.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.XorBeauty.xor_beauty nums = ok r) :
    ∀ b : Nat, b < 63 → (bitAt r.val b = true ↔ Odd (bitCount nums.val b)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.XorBeauty.xor_beauty nums = ok r), ∀ b : Nat, b < 63 → (bitAt r.val b = true ↔ Odd (bitCount nums.val b))) := by
  sorry

/-- For every slice nums satisfying the preconditions, xor_beauty(nums) returns a result r; it does not fail, panic, go out of bounds, or overflow.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∃ r : I64, Aegis.XorBeauty.xor_beauty nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r : I64, Aegis.XorBeauty.xor_beauty nums = ok r) := by
  sorry

/-- For every slice nums satisfying the preconditions, whenever xor_beauty(nums) returns a result r, 0 <= r < 2^30 = 1073741824.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.XorBeauty.xor_beauty nums = ok r) :
    0 ≤ r.val ∧ r.val < 1073741824 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.XorBeauty.xor_beauty nums = ok r), 0 ≤ r.val ∧ r.val < 1073741824) := by
  sorry

/-- For every slice nums satisfying the preconditions, whenever xor_beauty(nums) returns a result r, r = 0 if and only if for every bit position b with 0 <= b < 63, the number of indices i with 0 <= i < len(nums) whose b-th bit of nums[i] is 1 is even.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.XorBeauty.xor_beauty nums = ok r) :
    (r.val = 0 ↔ ∀ b : Nat, b < 63 → Even (bitCount nums.val b)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.XorBeauty.xor_beauty nums = ok r), (r.val = 0 ↔ ∀ b : Nat, b < 63 → Even (bitCount nums.val b))) := by
  sorry

/-- Whenever xor_beauty(nums) returns r and xor_beauty(nums2) returns r2, we have r = r2.
  Preconditions: nums and nums2 are slices of 64-bit integers, each with 1 <= length <= 100000 and all elements between 1 and 1000000000, and nums2 is a permutation of nums (same length and same multiset of values). -/
theorem spec_5 (nums nums2 : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hlen2 : 1 ≤ nums2.val.length) (hlen2_max : nums2.val.length ≤ 100000)
    (hbound2 : ∀ x ∈ nums2.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hperm : nums2.val.Perm nums.val)
    (r r2 : I64) (hr : Aegis.XorBeauty.xor_beauty nums = ok r)
    (hr2 : Aegis.XorBeauty.xor_beauty nums2 = ok r2) :
    r = r2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums nums2 : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hlen2 : 1 ≤ nums2.val.length) (hlen2_max : nums2.val.length ≤ 100000)
    (hbound2 : ∀ x ∈ nums2.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hperm : nums2.val.Perm nums.val)
    (r r2 : I64) (hr : Aegis.XorBeauty.xor_beauty nums = ok r)
    (hr2 : Aegis.XorBeauty.xor_beauty nums2 = ok r2), r = r2) := by
  sorry

/-- Whenever xor_beauty(xs) returns rx, xor_beauty(ys) returns ry, and xor_beauty(nums) returns r, we have r = rx XOR ry, where XOR is bitwise exclusive or (for each bit position the result bit is 1 if and only if exactly one of the two operand bits is 1).
  Preconditions: xs and ys are nonempty slices of 64-bit integers, each with length between 1 and 100000 and all elements between 1 and 1000000000, and len(xs)+len(ys) <= 100000. Let nums be the concatenation xs ++ ys. -/
theorem spec_6 (xs ys nums : Slice I64)
    (hxs : 1 ≤ xs.val.length) (hxs_max : xs.val.length ≤ 100000)
    (hxs_bound : ∀ x ∈ xs.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hys : 1 ≤ ys.val.length) (hys_max : ys.val.length ≤ 100000)
    (hys_bound : ∀ x ∈ ys.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hsum : xs.val.length + ys.val.length ≤ 100000)
    (hnums : nums.val = xs.val ++ ys.val)
    (rx ry r : I64) (hrx : Aegis.XorBeauty.xor_beauty xs = ok rx)
    (hry : Aegis.XorBeauty.xor_beauty ys = ok ry)
    (hr : Aegis.XorBeauty.xor_beauty nums = ok r) :
    r.val = xorInt rx.val ry.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (xs ys nums : Slice I64)
    (hxs : 1 ≤ xs.val.length) (hxs_max : xs.val.length ≤ 100000)
    (hxs_bound : ∀ x ∈ xs.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hys : 1 ≤ ys.val.length) (hys_max : ys.val.length ≤ 100000)
    (hys_bound : ∀ x ∈ ys.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hsum : xs.val.length + ys.val.length ≤ 100000)
    (hnums : nums.val = xs.val ++ ys.val)
    (rx ry r : I64) (hrx : Aegis.XorBeauty.xor_beauty xs = ok rx)
    (hry : Aegis.XorBeauty.xor_beauty ys = ok ry)
    (hr : Aegis.XorBeauty.xor_beauty nums = ok r), r.val = xorInt rx.val ry.val) := by
  sorry

/-- For every slice nums satisfying the preconditions, whenever xor_beauty(nums) returns a result r, r is the bitwise XOR of exactly those distinct values v that occur an odd number of times among the entries of nums. More precisely, for every bit position b with 0 <= b < 63, the b-th bit of r is 1 if and only if the number of distinct values v with 1 <= v <= 1000000000 such that v occurs an odd number of times in nums and the b-th bit of v is 1 is odd. If no value occurs an odd number of times, then r = 0.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.XorBeauty.xor_beauty nums = ok r) :
    (∀ b : Nat, b < 63 → (bitAt r.val b = true ↔ Odd (oddValueBitCount nums.val b)))
      ∧ ((∀ v : Int, 1 ≤ v → v ≤ 1000000000 → ¬ occursOdd nums.val v) → r.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
    (hbound : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.XorBeauty.xor_beauty nums = ok r), (∀ b : Nat, b < 63 → (bitAt r.val b = true ↔ Odd (oddValueBitCount nums.val b)))
      ∧ ((∀ v : Int, 1 ≤ v → v ≤ 1000000000 → ¬ occursOdd nums.val v) → r.val = 0)) := by
  sorry

end AegisSpec.XorBeauty
