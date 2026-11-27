import Aegis.FindKOr.Code.Funs

/-!
# Specifications of `Aegis.FindKOr.find_k_or`

LeetCode problem `find-the-k-or-of-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindKOr

open Aegis.FindKOr

def bit (x : ℤ) (b : ℕ) : ℤ := (x / (2 : ℤ) ^ b) % 2

def bitCount (nums : Slice Std.I64) (b : ℕ) : ℕ :=
  nums.val.countP (fun x => bit x.val b == 1)

def hasBit (nums : Slice Std.I64) (b : ℕ) : Prop :=
  ∃ x ∈ nums.val, bit x.val b = 1

def allBit (nums : Slice Std.I64) (b : ℕ) : Prop :=
  ∀ x ∈ nums.val, bit x.val b = 1

def countVal (nums : Slice Std.I64) (v : ℤ) : ℕ :=
  nums.val.countP (fun x => x.val == v)

def ValInU32 (nums : Slice Std.I64) : Prop :=
  ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 2 ^ 32

def PermOf (nums nums2 : Slice Std.I64) : Prop :=
  ∀ v : ℤ, countVal nums v = countVal nums2 v

def anyBitTest (nums : Slice Std.I64) (b : ℕ) : Bool :=
  nums.val.any (fun x => bit x.val b == 1)

def allBitTest (nums : Slice Std.I64) (b : ℕ) : Bool :=
  nums.val.all (fun x => bit x.val b == 1)

def ofBitTest (p : ℕ → Bool) : ℕ :=
  (List.range 32).foldr (fun b acc => if p b then acc + (2 : ℕ) ^ b else acc) 0

def orAll (nums : Slice Std.I64) : ℕ := ofBitTest (anyBitTest nums)

def andAll (nums : Slice Std.I64) : ℕ := ofBitTest (allBitTest nums)

/-- Whenever the function returns a result r, r is a nonnegative integer less than 2^32, and for every bit position b with 0 <= b < 32, bit b of r is 1 if and only if the number of indices i with 0 <= i < len(nums) such that bit b of nums[i] is 1 is at least k. Here bit b of a nonnegative integer x means (floor(x / 2^b)) mod 2. Also, for every bit position b >= 32, bit b of r is 0.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; and 1 <= k <= len(nums). -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r) :
    0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → (bit r.val b = 1 ↔ k.val ≤ (bitCount nums b : ℤ))) ∧
      (∀ b : ℕ, 32 ≤ b → bit r.val b = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r), 0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → (bit r.val b = 1 ↔ k.val ≤ (bitCount nums b : ℤ))) ∧
      (∀ b : ℕ, 32 ≤ b → bit r.val b = 0)) := by
  sorry

/-- Whenever the function returns a result r, r is a nonnegative integer and r < 2^32; equivalently, 0 <= r <= 2^32 - 1.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; and 1 <= k <= len(nums). -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r) :
    0 ≤ r.val ∧ r.val < 2 ^ 32 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r), 0 ≤ r.val ∧ r.val < 2 ^ 32) := by
  sorry

/-- For every nums and k satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; and 1 <= k <= len(nums). -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ)) :
    ∃ r : Std.I64, find_k_or nums k = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ)), ∃ r : Std.I64, find_k_or nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r is the unique nonnegative integer less than 2^32 such that, for every bit position b with 0 <= b < 32, bit b of r is 1 if and only if there exists an index i with 0 <= i < len(nums) for which bit b of nums[i] is 1; equivalently, r equals the bitwise OR of all elements of nums.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; 1 <= k <= len(nums); and k = 1. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hk_eq : k.val = 1)
    (hres : find_k_or nums k = ok r) :
    0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → (bit r.val b = 1 ↔ hasBit nums b)) ∧
      r.val = (orAll nums : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hk_eq : k.val = 1)
    (hres : find_k_or nums k = ok r), 0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → (bit r.val b = 1 ↔ hasBit nums b)) ∧
      r.val = (orAll nums : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r is the unique nonnegative integer less than 2^32 such that, for every bit position b with 0 <= b < 32, bit b of r is 1 if and only if every index i with 0 <= i < len(nums) has bit b of nums[i] equal to 1; equivalently, r equals the bitwise AND of all elements of nums.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; 1 <= k <= len(nums); and k = len(nums). -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hk_eq : k.val = (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r) :
    0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → (bit r.val b = 1 ↔ allBit nums b)) ∧
      r.val = (andAll nums : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hk_eq : k.val = (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r), 0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → (bit r.val b = 1 ↔ allBit nums b)) ∧
      r.val = (andAll nums : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = nums[0].
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; 1 <= k <= len(nums); and len(nums) = 1. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hlen_eq : nums.val.length = 1)
    (hres : find_k_or nums k = ok r) :
    r.val = (nums.val[0]'(by omega)).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hlen_eq : nums.val.length = 1)
    (hres : find_k_or nums k = ok r), r.val = (nums.val[0]'(by omega)).val) := by
  sorry

/-- Whenever the function returns a result r, r is a nonnegative integer less than 2^32 and, for every bit position b with 0 <= b < 32, if bit b of r is 1 then there exists an index i with 0 <= i < len(nums) such that bit b of nums[i] is 1. Equivalently, every 1-bit of r is also a 1-bit of the bitwise OR of all elements of nums.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; and 1 <= k <= len(nums). -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r) :
    0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → bit r.val b = 1 → hasBit nums b) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r), 0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → bit r.val b = 1 → hasBit nums b)) := by
  sorry

/-- Whenever the function returns a result r, r is a nonnegative integer less than 2^32 and, for every bit position b with 0 <= b < 32, if bit b of nums[i] is 1 for every index i with 0 <= i < len(nums), then bit b of r is 1. Equivalently, every 1-bit of the bitwise AND of all elements of nums is also a 1-bit of r.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; and 1 <= k <= len(nums). -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r) :
    0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → allBit nums b → bit r.val b = 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r), 0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → allBit nums b → bit r.val b = 1)) := by
  sorry

/-- If the function returns r1 on input (nums, k1) and returns r2 on input (nums, k2), then r1 and r2 are nonnegative integers less than 2^32 and, for every bit position b with 0 <= b < 32, if bit b of r2 is 1 then bit b of r1 is 1. Equivalently, every 1-bit of the K-or with threshold k2 is also a 1-bit of the K-or with threshold k1.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; and 1 <= k1 <= k2 <= len(nums). -/
theorem spec_9 (nums : Slice Std.I64) (k1 : Std.I64) (k2 : Std.I64)
    (r1 : Std.I64) (r2 : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k1.val) (hkm : k1.val ≤ k2.val)
    (hk2 : k2.val ≤ (nums.val.length : ℤ))
    (hres1 : find_k_or nums k1 = ok r1) (hres2 : find_k_or nums k2 = ok r2) :
    0 ≤ r1.val ∧ r1.val < 2 ^ 32 ∧ 0 ≤ r2.val ∧ r2.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → bit r2.val b = 1 → bit r1.val b = 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 : Std.I64) (k2 : Std.I64)
    (r1 : Std.I64) (r2 : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k1.val) (hkm : k1.val ≤ k2.val)
    (hk2 : k2.val ≤ (nums.val.length : ℤ))
    (hres1 : find_k_or nums k1 = ok r1) (hres2 : find_k_or nums k2 = ok r2), 0 ≤ r1.val ∧ r1.val < 2 ^ 32 ∧ 0 ≤ r2.val ∧ r2.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → bit r2.val b = 1 → bit r1.val b = 1)) := by
  sorry

/-- If the function returns r on input (nums, k) and returns r' on input (nums2, k), then r = r'.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; 1 <= k <= len(nums); len(nums2) = len(nums); for every j with 0 <= j < len(nums2), 0 <= nums2[j] < 2^32; and nums2 is a permutation of nums, meaning that for every integer v, the number of indices i with 0 <= i < len(nums) and nums[i] = v equals the number of indices j with 0 <= j < len(nums2) and nums2[j] = v. -/
theorem spec_10 (nums nums2 : Slice Std.I64) (k : Std.I64) (r r' : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hlen2 : nums2.val.length = nums.val.length)
    (hval2 : ValInU32 nums2)
    (hperm : PermOf nums nums2)
    (hres : find_k_or nums k = ok r) (hres2 : find_k_or nums2 k = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k : Std.I64) (r r' : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hlen2 : nums2.val.length = nums.val.length)
    (hval2 : ValInU32 nums2)
    (hperm : PermOf nums nums2)
    (hres : find_k_or nums k = ok r) (hres2 : find_k_or nums2 k = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, r is a nonnegative integer less than 2^32 and, for every bit position b with 0 <= b < 32, if bit b of r is 1 then the number of indices i with 0 <= i < len(nums) such that bit b of nums[i] is 1 is at least k. Equivalently, every set bit of r has at least k distinct witnesses in nums.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; and 1 <= k <= len(nums). -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r) :
    0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → bit r.val b = 1 → k.val ≤ (bitCount nums b : ℤ)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r), 0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → bit r.val b = 1 → k.val ≤ (bitCount nums b : ℤ))) := by
  sorry

/-- Whenever the function returns a result r, r is a nonnegative integer less than 2^32 and, for every bit position b with 0 <= b < 32, if bit b of r is 0 then the number of indices i with 0 <= i < len(nums) such that bit b of nums[i] is 1 is at most k - 1. Equivalently, a bit with fewer than k witnesses is cleared in r.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; and 1 <= k <= len(nums). -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r) :
    0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → bit r.val b = 0 → (bitCount nums b : ℤ) ≤ k.val - 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hres : find_k_or nums k = ok r), 0 ≤ r.val ∧ r.val < 2 ^ 32 ∧
      (∀ b : ℕ, b < 32 → bit r.val b = 0 → (bitCount nums b : ℤ) ≤ k.val - 1)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: len(nums) >= 1 and len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^32; 1 <= k <= len(nums); and for every bit position b with 0 <= b < 32, the number of indices i with 0 <= i < len(nums) such that bit b of nums[i] is 1 is less than k. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hfew : ∀ b : ℕ, b < 32 → (bitCount nums b : ℤ) < k.val)
    (hres : find_k_or nums k = ok r) :
    r.val = 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ValInU32 nums)
    (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (nums.val.length : ℤ))
    (hfew : ∀ b : ℕ, b < 32 → (bitCount nums b : ℤ) < k.val)
    (hres : find_k_or nums k = ok r), r.val = 0) := by
  sorry

end AegisSpec.FindKOr
