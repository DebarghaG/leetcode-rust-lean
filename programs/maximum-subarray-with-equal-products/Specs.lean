import Aegis.MaxLength.Code.Funs

/-!
# Specifications of `Aegis.MaxLength.max_length`

LeetCode problem `maximum-subarray-with-equal-products`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxLength

def entry (nums : Slice Std.I64) (i : Nat) (h : i < nums.val.length) : Int :=
  (nums.val.get ⟨i, h⟩).val

def subvals (nums : Slice Std.I64) (l u : Nat) : List Int :=
  List.map (fun x : Std.I64 => x.val) (List.take (u - l) (List.drop l nums.val))

def prodSub (nums : Slice Std.I64) (l u : Nat) : Int :=
  List.prod (subvals nums l u)

def gcdSub (nums : Slice Std.I64) (l u : Nat) : Int :=
  Int.ofNat (List.foldr Nat.gcd 0 (List.map Int.natAbs (subvals nums l u)))

def lcmSub (nums : Slice Std.I64) (l u : Nat) : Int :=
  Int.ofNat (List.foldr Nat.lcm 1 (List.map Int.natAbs (subvals nums l u)))

def ProductEquivalent (nums : Slice Std.I64) (l u : Nat) : Prop :=
  prodSub nums l u = lcmSub nums l u * gcdSub nums l u

def IsProdEqSub (nums : Slice Std.I64) (l u : Nat) : Prop :=
  l < u ∧ u ≤ nums.val.length ∧ ProductEquivalent nums l u

noncomputable def maxProdEqLength (nums : Slice Std.I64) : Nat := by
  classical
  exact ((Finset.range (nums.val.length + 1)).product (Finset.range (nums.val.length + 1))).filter
      (fun p : Nat × Nat => IsProdEqSub nums p.1 p.2)
    |>.sup (fun p : Nat × Nat => p.2 - p.1)

def countGtOne (xs : List Int) : Nat :=
  List.countP (fun x => decide (1 < x)) xs

noncomputable def maxAtMostOneBig (nums : Slice Std.I64) : Nat := by
  classical
  exact ((Finset.range (nums.val.length + 1)).product (Finset.range (nums.val.length + 1))).filter
      (fun p : Nat × Nat =>
        p.1 < p.2 ∧ p.2 ≤ nums.val.length ∧ countGtOne (subvals nums p.1 p.2) ≤ 1)
    |>.sup (fun p : Nat × Nat => p.2 - p.1)

/-- The function returns a result res (it does not fail), and res is the maximum length of a non-empty contiguous subarray of nums that is product equivalent. For indices l and u with 0 <= l < u <= len(nums), define P(l,u) as the product of nums[i] for l <= i < u, G(l,u) as the greatest common divisor of the set {nums[i] | l <= i < u}, and M(l,u) as the least common multiple of that same set, all as positive mathematical integers. The subarray nums[l..u) is product equivalent iff P(l,u) = M(l,u) * G(l,u). Then res = max { u - l | 0 <= l < u <= len(nums) and P(l,u) = M(l,u) * G(l,u) }.
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10) :
    ∃ res, Aegis.MaxLength.max_length nums = ok res ∧
      res.val = (maxProdEqLength nums : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10), ∃ res, Aegis.MaxLength.max_length nums = ok res ∧
      res.val = (maxProdEqLength nums : Int)) := by
  sorry

/-- For every nums satisfying the preconditions, the function returns a result res; it does not fail because of integer overflow, out-of-bounds indexing, or panic.
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10) :
    ∃ res, Aegis.MaxLength.max_length nums = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10), ∃ res, Aegis.MaxLength.max_length nums = ok res) := by
  sorry

/-- Whenever the function returns a result res, res <= len(nums).
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res) :
    res.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res), res.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result res, res >= 2.
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res) :
    2 ≤ res.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res), 2 ≤ res.val) := by
  sorry

/-- Whenever the function returns a result res, there exist indices l and u with 0 <= l < u <= len(nums) such that u - l = res and nums[l..u) is product equivalent, i.e. P(l,u) = M(l,u) * G(l,u) using the definitions from spec_1.
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res) :
    ∃ l u, l < u ∧ u ≤ nums.val.length ∧ ((u - l : Nat) : Int) = res.val ∧
      ProductEquivalent nums l u := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res), ∃ l u, l < u ∧ u ≤ nums.val.length ∧ ((u - l : Nat) : Int) = res.val ∧
      ProductEquivalent nums l u) := by
  sorry

/-- Whenever the function returns a result res, for every pair of indices l and u with 0 <= l < u <= len(nums), if nums[l..u) is product equivalent (P(l,u) = M(l,u) * G(l,u) as in spec_1), then u - l <= res.
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res)
    (l u : Nat) (hlu : l < u) (hu : u ≤ nums.val.length)
    (hpe : ProductEquivalent nums l u) :
    ((u - l : Nat) : Int) ≤ res.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res)
    (l u : Nat) (hlu : l < u) (hu : u ≤ nums.val.length)
    (hpe : ProductEquivalent nums l u), ((u - l : Nat) : Int) ≤ res.val) := by
  sorry

/-- Whenever the function returns a result res, res = len(nums) if and only if the whole array nums[0..len(nums)) is product equivalent.
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res) :
    res.val = (nums.val.length : Int) ↔ ProductEquivalent nums 0 nums.val.length := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res), res.val = (nums.val.length : Int) ↔ ProductEquivalent nums 0 nums.val.length) := by
  sorry

/-- Whenever the function returns a result res, res = 2 if and only if there is no product-equivalent contiguous subarray of length at least 3.
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res) :
    res.val = 2 ↔ ¬ ∃ l u, l < u ∧ u ≤ nums.val.length ∧ 3 ≤ u - l ∧
      ProductEquivalent nums l u := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res), res.val = 2 ↔ ¬ ∃ l u, l < u ∧ u ≤ nums.val.length ∧ 3 ≤ u - l ∧
      ProductEquivalent nums l u) := by
  sorry

/-- Whenever the function returns a result res, res = 2.
  Preconditions: len(nums) = 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen : nums.val.length = 2)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res) :
    res.val = 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 2)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res), res.val = 2) := by
  sorry

/-- Whenever the function returns a result res, res = len(nums).
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] = 1. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), entry nums i h = 1)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res) :
    res.val = (nums.val.length : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), entry nums i h = 1)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res), res.val = (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result res, res = len(nums) if and only if for every pair of indices i and j with 0 <= i < j < len(nums), gcd(nums[i], nums[j]) = 1.
  Preconditions: 3 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res) :
    res.val = (nums.val.length : Int) ↔
      ∀ i j (hi : i < nums.val.length) (hj : j < nums.val.length), i < j →
        Int.gcd (entry nums i hi) (entry nums j hj) = 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res), res.val = (nums.val.length : Int) ↔
      ∀ i j (hi : i < nums.val.length) (hj : j < nums.val.length), i < j →
        Int.gcd (entry nums i hi) (entry nums j hj) = 1) := by
  sorry

/-- For every nums satisfying the preconditions, if the function returns res on nums and returns res_rev on the reversed slice reverse(nums), where (reverse(nums))[i] = nums[len(nums)-1-i] for 0 <= i < len(nums), then res = res_rev.
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (nums_rev : Slice Std.I64) (hrev : nums_rev.val = nums.val.reverse)
    (res res_rev : Std.I64)
    (hres : Aegis.MaxLength.max_length nums = ok res)
    (hres_rev : Aegis.MaxLength.max_length nums_rev = ok res_rev) :
    res = res_rev := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (nums_rev : Slice Std.I64) (hrev : nums_rev.val = nums.val.reverse)
    (res res_rev : Std.I64)
    (hres : Aegis.MaxLength.max_length nums = ok res)
    (hres_rev : Aegis.MaxLength.max_length nums_rev = ok res_rev), res = res_rev) := by
  sorry

/-- Whenever the function returns a result res, let W be the maximum length of a non-empty contiguous subarray nums[l..u) such that at most one index i with l <= i < u has nums[i] > 1. Then res >= max(2, W).
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10. -/
theorem spec_13 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res) :
    ((max 2 (maxAtMostOneBig nums) : Nat) : Int) ≤ res.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res), ((max 2 (maxAtMostOneBig nums) : Nat) : Int) ≤ res.val) := by
  sorry

/-- Whenever the function returns a result res, res <= 4.
  Preconditions: 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 2 <= nums[i] <= 10. -/
theorem spec_14 (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 2 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res) :
    res.val ≤ 4 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (hrange : ∀ i (h : i < nums.val.length), 2 ≤ entry nums i h ∧ entry nums i h ≤ 10)
    (res : Std.I64) (hres : Aegis.MaxLength.max_length nums = ok res), res.val ≤ 4) := by
  sorry

end AegisSpec.MaxLength
