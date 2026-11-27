import Aegis.TotalHammingDistance.Code.Funs

/-!
# Specifications of `Aegis.TotalHammingDistance.total_hamming_distance`

LeetCode problem `total-hamming-distance`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped BigOperators

namespace AegisSpec.TotalHammingDistance

def vals (s : Aeneas.Std.Slice Aeneas.Std.I64) : List Int :=
  s.val.map (fun x => x.val)

def hd (a b : Int) : Int :=
  (((Finset.range 64).filter
      (fun k => Int.fdiv a ((2 : Int) ^ k) % 2 ≠ Int.fdiv b ((2 : Int) ^ k) % 2)).card : Int)

def pairSum (l : List Int) : Int :=
  ∑ i ∈ Finset.range l.length, ∑ j ∈ Finset.range l.length,
    if i < j then hd (l.getD i 0) (l.getD j 0) else 0

def orderedSum (l : List Int) : Int :=
  ∑ i ∈ Finset.range l.length, ∑ j ∈ Finset.range l.length,
    hd (l.getD i 0) (l.getD j 0)

def crossSum (l₁ l₂ : List Int) : Int :=
  ∑ i ∈ Finset.range l₁.length, ∑ j ∈ Finset.range l₂.length,
    hd (l₁.getD i 0) (l₂.getD j 0)

def c1 (l : List Int) (k : Nat) : Int :=
  (((Finset.range l.length).filter
      (fun i => Int.fdiv (l.getD i 0) ((2 : Int) ^ k) % 2 = 1)).card : Int)

def c0 (l : List Int) (k : Nat) : Int := (l.length : Int) - c1 l k

def countOcc (l : List Int) (v : Int) : Int :=
  (((Finset.range l.length).filter (fun i => l.getD i 0 = v)).card : Int)

def fits32 (x : Int) : Prop := -(2 ^ 31 : Int) ≤ x ∧ x < (2 ^ 31 : Int)

def isPermOf (l₁ l₂ : List Int) : Prop :=
  ∃ pi : Equiv.Perm (Fin l₁.length),
    ∀ j : Fin l₁.length, l₂.getD j.val 0 = l₁.getD (pi j).val 0

def mkSlice (l : List Aeneas.Std.I64) (h : l.length ≤ Aeneas.Std.Usize.max) :
    Aeneas.Std.Slice Aeneas.Std.I64 :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

def concatSlice (A B : Aeneas.Std.Slice Aeneas.Std.I64)
    (h : A.val.length + B.val.length ≤ 10000) : Aeneas.Std.Slice Aeneas.Std.I64 :=
  mkSlice (A.val ++ B.val) (by
    rw [List.length_append]
    have hmax := Aeneas.Std.Usize.cMax_bound_concrete
    omega)

/-- For every nums satisfying the preconditions, total_hamming_distance(nums) returns a result r and r = sum over all pairs 0 <= i < j < len(nums) of HD(nums[i], nums[j]), where HD(a,b) is the number of bit positions k with 0 <= k < 64 such that floor(a/2^k) mod 2 is different from floor(b/2^k) mod 2. The sum over an empty set of pairs, when len(nums) <= 1, is 0.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; and the mathematical sum described in the statement fits in a 32-bit signed integer. -/
theorem spec_1
    (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums))) :
    ∃ r : Aeneas.Std.I64,
      Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r ∧
        r.val = pairSum (vals nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums))), ∃ r : Aeneas.Std.I64,
      Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r ∧
        r.val = pairSum (vals nums)) := by
  sorry

/-- For every nums satisfying the preconditions, the call total_hamming_distance(nums) does not fail: it returns a result r, i.e. Ok r, rather than an overflow, out-of-bounds, or panic result.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; and the mathematical total-Hamming sum fits in a 32-bit signed integer. -/
theorem spec_2
    (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums))) :
    ∃ r : Aeneas.Std.I64,
      Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums))), ∃ r : Aeneas.Std.I64,
      Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r) := by
  sorry

/-- Whenever total_hamming_distance(nums) returns a result r for nums satisfying the preconditions, r >= 0.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; and the mathematical total-Hamming sum fits in a 32-bit signed integer. -/
theorem spec_3
    (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever total_hamming_distance(nums) returns a result r for nums satisfying the preconditions, r <= 30 * (len(nums) * (len(nums) - 1) / 2).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; and the mathematical total-Hamming sum fits in a 32-bit signed integer. -/
theorem spec_4
    (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r) :
    r.val ≤ 30 * (((nums.length * (nums.length - 1) / 2 : Nat)) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r), r.val ≤ 30 * (((nums.length * (nums.length - 1) / 2 : Nat)) : Int)) := by
  sorry

/-- Whenever total_hamming_distance(nums) returns a result r for nums satisfying the preconditions, r = sum from k=0 to 63 of c0(k) * c1(k), where c1(k) is the number of indices i with 0 <= i < len(nums) and floor(nums[i]/2^k) mod 2 = 1, and c0(k) = len(nums) - c1(k).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; and the mathematical total-Hamming sum fits in a 32-bit signed integer. -/
theorem spec_5
    (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r) :
    r.val = ∑ k ∈ Finset.range 64, c0 (vals nums) k * c1 (vals nums) k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r), r.val = ∑ k ∈ Finset.range 64, c0 (vals nums) k * c1 (vals nums) k) := by
  sorry

/-- Whenever total_hamming_distance(nums) returns a result r for nums satisfying the preconditions, 2 * r = sum over 0 <= i < len(nums) and 0 <= j < len(nums) of HD(nums[i], nums[j]), where HD(a,b) is the number of k with 0 <= k < 64 such that floor(a/2^k) mod 2 is different from floor(b/2^k) mod 2.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; and the mathematical total-Hamming sum fits in a 32-bit signed integer. -/
theorem spec_6
    (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r) :
    2 * r.val = orderedSum (vals nums) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r), 2 * r.val = orderedSum (vals nums)) := by
  sorry

/-- Whenever total_hamming_distance(nums) returns r and total_hamming_distance(nums') returns r', we have r = r'.
  Preconditions: nums and nums' are slices of 64-bit integers, both satisfy the problem constraints: 1 <= len(nums) = len(nums') <= 10000, every entry is between 0 and 1000000000, and the mathematical total-Hamming sums fit in a 32-bit signed integer; moreover nums' is a permutation of nums, meaning there is a bijection pi from {0,...,n-1} to itself such that nums'[j] = nums[pi(j)] for every j with 0 <= j < n. -/
theorem spec_7
    (nums nums' : Aeneas.Std.Slice Aeneas.Std.I64)
    (r r' : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hlen_eq : nums'.length = nums.length)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hbound' : ∀ i : Nat, i < nums'.length →
      0 ≤ (vals nums').getD i 0 ∧ (vals nums').getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hfit' : fits32 (pairSum (vals nums')))
    (hperm : isPermOf (vals nums) (vals nums'))
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r)
    (hr' : Aegis.TotalHammingDistance.total_hamming_distance nums' = Aeneas.Std.Result.ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Aeneas.Std.Slice Aeneas.Std.I64)
    (r r' : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hlen_eq : nums'.length = nums.length)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hbound' : ∀ i : Nat, i < nums'.length →
      0 ≤ (vals nums').getD i 0 ∧ (vals nums').getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hfit' : fits32 (pairSum (vals nums')))
    (hperm : isPermOf (vals nums) (vals nums'))
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r)
    (hr' : Aegis.TotalHammingDistance.total_hamming_distance nums' = Aeneas.Std.Result.ok r'), r.val = r'.val) := by
  sorry

/-- Whenever total_hamming_distance(nums) returns a result r under these preconditions, r > 0.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; the mathematical total-Hamming sum fits in a 32-bit signed integer; and there exist indices i,j with 0 <= i < j < len(nums) and nums[i] != nums[j]. -/
theorem spec_8
    (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hwitness : ∃ i j : Nat, i < j ∧ j < nums.length ∧
      (vals nums).getD i 0 ≠ (vals nums).getD j 0)
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r) :
    0 < r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (hwitness : ∃ i j : Nat, i < j ∧ j < nums.length ∧
      (vals nums).getD i 0 ≠ (vals nums).getD j 0)
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r), 0 < r.val) := by
  sorry

/-- Whenever total_hamming_distance(A) returns rA, total_hamming_distance(B) returns rB, and total_hamming_distance(A ++ B) returns rAB, where A ++ B is the concatenation of A followed by B, we have rAB = rA + rB + sum over 0 <= i < len(A) and 0 <= j < len(B) of HD(A[i], B[j]), where HD(a,b) is the number of k with 0 <= k < 64 such that floor(a/2^k) mod 2 is different from floor(b/2^k) mod 2.
  Preconditions: A and B are slices of 64-bit integers with 1 <= len(A), 1 <= len(B), len(A)+len(B) <= 10000; every entry of A and B is between 0 and 1000000000; and the mathematical total-Hamming sums for A, B, and A++B fit in a 32-bit signed integer. -/
theorem spec_9
    (A B : Aeneas.Std.Slice Aeneas.Std.I64)
    (rA rB rAB : Aeneas.Std.I64)
    (hA_lo : 1 ≤ A.length)
    (hB_lo : 1 ≤ B.length)
    (hlen_sum : A.length + B.length ≤ 10000)
    (hboundA : ∀ i : Nat, i < A.length →
      0 ≤ (vals A).getD i 0 ∧ (vals A).getD i 0 ≤ 1000000000)
    (hboundB : ∀ i : Nat, i < B.length →
      0 ≤ (vals B).getD i 0 ∧ (vals B).getD i 0 ≤ 1000000000)
    (hfitA : fits32 (pairSum (vals A)))
    (hfitB : fits32 (pairSum (vals B)))
    (hfitAB : fits32 (pairSum (vals (concatSlice A B hlen_sum))))
    (hrA : Aegis.TotalHammingDistance.total_hamming_distance A = Aeneas.Std.Result.ok rA)
    (hrB : Aegis.TotalHammingDistance.total_hamming_distance B = Aeneas.Std.Result.ok rB)
    (hrAB :
      Aegis.TotalHammingDistance.total_hamming_distance (concatSlice A B hlen_sum) =
        Aeneas.Std.Result.ok rAB) :
    rAB.val = rA.val + rB.val + crossSum (vals A) (vals B) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (A B : Aeneas.Std.Slice Aeneas.Std.I64)
    (rA rB rAB : Aeneas.Std.I64)
    (hA_lo : 1 ≤ A.length)
    (hB_lo : 1 ≤ B.length)
    (hlen_sum : A.length + B.length ≤ 10000)
    (hboundA : ∀ i : Nat, i < A.length →
      0 ≤ (vals A).getD i 0 ∧ (vals A).getD i 0 ≤ 1000000000)
    (hboundB : ∀ i : Nat, i < B.length →
      0 ≤ (vals B).getD i 0 ∧ (vals B).getD i 0 ≤ 1000000000)
    (hfitA : fits32 (pairSum (vals A)))
    (hfitB : fits32 (pairSum (vals B)))
    (hfitAB : fits32 (pairSum (vals (concatSlice A B hlen_sum))))
    (hrA : Aegis.TotalHammingDistance.total_hamming_distance A = Aeneas.Std.Result.ok rA)
    (hrB : Aegis.TotalHammingDistance.total_hamming_distance B = Aeneas.Std.Result.ok rB)
    (hrAB :
      Aegis.TotalHammingDistance.total_hamming_distance (concatSlice A B hlen_sum) =
        Aeneas.Std.Result.ok rAB), rAB.val = rA.val + rB.val + crossSum (vals A) (vals B)) := by
  sorry

/-- For every pair of distinct integers a and b with 0 <= a,b <= 1000000000 such that every entry of nums is equal to a or equal to b, if total_hamming_distance(nums) returns Ok r, then r = c_a * c_b * HD(a,b), where c_a is the number of indices i with nums[i] = a, c_b is the number of indices i with nums[i] = b, and HD(a,b) is the number of bit positions k with 0 <= k < 64 such that floor(a/2^k) mod 2 is different from floor(b/2^k) mod 2.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; the mathematical total-Hamming sum for nums fits in a 32-bit signed integer; and there exist distinct integers a and b with 0 <= a,b <= 1000000000 such that every entry of nums is equal to a or equal to b. -/
theorem spec_10
    (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (a b : Int)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (ha_range : 0 ≤ a ∧ a ≤ 1000000000)
    (hb_range : 0 ≤ b ∧ b ≤ 1000000000)
    (hab : a ≠ b)
    (hcover : ∀ i : Nat, i < nums.length →
      (vals nums).getD i 0 = a ∨ (vals nums).getD i 0 = b)
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r) :
    r.val = countOcc (vals nums) a * countOcc (vals nums) b * hd a b := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (r : Aeneas.Std.I64)
    (a b : Int)
    (hlen_lo : 1 ≤ nums.length)
    (hlen_hi : nums.length ≤ 10000)
    (hbound : ∀ i : Nat, i < nums.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hfit : fits32 (pairSum (vals nums)))
    (ha_range : 0 ≤ a ∧ a ≤ 1000000000)
    (hb_range : 0 ≤ b ∧ b ≤ 1000000000)
    (hab : a ≠ b)
    (hcover : ∀ i : Nat, i < nums.length →
      (vals nums).getD i 0 = a ∨ (vals nums).getD i 0 = b)
    (hr : Aegis.TotalHammingDistance.total_hamming_distance nums = Aeneas.Std.Result.ok r), r.val = countOcc (vals nums) a * countOcc (vals nums) b * hd a b) := by
  sorry

end AegisSpec.TotalHammingDistance
