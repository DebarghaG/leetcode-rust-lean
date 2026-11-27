import Aegis.MaximumXor.Code.Funs
import Mathlib.Data.Int.Bitwise

/-!
# Specifications of `Aegis.MaximumXor.maximum_xor`

LeetCode problem `maximum-xor-after-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.MaximumXor

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

@[simp]
theorem vals_length (nums : Slice Std.I64) : (vals nums).length = nums.val.length := by
  simp [vals]

@[simp]
theorem vals_length_leng (nums : Slice Std.I64) : (vals nums).length = nums.leng := by
  have h : ∀ {n : ℕ} (l : Aeneas.Data.ListN.ListN Std.I64 n), l.toList.length = n :=
    fun l => by
      induction l with
      | nil => rfl
      | cons x xs ih => simp [Aeneas.Data.ListN.ListN.toList, ih]
  simpa [vals, Slice.val] using h nums.list

def IsSubmask (a b : ℤ) : Prop := Int.land a b = a

def orAll (l : List ℤ) : ℤ := l.foldl (fun acc x => Int.lor acc x) 0

def xorAll (l : List ℤ) : ℤ := l.foldl (fun acc x => Int.xor acc x) 0

/-- The function returns a result r, and r is the maximum possible bitwise XOR of all elements after applying the operation any number of times. Equivalently, let b range over all arrays of length len(nums) such that for every i with 0 <= i < len(nums), b[i] is a bitwise submask of nums[i] (i.e., every 1-bit of b[i] is also a 1-bit of nums[i], or (b[i] AND nums[i]) = b[i]); then r = max { b[0] XOR b[1] XOR ... XOR b[len(nums)-1] }. Equivalently, r = nums[0] OR nums[1] OR ... OR nums[len(nums)-1], the bitwise OR of all elements of nums.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000) :
    ∃ r, Aegis.MaximumXor.maximum_xor nums = ok r ∧
      r.val = orAll (vals nums) ∧
      (∀ (b : List ℤ) (hb : b.length = (vals nums).length)
          (hbm : ∀ (i : ℕ) (hi : i < (vals nums).length), IsSubmask b[i] (vals nums)[i]),
        xorAll b ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000), ∃ r, Aegis.MaximumXor.maximum_xor nums = ok r ∧
      r.val = orAll (vals nums) ∧
      (∀ (b : List ℤ) (hb : b.length = (vals nums).length)
          (hbm : ∀ (i : ℕ) (hi : i < (vals nums).length), IsSubmask b[i] (vals nums)[i]),
        xorAll b ≤ r.val)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 134217727 (i.e., r < 2^27).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r) :
    0 ≤ r.val ∧ r.val ≤ 134217727 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r), 0 ≤ r.val ∧ r.val ≤ 134217727) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(nums), r >= nums[i] (ordinary integer ordering).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r) :
    ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums)[i] ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r), ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums)[i] ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(nums), nums[i] is a bitwise submask of r; equivalently, (nums[i] AND r) = nums[i], or (nums[i] OR r) = r.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r) :
    ∀ (i : ℕ) (hi : i < (vals nums).length), IsSubmask (vals nums)[i] r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r), ∀ (i : ℕ) (hi : i < (vals nums).length), IsSubmask (vals nums)[i] r.val) := by
  sorry

/-- Whenever the function returns a result r, for every non-negative 64-bit integer y, if for every i with 0 <= i < len(nums) we have (nums[i] AND y) = nums[i] (i.e., every nums[i] is a submask of y), then r <= y.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r) :
    ∀ (y : Std.I64) (hy : 0 ≤ y.val)
      (hsub : ∀ (i : ℕ) (hi : i < (vals nums).length), IsSubmask (vals nums)[i] y.val),
      r.val ≤ y.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r), ∀ (y : Std.I64) (hy : 0 ≤ y.val)
      (hsub : ∀ (i : ℕ) (hi : i < (vals nums).length), IsSubmask (vals nums)[i] y.val),
      r.val ≤ y.val) := by
  sorry

/-- Whenever the function returns a result r, for every array b of length len(nums) such that for every i with 0 <= i < len(nums), b[i] is a bitwise submask of nums[i] (i.e., (b[i] AND nums[i]) = b[i]), the bitwise XOR b[0] XOR b[1] XOR ... XOR b[len(nums)-1] is at most r (ordinary integer ordering).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r) :
    ∀ (b : List ℤ) (hb : b.length = (vals nums).length)
      (hbm : ∀ (i : ℕ) (hi : i < (vals nums).length), IsSubmask b[i] (vals nums)[i]),
      xorAll b ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r), ∀ (b : List ℤ) (hb : b.length = (vals nums).length)
      (hbm : ∀ (i : ℕ) (hi : i < (vals nums).length), IsSubmask b[i] (vals nums)[i]),
      xorAll b ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an array b of length len(nums) such that for every i with 0 <= i < len(nums), b[i] is a bitwise submask of nums[i] (i.e., (b[i] AND nums[i]) = b[i]), and b[0] XOR b[1] XOR ... XOR b[len(nums)-1] = r.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r) :
    ∃ (b : List ℤ) (hb : b.length = (vals nums).length),
      (∀ (i : ℕ) (hi : i < (vals nums).length), IsSubmask b[i] (vals nums)[i]) ∧
      xorAll b = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r), ∃ (b : List ℤ) (hb : b.length = (vals nums).length),
      (∀ (i : ℕ) (hi : i < (vals nums).length), IsSubmask b[i] (vals nums)[i]) ∧
      xorAll b = r.val) := by
  sorry

/-- Under these conditions, the result returned by maximum_xor for nums equals the result returned by maximum_xor for nums'.
  Preconditions: For two arrays nums and nums' of length n = len(nums), both satisfy 1 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 100000000 and 0 <= nums'[i] <= 100000000; and there is a permutation π of {0,...,n-1} such that nums'[i] = nums[π(i)] for every i. -/
theorem spec_8 (nums nums' : Slice Std.I64) (n : ℕ)
    (hn : n = (vals nums).length)
    (hn' : n = (vals nums').length)
    (hlen_low : 1 ≤ n)
    (hlen_high : n ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < n), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    (hbounds' : ∀ (i : ℕ) (hi : i < n), 0 ≤ (vals nums')[i] ∧ (vals nums')[i] ≤ 100000000)
    (hperm : ∃ π : Equiv.Perm (Fin n),
      ∀ (i : Fin n), (vals nums')[i.val] = (vals nums)[(π i).val])
    (r r' : Std.I64)
    (hr : Aegis.MaximumXor.maximum_xor nums = ok r)
    (hr' : Aegis.MaximumXor.maximum_xor nums' = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (n : ℕ)
    (hn : n = (vals nums).length)
    (hn' : n = (vals nums').length)
    (hlen_low : 1 ≤ n)
    (hlen_high : n ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < n), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    (hbounds' : ∀ (i : ℕ) (hi : i < n), 0 ≤ (vals nums')[i] ∧ (vals nums')[i] ≤ 100000000)
    (hperm : ∃ π : Equiv.Perm (Fin n),
      ∀ (i : Fin n), (vals nums')[i.val] = (vals nums)[(π i).val])
    (r r' : Std.I64)
    (hr : Aegis.MaximumXor.maximum_xor nums = ok r)
    (hr' : Aegis.MaximumXor.maximum_xor nums' = ok r'), r = r') := by
  sorry

/-- For every r and r', if maximum_xor nums returns r and maximum_xor nums' returns r', then r <= r' (ordinary integer ordering).
  Preconditions: For two arrays nums and nums' of the same length n with 1 <= n <= 100000, both satisfying for every i with 0 <= i < n, 0 <= nums[i] <= 100000000 and 0 <= nums'[i] <= 100000000, and for every i with 0 <= i < n, nums[i] is a bitwise submask of nums'[i] (i.e., (nums[i] AND nums'[i]) = nums[i]). -/
theorem spec_9 (nums nums' : Slice Std.I64) (n : ℕ)
    (hn : n = (vals nums).length)
    (hn' : n = (vals nums').length)
    (hlen_low : 1 ≤ n)
    (hlen_high : n ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < n), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    (hbounds' : ∀ (i : ℕ) (hi : i < n), 0 ≤ (vals nums')[i] ∧ (vals nums')[i] ≤ 100000000)
    (hsub : ∀ (i : ℕ) (hi : i < n), IsSubmask (vals nums)[i] (vals nums')[i])
    (r r' : Std.I64)
    (hr : Aegis.MaximumXor.maximum_xor nums = ok r)
    (hr' : Aegis.MaximumXor.maximum_xor nums' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (n : ℕ)
    (hn : n = (vals nums).length)
    (hn' : n = (vals nums').length)
    (hlen_low : 1 ≤ n)
    (hlen_high : n ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < n), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    (hbounds' : ∀ (i : ℕ) (hi : i < n), 0 ≤ (vals nums')[i] ∧ (vals nums')[i] ≤ 100000000)
    (hsub : ∀ (i : ℕ) (hi : i < n), IsSubmask (vals nums)[i] (vals nums')[i])
    (r r' : Std.I64)
    (hr : Aegis.MaximumXor.maximum_xor nums = ok r)
    (hr' : Aegis.MaximumXor.maximum_xor nums' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns a result r, for every bit position k with 0 <= k < 64, if every element nums[i] has bit k equal to 0, then r has bit k equal to 0.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r) :
    ∀ (k : ℕ) (hk : k < 64)
      (hzero : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums)[i].testBit k = false),
      r.val.testBit k = false := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ (vals nums).length)
    (hlen_high : (vals nums).length ≤ 100000)
    (hbounds : ∀ (i : ℕ) (hi : i < (vals nums).length),
      0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100000000)
    {r : Std.I64} (hr : Aegis.MaximumXor.maximum_xor nums = ok r), ∀ (k : ℕ) (hk : k < 64)
      (hzero : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums)[i].testBit k = false),
      r.val.testBit k = false) := by
  sorry

end AegisSpec.MaximumXor
