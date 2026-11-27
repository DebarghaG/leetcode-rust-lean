import Aegis.Permute.Code.Funs

/-!
# Specifications of `Aegis.Permute.permute`

LeetCode problem `permutations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Permute

def IsPermOf (nums p : List Std.I64) : Prop :=
  ∃ (hlen : p.length = nums.length) (pi : Fin nums.length → Fin nums.length),
    Function.Bijective pi ∧
      ∀ i : Fin nums.length, p.get ⟨i.val, hlen.symm ▸ i.isLt⟩ = nums.get (pi i)

def countRows (rows : List (alloc.vec.Vec Std.I64)) (n i : Nat) (v : Std.I64) : Nat :=
  (rows.filter (fun row => decide (row.val.length = n ∧ row.val[i]? = some v))).length

/-- The function returns a result r and, for n = len(nums), both of the following hold. (1) For every j with 0 <= j < len(r), the entry r[j] is a permutation of nums: len(r[j]) = n and there exists a bijection pi from {0,...,n-1} to itself such that r[j][i] = nums[pi(i)] for every i with 0 <= i < n. (2) For every sequence p of 64-bit integers that is a permutation of nums (i.e. len(p) = n and p[i] = nums[pi(i)] for every i with 0 <= i < n for some bijection pi from {0,...,n-1} to itself), there is exactly one index j with 0 <= j < len(r) such that len(r[j]) = n and r[j][i] = p[i] for every i with 0 <= i < n. No condition is imposed on the order of the entries r[0],...,r[len(r)-1].
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Permute.permute nums = ok r ∧
        (∀ j : Fin r.val.length, IsPermOf nums.val (r.val.get j).val) ∧
        (∀ p : List Std.I64, IsPermOf nums.val p →
          ∃! j : Fin r.val.length, (r.val.get j).val = p) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Permute.permute nums = ok r ∧
        (∀ j : Fin r.val.length, IsPermOf nums.val (r.val.get j).val) ∧
        (∀ p : List Std.I64, IsPermOf nums.val p →
          ∃! j : Fin r.val.length, (r.val.get j).val = p)) := by
  sorry

/-- Whenever the function is called with an input satisfying the preconditions, it returns a result r; that is, it does not fail, panic, or overflow. No further property of r is claimed here.
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), Aegis.Permute.permute nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), Aegis.Permute.permute nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, with n = len(nums), len(r) = n! = 1*2*...*n, the product of all integers from 1 to n (so for n=1 the value is 1).
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r) :
    r.val.length = Nat.factorial nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r), r.val.length = Nat.factorial nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), len(r[j]) = len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r) :
    ∀ j : Fin r.val.length, (r.val.get j).val.length = nums.val.length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r), ∀ j : Fin r.val.length, (r.val.get j).val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), the entry r[j] is a permutation of nums: len(r[j]) = len(nums) and there exists a bijection pi from {0,...,len(nums)-1} to itself such that r[j][i] = nums[pi(i)] for every i with 0 <= i < len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r) :
    ∀ j : Fin r.val.length, IsPermOf nums.val (r.val.get j).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r), ∀ j : Fin r.val.length, IsPermOf nums.val (r.val.get j).val) := by
  sorry

/-- Whenever the function returns a result r, for every sequence p of 64-bit integers that is a permutation of nums (i.e. len(p) = len(nums) and p[i] = nums[pi(i)] for every i with 0 <= i < len(nums) for some bijection pi from {0,...,len(nums)-1} to itself), there exists an index j with 0 <= j < len(r) such that len(r[j]) = len(nums) and r[j][i] = p[i] for every i with 0 <= i < len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r) :
    ∀ p : List Std.I64, IsPermOf nums.val p →
      ∃ j : Fin r.val.length,
        (r.val.get j).val.length = nums.val.length ∧ (r.val.get j).val = p := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r), ∀ p : List Std.I64, IsPermOf nums.val p →
      ∃ j : Fin r.val.length,
        (r.val.get j).val.length = nums.val.length ∧ (r.val.get j).val = p) := by
  sorry

/-- Whenever the function returns a result r, for every j, k with 0 <= j < k < len(r), the entries r[j] and r[k] are not equal as sequences: either len(r[j]) != len(r[k]) or there exists i with 0 <= i < len(r[j]) such that r[j][i] != r[k][i].
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r) :
    ∀ j k : Fin r.val.length, j ≠ k → (r.val.get j).val ≠ (r.val.get k).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r), ∀ j k : Fin r.val.length, j ≠ k → (r.val.get j).val ≠ (r.val.get k).val) := by
  sorry

/-- Whenever the function returns a result r, there exists j with 0 <= j < len(r) such that len(r[j]) = len(nums) and r[j][i] = nums[i] for every i with 0 <= i < len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r) :
    ∃ j : Fin r.val.length,
      (r.val.get j).val.length = nums.val.length ∧ (r.val.get j).val = nums.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r), ∃ j : Fin r.val.length,
      (r.val.get j).val.length = nums.val.length ∧ (r.val.get j).val = nums.val) := by
  sorry

/-- Whenever the function returns a result r, with n = len(nums), there exists j with 0 <= j < len(r) such that len(r[j]) = n and r[j][i] = nums[n-1-i] for every i with 0 <= i < n.
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r) :
    ∃ j : Fin r.val.length,
      (r.val.get j).val.length = nums.val.length ∧ (r.val.get j).val = nums.val.reverse := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r), ∃ j : Fin r.val.length,
      (r.val.get j).val.length = nums.val.length ∧ (r.val.get j).val = nums.val.reverse) := by
  sorry

/-- Whenever the function returns a result r and len(nums) = 1, then len(r) = 1 and r[0] is the one-element sequence whose only value is nums[0].
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r)
    (hlen1 : nums.val.length = 1) :
    r.val.map (fun row => row.val) = [nums.val] := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r)
    (hlen1 : nums.val.length = 1), r.val.map (fun row => row.val) = [nums.val]) := by
  sorry

/-- Whenever the function returns a result r, for every j and i with 0 <= j < len(r) and 0 <= i < len(r[j]), there exists k with 0 <= k < len(nums) such that r[j][i] = nums[k].
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r) :
    ∀ j : Fin r.val.length, ∀ i : Fin (r.val.get j).val.length,
      ∃ k : Fin nums.val.length, (r.val.get j).val.get i = nums.val.get k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r), ∀ j : Fin r.val.length, ∀ i : Fin (r.val.get j).val.length,
      ∃ k : Fin nums.val.length, (r.val.get j).val.get i = nums.val.get k) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r) and every k with 0 <= k < len(nums), there exists i with 0 <= i < len(r[j]) such that r[j][i] = nums[k].
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r) :
    ∀ j : Fin r.val.length, ∀ k : Fin nums.val.length,
      ∃ i : Fin (r.val.get j).val.length, (r.val.get j).val.get i = nums.val.get k := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r), ∀ j : Fin r.val.length, ∀ k : Fin nums.val.length,
      ∃ i : Fin (r.val.get j).val.length, (r.val.get j).val.get i = nums.val.get k) := by
  sorry

/-- Whenever the function returns a result r, with n = len(nums), for every position i with 0 <= i < n and every index k with 0 <= k < n, the number of indices j such that 0 <= j < len(r), len(r[j]) = n, and r[j][i] = nums[k] is (n-1)! = 1*2*...*(n-1) (with 0! = 1).
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_13 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r) :
    ∀ i : Fin nums.val.length, ∀ k : Fin nums.val.length,
      countRows r.val nums.val.length i.val (nums.val.get k) =
        Nat.factorial (nums.val.length - 1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r), ∀ i : Fin nums.val.length, ∀ k : Fin nums.val.length,
      countRows r.val nums.val.length i.val (nums.val.get k) =
        Nat.factorial (nums.val.length - 1)) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r) such that len(r[j]) = len(nums), and for every bijection sigma from {0,...,len(nums)-1} to itself, there exists k with 0 <= k < len(r) such that len(r[k]) = len(nums) and r[k][i] = r[j][sigma(i)] for every i with 0 <= i < len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_14 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r)
    (j : Fin r.val.length) (hj : (r.val.get j).val.length = nums.val.length)
    (sigma : Fin nums.val.length → Fin nums.val.length) (hsigma : Function.Bijective sigma) :
    ∃ k : Fin r.val.length,
      (r.val.get k).val.length = nums.val.length ∧
        ∀ i : Fin nums.val.length,
          (r.val.get k).val[i.val]? = (r.val.get j).val[(sigma i).val]? := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r)
    (j : Fin r.val.length) (hj : (r.val.get j).val.length = nums.val.length)
    (sigma : Fin nums.val.length → Fin nums.val.length) (hsigma : Function.Bijective sigma), ∃ k : Fin r.val.length,
      (r.val.get k).val.length = nums.val.length ∧
        ∀ i : Fin nums.val.length,
          (r.val.get k).val[i.val]? = (r.val.get j).val[(sigma i).val]?) := by
  sorry

/-- Whenever the function returns a result r, for every j and i with 0 <= j < len(r) and 0 <= i < len(r[j]), -10 <= r[j][i] <= 10.
  Preconditions: len(nums) >= 1 and len(nums) <= 6; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_15 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r) :
    ∀ j : Fin r.val.length, ∀ i : Fin (r.val.get j).val.length,
      -10 ≤ ((r.val.get j).val.get i).val ∧ ((r.val.get j).val.get i).val ≤ 10 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 6)
    (hbound : ∀ i : Fin nums.val.length, -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
    (huniq : ∀ i j : Fin nums.val.length, i ≠ j → nums.val.get i ≠ nums.val.get j)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (h : Aegis.Permute.permute nums = ok r), ∀ j : Fin r.val.length, ∀ i : Fin (r.val.get j).val.length,
      -10 ≤ ((r.val.get j).val.get i).val ∧ ((r.val.get j).val.get i).val ≤ 10) := by
  sorry

end AegisSpec.Permute
