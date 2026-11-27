import Aegis.MinimumArrayLength.Code.Funs

/-!
# Specifications of `Aegis.MinimumArrayLength.minimum_array_length`

LeetCode problem `minimize-length-of-array-using-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumArrayLength

def vals (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def minElem : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl (fun acc y => if y < acc then y else acc) x

def countEq (l : List Int) (m : Int) : Nat := (l.filter (fun x => x = m)).length

def allDiv (l : List Int) (m : Int) : Prop := ∀ x ∈ l, x % m = 0

def someNonDiv (l : List Int) (m : Int) : Prop :=
  ∃ i, ∃ hi : i < l.length, l[i]'hi % m ≠ 0

def countPos (l : List Int) : Nat := (l.filter (fun x => 0 < x)).length

def Pre (nums : Slice I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
    ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000

def eraseTwo (l : List Int) (i j : Nat) : List Int :=
  (l.eraseIdx i).eraseIdx (if i < j then j - 1 else j)

def Step (A B : List Int) : Prop :=
  ∃ (i j : Nat), ∃ (_ : i < A.length) (_ : j < A.length),
    i ≠ j ∧ 0 < A[i] ∧ 0 < A[j] ∧ B = eraseTwo A i j ++ [A[i] % A[j]]

def Reach (A B : List Int) : Prop := Relation.ReflTransGen Step A B

/-- The function returns a result r (it does not fail). Let mn be the minimum element of nums (which exists because len(nums) >= 1), let cnt be the number of indices i with 0 <= i < len(nums) and nums[i] = mn, and let allDiv be the condition that for every i with 0 <= i < len(nums), nums[i] % mn = 0. Then r = (cnt + 1) / 2 (integer division) if allDiv holds, and r = 1 if allDiv does not hold. Equivalently, r is the minimum length of an array achievable from nums by any finite sequence of allowed operations, where an allowed operation on an array A chooses distinct indices i,j with A[i] > 0 and A[j] > 0, removes A[i] and A[j], and appends A[i] % A[j].
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice I64) (h : Pre nums) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      (allDiv (vals nums) (minElem (vals nums)) →
        r.val = (((countEq (vals nums) (minElem (vals nums)) + 1) / 2 : Nat) : Int)) ∧
      (¬ allDiv (vals nums) (minElem (vals nums)) → r.val = 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      (allDiv (vals nums) (minElem (vals nums)) →
        r.val = (((countEq (vals nums) (minElem (vals nums)) + 1) / 2 : Nat) : Int)) ∧
      (¬ allDiv (vals nums) (minElem (vals nums)) → r.val = 1)) := by
  sorry

/-- The function returns a result r and 1 <= r <= len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice I64) (h : Pre nums) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- The function returns a result r. Let mn be the minimum element of nums and let cnt be the number of indices i with nums[i] = mn. Then r <= (cnt + 1) / 2 (integer division).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice I64) (h : Pre nums) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      r.val ≤ (((countEq (vals nums) (minElem (vals nums)) + 1) / 2 : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      r.val ≤ (((countEq (vals nums) (minElem (vals nums)) + 1) / 2 : Nat) : Int)) := by
  sorry

/-- If len(nums) = 2, then the function returns a result r and r = 1.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice I64) (h : Pre nums) (hlen : nums.val.length = 2) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧ r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums) (hlen : nums.val.length = 2), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧ r.val = 1) := by
  sorry

/-- Let mn be the minimum element of nums. If there exists an index i with 0 <= i < len(nums) such that nums[i] % mn != 0, then the function returns a result r and r = 1.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice I64) (h : Pre nums)
    (hnd : someNonDiv (vals nums) (minElem (vals nums))) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧ r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums)
    (hnd : someNonDiv (vals nums) (minElem (vals nums))), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧ r.val = 1) := by
  sorry

/-- Let mn be the minimum element of nums and let cnt be the number of indices i with nums[i] = mn. If for every i with 0 <= i < len(nums), nums[i] % mn = 0, then the function returns a result r and r = (cnt + 1) / 2 (integer division).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice I64) (h : Pre nums)
    (hd : allDiv (vals nums) (minElem (vals nums))) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      r.val = (((countEq (vals nums) (minElem (vals nums)) + 1) / 2 : Nat) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums)
    (hd : allDiv (vals nums) (minElem (vals nums))), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      r.val = (((countEq (vals nums) (minElem (vals nums)) + 1) / 2 : Nat) : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no overflow, no panic, no out-of-bounds access).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice I64) (h : Pre nums) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r) := by
  sorry

/-- The function returns a result r and there exists a finite sequence of zero or more allowed operations that transforms nums into an array of length r. (An allowed operation on an array A chooses distinct indices i,j with A[i] > 0 and A[j] > 0, removes A[i] and A[j], and appends A[i] % A[j].)
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : Slice I64) (h : Pre nums) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      ∃ B : List Int, Reach (vals nums) B ∧ (B.length : Int) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      ∃ B : List Int, Reach (vals nums) B ∧ (B.length : Int) = r.val) := by
  sorry

/-- The function returns a result r and for every finite sequence of allowed operations that transforms nums into an array B, we have len(B) >= r. (An allowed operation on an array A chooses distinct indices i,j with A[i] > 0 and A[j] > 0, removes A[i] and A[j], and appends A[i] % A[j].)
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_9 (nums : Slice I64) (h : Pre nums) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      ∀ B : List Int, Reach (vals nums) B → r.val ≤ (B.length : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      ∀ B : List Int, Reach (vals nums) B → r.val ≤ (B.length : Int)) := by
  sorry

/-- The function returns a result r. Let mn be the minimum element of nums and let cnt be the number of indices i with nums[i] = mn. Then r = 1 if and only if either (a) there exists an index i with nums[i] % mn != 0, or (b) cnt <= 2.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_10 (nums : Slice I64) (h : Pre nums) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      (r.val = 1 ↔ someNonDiv (vals nums) (minElem (vals nums)) ∨
        countEq (vals nums) (minElem (vals nums)) ≤ 2) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      (r.val = 1 ↔ someNonDiv (vals nums) (minElem (vals nums)) ∨
        countEq (vals nums) (minElem (vals nums)) ≤ 2)) := by
  sorry

/-- The function returns a result r and for every slice nums' satisfying the preconditions and with the same multiset of values as nums, the function minimum_array_length(nums') also returns r.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_11 (nums : Slice I64) (h : Pre nums) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      ∀ nums' : Slice I64, Pre nums' → List.Perm nums'.val nums.val →
        Aegis.MinimumArrayLength.minimum_array_length nums' = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      ∀ nums' : Slice I64, Pre nums' → List.Perm nums'.val nums.val →
        Aegis.MinimumArrayLength.minimum_array_length nums' = ok r) := by
  sorry

/-- The function returns a result r and there exists a finite sequence of allowed operations that transforms nums into an array B with len(B) = r and with at most one index i such that B[i] > 0. (An allowed operation on an array A chooses distinct indices i,j with A[i] > 0 and A[j] > 0, removes A[i] and A[j], and appends A[i] % A[j].)
  Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_12 (nums : Slice I64) (h : Pre nums) :
    ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      ∃ B : List Int, Reach (vals nums) B ∧ (B.length : Int) = r.val ∧ countPos B ≤ 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (h : Pre nums), ∃ r, Aegis.MinimumArrayLength.minimum_array_length nums = ok r ∧
      ∃ B : List Int, Reach (vals nums) B ∧ (B.length : Int) = r.val ∧ countPos B ≤ 1) := by
  sorry

  end AegisSpec.MinimumArrayLength
