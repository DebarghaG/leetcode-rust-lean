import Aegis.MaxStrength.Code.Funs

/-!
# Specifications of `Aegis.MaxStrength.max_strength`

LeetCode problem `maximum-strength-of-a-group`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxStrength

open Aegis.MaxStrength

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def entry (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def NonemptySubset (l : List ℤ) (S : Finset ℕ) : Prop :=
  S.Nonempty ∧ ∀ i ∈ S, i < l.length

def prodOn (l : List ℤ) (S : Finset ℕ) : ℤ := S.prod (fun i => entry l i)

def prodNonzero (l : List ℤ) : ℤ := (l.filter (fun x => x ≠ 0)).prod

def negCount (l : List ℤ) : ℕ := (l.filter (fun x => x < 0)).length

def negCountOn (l : List ℤ) (S : Finset ℕ) : ℕ := (S.filter (fun i => entry l i < 0)).card

def hasZero (l : List ℤ) : Prop := ∃ i, i < l.length ∧ entry l i = 0

def allNonpos (l : List ℤ) : Prop := ∀ i, i < l.length → entry l i ≤ 0

def IsMaxOf (l : List ℤ) (m : ℤ) : Prop :=
  (∃ i, i < l.length ∧ entry l i = m) ∧ ∀ i, i < l.length → entry l i ≤ m

def IsMaxOfNegatives (l : List ℤ) (m : ℤ) : Prop :=
  (∃ i, i < l.length ∧ entry l i = m ∧ m < 0) ∧
    ∀ i, i < l.length → entry l i < 0 → entry l i ≤ m

/-- Let n = len(nums). For each nonempty subset S of {0,...,n-1}, define P(S) = product over i in S of nums[i]. The function returns a result r and r is the maximum value of P(S) over all nonempty subsets S; that is, (a) there exists a nonempty S with r = P(S), and (b) for every nonempty S, P(S) <= r.
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9) :
    ∃ r : Std.I64, max_strength nums = ok r ∧
      (∃ S, NonemptySubset (vals nums) S ∧ r.val = prodOn (vals nums) S) ∧
      (∀ S, NonemptySubset (vals nums) S → prodOn (vals nums) S ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9), ∃ r : Std.I64, max_strength nums = ok r ∧
      (∃ S, NonemptySubset (vals nums) S ∧ r.val = prodOn (vals nums) S) ∧
      (∀ S, NonemptySubset (vals nums) S → prodOn (vals nums) S ≤ r.val)) := by
  sorry

/-- The function returns a result r; it does not fail due to i64 overflow, out-of-bounds indexing, or panic.
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9) :
    ∃ r : Std.I64, max_strength nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9), ∃ r : Std.I64, max_strength nums = ok r) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result r, there exists a nonempty subset S of {0,...,n-1} with r = product over i in S of nums[i]. Moreover: if r > 0, S can be chosen with nums[i] != 0 for all i in S and with an even number of indices i in S satisfying nums[i] < 0; if r < 0, S can be chosen with nums[i] != 0 for all i in S and with an odd number of such indices; if r = 0, S can be chosen containing an index i with nums[i] = 0.
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9) :
    ∀ r : Std.I64, max_strength nums = ok r →
      (∃ S, NonemptySubset (vals nums) S ∧ r.val = prodOn (vals nums) S) ∧
      (0 < r.val →
        ∃ S, NonemptySubset (vals nums) S ∧ r.val = prodOn (vals nums) S ∧
          (∀ i ∈ S, entry (vals nums) i ≠ 0) ∧ Even (negCountOn (vals nums) S)) ∧
      (r.val < 0 →
        ∃ S, NonemptySubset (vals nums) S ∧ r.val = prodOn (vals nums) S ∧
          (∀ i ∈ S, entry (vals nums) i ≠ 0) ∧ Odd (negCountOn (vals nums) S)) ∧
      (r.val = 0 →
        ∃ S, NonemptySubset (vals nums) S ∧ r.val = prodOn (vals nums) S ∧
          ∃ i ∈ S, entry (vals nums) i = 0) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9), ∀ r : Std.I64, max_strength nums = ok r →
      (∃ S, NonemptySubset (vals nums) S ∧ r.val = prodOn (vals nums) S) ∧
      (0 < r.val →
        ∃ S, NonemptySubset (vals nums) S ∧ r.val = prodOn (vals nums) S ∧
          (∀ i ∈ S, entry (vals nums) i ≠ 0) ∧ Even (negCountOn (vals nums) S)) ∧
      (r.val < 0 →
        ∃ S, NonemptySubset (vals nums) S ∧ r.val = prodOn (vals nums) S ∧
          (∀ i ∈ S, entry (vals nums) i ≠ 0) ∧ Odd (negCountOn (vals nums) S)) ∧
      (r.val = 0 →
        ∃ S, NonemptySubset (vals nums) S ∧ r.val = prodOn (vals nums) S ∧
          ∃ i ∈ S, entry (vals nums) i = 0)) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result r, for every nonempty subset S of {0,...,n-1}, product over i in S of nums[i] <= r.
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9) :
    ∀ r : Std.I64, max_strength nums = ok r →
      ∀ S, NonemptySubset (vals nums) S → prodOn (vals nums) S ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9), ∀ r : Std.I64, max_strength nums = ok r →
      ∀ S, NonemptySubset (vals nums) S → prodOn (vals nums) S ≤ r.val) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result r, for every i with 0 <= i < n, r >= nums[i].
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9) :
    ∀ r : Std.I64, max_strength nums = ok r →
      ∀ i, i < (vals nums).length → entry (vals nums) i ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9), ∀ r : Std.I64, max_strength nums = ok r →
      ∀ i, i < (vals nums).length → entry (vals nums) i ≤ r.val) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result r, r < 0 if and only if n = 1 and nums[0] < 0.
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9) :
    ∀ r : Std.I64, max_strength nums = ok r →
      (r.val < 0 ↔ (vals nums).length = 1 ∧ entry (vals nums) 0 < 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9), ∀ r : Std.I64, max_strength nums = ok r →
      (r.val < 0 ↔ (vals nums).length = 1 ∧ entry (vals nums) 0 < 0)) := by
  sorry

/-- The function returns a result r and r = nums[0].
  Preconditions: len(nums) = 1 and -9 <= nums[0] <= 9. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len : (vals nums).length = 1)
    (h_bounds : -9 ≤ entry (vals nums) 0 ∧ entry (vals nums) 0 ≤ 9) :
    ∃ r : Std.I64, max_strength nums = ok r ∧ r.val = entry (vals nums) 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : (vals nums).length = 1)
    (h_bounds : -9 ≤ entry (vals nums) 0 ∧ entry (vals nums) 0 ≤ 9), ∃ r : Std.I64, max_strength nums = ok r ∧ r.val = entry (vals nums) 0) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), nums[i] = 0. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_zeros : ∀ i, i < (vals nums).length → entry (vals nums) i = 0) :
    ∀ r : Std.I64, max_strength nums = ok r → r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_zeros : ∀ i, i < (vals nums).length → entry (vals nums) i = 0), ∀ r : Std.I64, max_strength nums = ok r → r.val = 0) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result r, r = product over i = 0 to n-1 of nums[i].
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9 and nums[i] > 0. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_pos : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ 0 < entry (vals nums) i) :
    ∀ r : Std.I64, max_strength nums = ok r → r.val = (vals nums).prod := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_pos : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ 0 < entry (vals nums) i), ∀ r : Std.I64, max_strength nums = ok r → r.val = (vals nums).prod) := by
  sorry

/-- Let n = len(nums) and let Prod = product over i = 0 to n-1 of nums[i]. Whenever the function returns a result r: if n = 1, then r = nums[0]; if n >= 2 and n is even, then r = Prod; if n >= 2 and n is odd, then r = Prod / m, where m is the largest value among nums[0],...,nums[n-1] (the negative entry closest to zero), and the division is exact.
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9 and nums[i] < 0. -/
theorem spec_10 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_neg : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i < 0) :
    ∀ r : Std.I64, max_strength nums = ok r →
      ((vals nums).length = 1 → r.val = entry (vals nums) 0) ∧
      (2 ≤ (vals nums).length → Even (vals nums).length → r.val = (vals nums).prod) ∧
      (2 ≤ (vals nums).length → Odd (vals nums).length →
        ∃ m, IsMaxOf (vals nums) m ∧ r.val = (vals nums).prod / m ∧ m * r.val = (vals nums).prod) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_neg : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i < 0), ∀ r : Std.I64, max_strength nums = ok r →
      ((vals nums).length = 1 → r.val = entry (vals nums) 0) ∧
      (2 ≤ (vals nums).length → Even (vals nums).length → r.val = (vals nums).prod) ∧
      (2 ≤ (vals nums).length → Odd (vals nums).length →
        ∃ m, IsMaxOf (vals nums) m ∧ r.val = (vals nums).prod / m ∧ m * r.val = (vals nums).prod)) := by
  sorry

/-- Whenever the function returns a result r, r = nums[j].
  Preconditions: len(nums) >= 1, len(nums) <= 13, for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9, and there exists j with 0 <= j < len(nums) such that nums[j] > 0 and for every i with 0 <= i < len(nums) and i != j, nums[i] = 0. -/
theorem spec_11 (nums : Slice Std.I64) (j : ℕ)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9)
    (h_j_lt : j < (vals nums).length)
    (h_j_pos : 0 < entry (vals nums) j)
    (h_others_zero : ∀ i, i < (vals nums).length → i ≠ j → entry (vals nums) i = 0) :
    ∀ r : Std.I64, max_strength nums = ok r → r.val = entry (vals nums) j := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (j : ℕ)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9)
    (h_j_lt : j < (vals nums).length)
    (h_j_pos : 0 < entry (vals nums) j)
    (h_others_zero : ∀ i, i < (vals nums).length → i ≠ j → entry (vals nums) i = 0), ∀ r : Std.I64, max_strength nums = ok r → r.val = entry (vals nums) j) := by
  sorry

/-- Let n = len(nums) and let negCount be the number of indices i with 0 <= i < n and nums[i] < 0. Whenever the function returns a result r, r = 0 if and only if (there exists i with 0 <= i < n and nums[i] = 0) and (for every i with 0 <= i < n, nums[i] <= 0) and negCount <= 1.
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9. -/
theorem spec_12 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9) :
    ∀ r : Std.I64, max_strength nums = ok r →
      (r.val = 0 ↔ hasZero (vals nums) ∧ allNonpos (vals nums) ∧ negCount (vals nums) ≤ 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9), ∀ r : Std.I64, max_strength nums = ok r →
      (r.val = 0 ↔ hasZero (vals nums) ∧ allNonpos (vals nums) ∧ negCount (vals nums) ≤ 1)) := by
  sorry

/-- Let N = {i | 0 <= i < len(nums) and nums[i] != 0}. Whenever the function returns a result r, r = product over i in N of nums[i].
  Preconditions: len(nums) >= 1, len(nums) <= 13, for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9, there exists i with nums[i] != 0, and the number of indices i with nums[i] < 0 is even. -/
theorem spec_13 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9)
    (h_some_nonzero : ∃ i, i < (vals nums).length ∧ entry (vals nums) i ≠ 0)
    (h_even : Even (negCount (vals nums))) :
    ∀ r : Std.I64, max_strength nums = ok r → r.val = prodNonzero (vals nums) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9)
    (h_some_nonzero : ∃ i, i < (vals nums).length ∧ entry (vals nums) i ≠ 0)
    (h_even : Even (negCount (vals nums))), ∀ r : Std.I64, max_strength nums = ok r → r.val = prodNonzero (vals nums)) := by
  sorry

/-- Let N = {i | 0 <= i < len(nums) and nums[i] != 0}. Let m be the largest value among the negative entries, i.e. m = max { nums[i] | 0 <= i < len(nums) and nums[i] < 0 }. Whenever the function returns a result r, r = (product over i in N of nums[i]) / m, and the division is exact.
  Preconditions: len(nums) >= 1, len(nums) <= 13, for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9, the number of indices i with nums[i] < 0 is odd, and either there exists i with nums[i] > 0 or the number of negative entries is at least 3. -/
theorem spec_14 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9)
    (h_odd : Odd (negCount (vals nums)))
    (h_case : (∃ i, i < (vals nums).length ∧ 1 < entry (vals nums) i) ∨
      3 ≤ negCount (vals nums)) :
    ∀ r : Std.I64, max_strength nums = ok r →
      ∃ m, IsMaxOfNegatives (vals nums) m ∧
        r.val = prodNonzero (vals nums) / m ∧ m * r.val = prodNonzero (vals nums) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9)
    (h_odd : Odd (negCount (vals nums)))
    (h_case : (∃ i, i < (vals nums).length ∧ 1 < entry (vals nums) i) ∨
      3 ≤ negCount (vals nums)), ∀ r : Std.I64, max_strength nums = ok r →
      ∃ m, IsMaxOfNegatives (vals nums) m ∧
        r.val = prodNonzero (vals nums) / m ∧ m * r.val = prodNonzero (vals nums)) := by
  sorry

/-- Let n = len(nums). For every slice nums' of length n that is a permutation of nums (there is a bijection pi on {0,...,n-1} with nums'[j] = nums[pi(j)] for every j), the function returns the same result on nums' as on nums; both calls return results and their results are equal.
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9. -/
theorem spec_15 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9) :
    ∀ nums' : Slice Std.I64, (vals nums').Perm (vals nums) →
      ∃ r r' : Std.I64, max_strength nums = ok r ∧ max_strength nums' = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9), ∀ nums' : Slice Std.I64, (vals nums').Perm (vals nums) →
      ∃ r r' : Std.I64, max_strength nums = ok r ∧ max_strength nums' = ok r' ∧ r.val = r'.val) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result r, if r > 0 then for every i with 0 <= i < n and nums[i] > 1 there exists an integer k such that r = nums[i] * k.
  Preconditions: len(nums) >= 1, len(nums) <= 13, and for every i with 0 <= i < len(nums), -9 <= nums[i] <= 9. -/
theorem spec_16 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9) :
    ∀ r : Std.I64, max_strength nums = ok r →
      0 < r.val → ∀ i, i < (vals nums).length → 1 < entry (vals nums) i →
        ∃ k : ℤ, r.val = entry (vals nums) i * k := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ (vals nums).length)
    (h_len_le : (vals nums).length ≤ 13)
    (h_bounds : ∀ i, i < (vals nums).length → -9 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 9), ∀ r : Std.I64, max_strength nums = ok r →
      0 < r.val → ∀ i, i < (vals nums).length → 1 < entry (vals nums) i →
        ∃ k : ℤ, r.val = entry (vals nums) i * k) := by
  sorry

end AegisSpec.MaxStrength
