import Aegis.DistinctAverages.Code.Funs

/-!
# Specifications of `Aegis.DistinctAverages.distinct_averages`

LeetCode problem `number-of-distinct-averages`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.DistinctAverages

namespace AegisSpec.DistinctAverages

def values (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def IsNondecReorder (a : List Int) (l : List Int) : Prop := a.Pairwise (· ≤ ·) ∧ a.Perm l

def pairSums (a : List Int) : List Int :=
  ((a.take (a.length / 2)).zip a.reverse).map (fun p => p.1 + p.2)

def distinctCount (l : List Int) : Nat := l.dedup.length

def IsMinOf (m : Int) (l : List Int) : Prop := m ∈ l ∧ ∀ x ∈ l, m ≤ x

def IsMaxOf (m : Int) (l : List Int) : Prop := m ∈ l ∧ ∀ x ∈ l, x ≤ m

/-- Let n = len(nums). Let a be a sequence of length n, sorted in nondecreasing order, whose entries are exactly the entries of nums with the same multiplicities. The function returns a result r and r = the number of distinct integers in the set { a[i] + a[n-1-i] | 0 <= i < n/2 }.
  Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 0 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_1 (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100) :
    ∃ r : I64, distinct_averages nums = ok r ∧
      ∀ a : List Int, IsNondecReorder a (values nums) →
        r.val = (distinctCount (pairSums a) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100), ∃ r : I64, distinct_averages nums = ok r ∧
      ∀ a : List Int, IsNondecReorder a (values nums) →
        r.val = (distinctCount (pairSums a) : Int)) := by
  sorry

/-- The function returns a result; it does not fail, panic, overflow, or access an index out of bounds.
  Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 0 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_2 (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100) :
    ∃ r : I64, distinct_averages nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100), ∃ r : I64, distinct_averages nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 0 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_3 (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100) :
    ∀ r : I64, distinct_averages nums = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100), ∀ r : I64, distinct_averages nums = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= len(nums)/2.
  Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 0 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_4 (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100) :
    ∀ r : I64, distinct_averages nums = ok r → r.val ≤ ((nums.val.length / 2 : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100), ∀ r : I64, distinct_averages nums = ok r → r.val ≤ ((nums.val.length / 2 : Nat) : Int)) := by
  sorry

/-- The function returns a result r and r = n/2.
  Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 0 <= nums[i] <= 100 for every i with 0 <= i < len(nums). Let n = len(nums) and let a be nums sorted in nondecreasing order. For every i and j with 0 <= i < j < n/2, a[i] + a[n-1-i] != a[j] + a[n-1-j]. -/
theorem spec_5 (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
    (h_pairwise : ∀ a : List Int, IsNondecReorder a (values nums) → (pairSums a).Nodup) :
    ∃ r : I64, distinct_averages nums = ok r ∧ r.val = ((nums.val.length / 2 : Nat) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
    (h_pairwise : ∀ a : List Int, IsNondecReorder a (values nums) → (pairSums a).Nodup), ∃ r : I64, distinct_averages nums = ok r ∧ r.val = ((nums.val.length / 2 : Nat) : Int)) := by
  sorry

/-- Let n = len(nums) and let a be nums sorted in nondecreasing order. Whenever the function returns a result r, r = 1 if and only if a[i] + a[n-1-i] = a[0] + a[n-1] for every i with 0 <= i < n/2.
  Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 0 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100) :
    ∀ r : I64, distinct_averages nums = ok r →
      ∀ a : List Int, IsNondecReorder a (values nums) →
        (r.val = 1 ↔ ∀ x ∈ pairSums a, x = (pairSums a).headD 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100), ∀ r : I64, distinct_averages nums = ok r →
      ∀ a : List Int, IsNondecReorder a (values nums) →
        (r.val = 1 ↔ ∀ x ∈ pairSums a, x = (pairSums a).headD 0)) := by
  sorry

/-- If distinct_averages(nums) returns r and distinct_averages(nums') returns r', then r = r'.
  Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 0 <= nums[i] <= 100 for every i with 0 <= i < len(nums). Also nums' is any slice with the same length and the same entries as nums with the same multiplicities. -/
theorem spec_7 (nums nums' : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
    (h_len' : nums'.val.length = nums.val.length)
    (h_same_entries : (values nums').Perm (values nums)) :
    ∀ (r r' : I64), distinct_averages nums = ok r → distinct_averages nums' = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
    (h_len' : nums'.val.length = nums.val.length)
    (h_same_entries : (values nums').Perm (values nums)), ∀ (r r' : I64), distinct_averages nums = ok r → distinct_averages nums' = ok r' → r = r') := by
  sorry

/-- Let n = len(nums) and let a be nums sorted in nondecreasing order. Whenever the function returns a result r, the set S = { a[i] + a[n-1-i] | 0 <= i < n/2 } has cardinality r and contains min(nums) + max(nums).
  Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 0 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_8 (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100) :
    ∃ mn mx : Int, IsMinOf mn (values nums) ∧ IsMaxOf mx (values nums) ∧
      ∃ r : I64, distinct_averages nums = ok r ∧
        ∀ a : List Int, IsNondecReorder a (values nums) →
          (distinctCount (pairSums a) : Int) = r.val ∧ mn + mx ∈ pairSums a := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (h_even : nums.val.length % 2 = 0)
    (h_ge_two : 2 ≤ nums.val.length)
    (h_le_hundred : nums.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100), ∃ mn mx : Int, IsMinOf mn (values nums) ∧ IsMaxOf mx (values nums) ∧
      ∃ r : I64, distinct_averages nums = ok r ∧
        ∀ a : List Int, IsNondecReorder a (values nums) →
          (distinctCount (pairSums a) : Int) = r.val ∧ mn + mx ∈ pairSums a) := by
  sorry

end AegisSpec.DistinctAverages
