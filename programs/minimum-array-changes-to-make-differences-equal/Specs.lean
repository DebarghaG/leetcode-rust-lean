import Aegis.MinChanges.Code.Funs

/-!
# Specifications of `Aegis.MinChanges.min_changes`

LeetCode problem `minimum-array-changes-to-make-differences-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinChanges

def ivs (s : Slice I64) : List ℤ := s.val.map fun x => x.val

def entry (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def pairDiff (a : List ℤ) (j : ℕ) : ℤ := |entry a j - entry a (a.length - 1 - j)|

def unequalCount (a : List ℤ) : ℕ :=
  (List.range (a.length / 2)).countP fun j =>
    decide (entry a j ≠ entry a (a.length - 1 - j))

def diffCount (a : List ℤ) (X : ℤ) : ℕ :=
  (List.range (a.length / 2)).countP fun j => decide (pairDiff a j = X)

def maxDiffCount (a : List ℤ) (k : ℤ) : ℕ :=
  (Finset.range (k.toNat + 1)).sup fun i => diffCount a (i : ℤ)

def Admissible (a : List ℤ) (k : ℤ) (b : List ℤ) : Prop :=
  b.length = a.length ∧
    (∀ i, i < a.length → 0 ≤ entry b i ∧ entry b i ≤ k) ∧
    ∃ X : ℤ,
      0 ≤ X ∧ X ≤ k ∧
        ∀ j, j < a.length / 2 → |entry b j - entry b (a.length - 1 - j)| = X

def changes (a b : List ℤ) : ℕ :=
  (List.range a.length).countP fun i => decide (entry b i ≠ entry a i)

def costSet (a : List ℤ) (k : ℤ) (j : ℕ) (X : ℤ) (c : ℕ) : Prop :=
  ∃ u v : ℤ,
    0 ≤ u ∧ u ≤ k ∧ 0 ≤ v ∧ v ≤ k ∧ |u - v| = X ∧
      c = (if u ≠ entry a j then 1 else 0) +
        (if v ≠ entry a (a.length - 1 - j) then 1 else 0)

noncomputable def pairCost (a : List ℤ) (k : ℤ) (j : ℕ) (X : ℤ) : ℕ := by
  classical
  exact if costSet a k j X 0 then 0 else if costSet a k j X 1 then 1 else 2

noncomputable def costSum (a : List ℤ) (k : ℤ) (X : ℤ) : ℤ :=
  (Finset.range (a.length / 2)).sum fun j => (pairCost a k j X : ℤ)

/-- Whenever min_changes nums k returns a result r, the following holds. Let n = len(nums) and m = n/2. For a length-n sequence b of integers, call b admissible when 0 <= b[i] <= k for every i with 0 <= i < n and there exists an integer X with 0 <= X <= k such that |b[j] - b[n-1-j]| = X for every j with 0 <= j < m. Let changes(b) be the number of indices i with 0 <= i < n and b[i] != nums[i]. Then r is the minimum value of changes(b) over all admissible b; equivalently, there exists an admissible b with changes(b) = r and every admissible b has changes(b) >= r.
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k. -/
theorem spec_1 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val) :
    ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        (∃ b : List ℤ,
            Admissible (ivs nums) k.val b ∧ (changes (ivs nums) b : ℤ) = r.val) ∧
          (∀ b : List ℤ,
            Admissible (ivs nums) k.val b → r.val ≤ (changes (ivs nums) b : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val), ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        (∃ b : List ℤ,
            Admissible (ivs nums) k.val b ∧ (changes (ivs nums) b : ℤ) = r.val) ∧
          (∀ b : List ℤ,
            Admissible (ivs nums) k.val b → r.val ≤ (changes (ivs nums) b : ℤ))) := by
  sorry

/-- The call min_changes nums k returns a result r; in particular it does not fail, overflow, index out of bounds, or panic.
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k. -/
theorem spec_2 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val) :
    ∃ r : I64, Aegis.MinChanges.min_changes nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val), ∃ r : I64, Aegis.MinChanges.min_changes nums k = ok r) := by
  sorry

/-- Whenever min_changes nums k returns a result r, 0 <= r <= len(nums)/2.
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k. -/
theorem spec_3 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val) :
    ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        0 ≤ r.val ∧ r.val ≤ (((ivs nums).length / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val), ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        0 ≤ r.val ∧ r.val ≤ (((ivs nums).length / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever min_changes nums k returns a result r, r = 0.
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, for every i with 0 <= i < n, 0 <= nums[i] <= k, and additionally len(nums) = 2. -/
theorem spec_4 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val)
    (h_len : nums.val.length = 2) :
    ∀ r : I64, Aegis.MinChanges.min_changes nums k = ok r → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val)
    (h_len : nums.val.length = 2), ∀ r : I64, Aegis.MinChanges.min_changes nums k = ok r → r.val = 0) := by
  sorry

/-- Whenever min_changes nums k returns a result r, r = 0 if and only if there exists an integer X with 0 <= X <= k such that for every j with 0 <= j < len(nums)/2, |nums[j] - nums[len(nums)-1-j]| = X.
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k. -/
theorem spec_5 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val) :
    ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        (r.val = 0 ↔
          ∃ X : ℤ,
            0 ≤ X ∧ X ≤ k.val ∧
              ∀ j : ℕ, j < (ivs nums).length / 2 → pairDiff (ivs nums) j = X) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val), ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        (r.val = 0 ↔
          ∃ X : ℤ,
            0 ≤ X ∧ X ≤ k.val ∧
              ∀ j : ℕ, j < (ivs nums).length / 2 → pairDiff (ivs nums) j = X)) := by
  sorry

/-- Whenever min_changes nums k returns a result r, r <= the number of indices j with 0 <= j < len(nums)/2 and nums[j] != nums[len(nums)-1-j].
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k. -/
theorem spec_6 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val) :
    ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        r.val ≤ ((unequalCount (ivs nums) : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val), ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        r.val ≤ ((unequalCount (ivs nums) : ℕ) : ℤ)) := by
  sorry

/-- Let n = len(nums), m = n/2, and for each j with 0 <= j < m let D_j = |nums[j] - nums[n-1-j]|. Let F be the maximum, over all integers X with 0 <= X <= k, of the number of j with 0 <= j < m and D_j = X. Whenever min_changes nums k returns a result r, r >= m - F.
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k. -/
theorem spec_7 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val) :
    ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        (((ivs nums).length / 2 : ℕ) : ℤ) -
            ((maxDiffCount (ivs nums) k.val : ℕ) : ℤ) ≤
          r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val), ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        (((ivs nums).length / 2 : ℕ) : ℤ) -
            ((maxDiffCount (ivs nums) k.val : ℕ) : ℤ) ≤
          r.val) := by
  sorry

/-- Let n = len(nums) and m = n/2. For each j with 0 <= j < m and each integer X with 0 <= X <= k, let c_j(X) be the least nonnegative integer c for which there exist integers u and v with 0 <= u <= k, 0 <= v <= k, |u-v| = X, and c = (if u != nums[j] then 1 else 0) + (if v != nums[n-1-j] then 1 else 0). Whenever min_changes nums k returns a result r, for every integer X with 0 <= X <= k we have r <= sum_{j=0}^{m-1} c_j(X).
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k. -/
theorem spec_8 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val) :
    ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        ∀ X : ℤ, 0 ≤ X → X ≤ k.val → r.val ≤ costSum (ivs nums) k.val X := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val), ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        ∀ X : ℤ, 0 ≤ X → X ≤ k.val → r.val ≤ costSum (ivs nums) k.val X) := by
  sorry

/-- Let n = len(nums) and m = n/2. For each j with 0 <= j < m and each integer X with 0 <= X <= k, let c_j(X) be the least nonnegative integer c for which there exist integers u and v with 0 <= u <= k, 0 <= v <= k, |u-v| = X, and c = (if u != nums[j] then 1 else 0) + (if v != nums[n-1-j] then 1 else 0). Whenever min_changes nums k returns a result r, there exists an integer X with 0 <= X <= k such that r = sum_{j=0}^{m-1} c_j(X).
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k. -/
theorem spec_9 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val) :
    ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        ∃ X : ℤ, 0 ≤ X ∧ X ≤ k.val ∧ r.val = costSum (ivs nums) k.val X := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val), ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        ∃ X : ℤ, 0 ≤ X ∧ X ≤ k.val ∧ r.val = costSum (ivs nums) k.val X) := by
  sorry

/-- Let n = len(nums), and let nums' be the sequence of length n defined by nums'[i] = nums[n-1-i] for every i with 0 <= i < n. If min_changes nums k returns a result r and min_changes nums' k returns a result r', then r = r'.
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k. -/
theorem spec_10 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val) :
    ∀ (nums' : Slice I64) (r r' : I64),
      ivs nums' = (ivs nums).reverse →
        Aegis.MinChanges.min_changes nums k = ok r →
          Aegis.MinChanges.min_changes nums' k = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val), ∀ (nums' : Slice I64) (r r' : I64),
      ivs nums' = (ivs nums).reverse →
        Aegis.MinChanges.min_changes nums k = ok r →
          Aegis.MinChanges.min_changes nums' k = ok r' → r = r') := by
  sorry

/-- Let n = len(nums) and m = n/2. For any sequence nums' of length n such that for every j with 0 <= j < m either (nums'[j] = nums[j] and nums'[n-1-j] = nums[n-1-j]) or (nums'[j] = nums[n-1-j] and nums'[n-1-j] = nums[j]), if min_changes nums k returns a result r and min_changes nums' k returns a result r', then r = r'.
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k. -/
theorem spec_11 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val) :
    ∀ (nums' : Slice I64) (r r' : I64),
      nums'.val.length = nums.val.length →
        (∀ j : ℕ,
            j < (ivs nums).length / 2 →
              (entry (ivs nums') j = entry (ivs nums) j ∧
                  entry (ivs nums') ((ivs nums).length - 1 - j) =
                    entry (ivs nums) ((ivs nums).length - 1 - j)) ∨
                (entry (ivs nums') j = entry (ivs nums) ((ivs nums).length - 1 - j) ∧
                  entry (ivs nums') ((ivs nums).length - 1 - j) =
                    entry (ivs nums) j)) →
          Aegis.MinChanges.min_changes nums k = ok r →
            Aegis.MinChanges.min_changes nums' k = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val), ∀ (nums' : Slice I64) (r r' : I64),
      nums'.val.length = nums.val.length →
        (∀ j : ℕ,
            j < (ivs nums).length / 2 →
              (entry (ivs nums') j = entry (ivs nums) j ∧
                  entry (ivs nums') ((ivs nums).length - 1 - j) =
                    entry (ivs nums) ((ivs nums).length - 1 - j)) ∨
                (entry (ivs nums') j = entry (ivs nums) ((ivs nums).length - 1 - j) ∧
                  entry (ivs nums') ((ivs nums).length - 1 - j) =
                    entry (ivs nums) j)) →
          Aegis.MinChanges.min_changes nums k = ok r →
            Aegis.MinChanges.min_changes nums' k = ok r' → r = r') := by
  sorry

/-- If min_changes nums k1 returns a result r1 and min_changes nums k2 returns a result r2, then r2 <= r1.
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers. n is even, 2 <= n <= 100000. Let k1 and k2 be 64-bit integers with 0 <= k1 <= k2 <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k1. -/
theorem spec_12 (nums : Slice I64) (k1 k2 : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k1_ge : 0 ≤ k1.val)
    (h_k12 : k1.val ≤ k2.val) (h_k2_le : k2.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k1.val) :
    ∀ r1 r2 : I64,
      Aegis.MinChanges.min_changes nums k1 = ok r1 →
        Aegis.MinChanges.min_changes nums k2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (k1 k2 : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k1_ge : 0 ≤ k1.val)
    (h_k12 : k1.val ≤ k2.val) (h_k2_le : k2.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k1.val), ∀ r1 r2 : I64,
      Aegis.MinChanges.min_changes nums k1 = ok r1 →
        Aegis.MinChanges.min_changes nums k2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- Let n = len(nums), m = n/2, and let t be the number of j with 0 <= j < m and nums[j] != nums[n-1-j]. Whenever min_changes nums k returns a result r, r = min(t, m - t).
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, for every i with 0 <= i < n, 0 <= nums[i] <= k, and additionally k = 1. -/
theorem spec_13 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val)
    (h_k : k.val = 1) :
    ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        r.val =
          ((min (unequalCount (ivs nums))
                ((ivs nums).length / 2 - unequalCount (ivs nums)) : ℕ) : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val)
    (h_k : k.val = 1), ∀ r : I64,
      Aegis.MinChanges.min_changes nums k = ok r →
        r.val =
          ((min (unequalCount (ivs nums))
                ((ivs nums).length / 2 - unequalCount (ivs nums)) : ℕ) : ℤ)) := by
  sorry

/-- Let n = len(nums), m = n/2, and let π be any permutation of {0,...,m-1}. Define nums' of length n by nums'[j] = nums[π(j)] and nums'[n-1-j] = nums[n-1-π(j)] for every j with 0 <= j < m. If min_changes nums k returns a result r and min_changes nums' k returns a result r', then r = r'.
  Preconditions: Let n = len(nums). nums is a slice of 64-bit integers and k is a 64-bit integer. n is even, 2 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= k. -/
theorem spec_14 (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val) :
    ∀ (π : ℕ → ℕ) (nums' : Slice I64) (r r' : I64),
      nums'.val.length = nums.val.length →
        (∀ i : ℕ, i < (ivs nums).length / 2 → π i < (ivs nums).length / 2) →
          (∀ i j : ℕ,
              i < (ivs nums).length / 2 → j < (ivs nums).length / 2 → π i = π j → i = j) →
            (∀ j : ℕ,
                j < (ivs nums).length / 2 →
                  entry (ivs nums') j = entry (ivs nums) (π j) ∧
                    entry (ivs nums') ((ivs nums).length - 1 - j) =
                      entry (ivs nums) ((ivs nums).length - 1 - π j)) →
              Aegis.MinChanges.min_changes nums k = ok r →
                Aegis.MinChanges.min_changes nums' k = ok r' → r = r' := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_even : nums.val.length % 2 = 0) (h_len_ge : 2 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000) (h_k_ge : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_bnd : ∀ i, i < nums.val.length →
      0 ≤ entry (ivs nums) i ∧ entry (ivs nums) i ≤ k.val), ∀ (π : ℕ → ℕ) (nums' : Slice I64) (r r' : I64),
      nums'.val.length = nums.val.length →
        (∀ i : ℕ, i < (ivs nums).length / 2 → π i < (ivs nums).length / 2) →
          (∀ i j : ℕ,
              i < (ivs nums).length / 2 → j < (ivs nums).length / 2 → π i = π j → i = j) →
            (∀ j : ℕ,
                j < (ivs nums).length / 2 →
                  entry (ivs nums') j = entry (ivs nums) (π j) ∧
                    entry (ivs nums') ((ivs nums).length - 1 - j) =
                      entry (ivs nums) ((ivs nums).length - 1 - π j)) →
              Aegis.MinChanges.min_changes nums k = ok r →
                Aegis.MinChanges.min_changes nums' k = ok r' → r = r') := by
  sorry

end AegisSpec.MinChanges
