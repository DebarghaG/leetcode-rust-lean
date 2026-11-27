import Aegis.MinDeletion.Code.Funs

/-!
# Specifications of `Aegis.MinDeletion.min_deletion`

LeetCode problem `minimum-deletions-to-make-array-beautiful`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinDeletion (min_deletion)

namespace AegisSpec.MinDeletion

def Beautiful {α : Type} (l : List α) : Prop :=
  l.length % 2 = 0 ∧ ∀ j : ℕ, j < l.length / 2 → l[2 * j]? ≠ l[2 * j + 1]?

def IsSubsequence {α : Type} (b : List α) (nums : Slice α) : Prop :=
  ∃ idx : Fin b.length → Fin nums.val.length,
    StrictMono idx ∧ ∀ t : Fin b.length, b[t] = nums.val[idx t]

def IsMaxBeautifulLen (L : ℕ) (nums : Slice I64) : Prop :=
  (∃ b : List I64, IsSubsequence b nums ∧ Beautiful b ∧ b.length = L) ∧
    ∀ b : List I64, IsSubsequence b nums → Beautiful b → b.length ≤ L

/-- The function returns a result r (it does not fail) and r = n - L, where L is the maximum length of a beautiful subsequence of nums. A sequence b of length m is beautiful iff m is even and, for every j with 0 <= j < m/2, b[2j] != b[2j+1]; the empty sequence is beautiful. A subsequence of nums is obtained by choosing indices 0 <= i_0 < i_1 < ... < i_{m-1} < n and setting b[t] = nums[i_t].
  Preconditions: Let n = len(nums). 0 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000) :
    ∃ r : I64, min_deletion nums = ok r ∧
      ∃ L : ℕ, IsMaxBeautifulLen L nums ∧ r.val = (nums.val.length : ℤ) - (L : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000), ∃ r : I64, min_deletion nums = ok r ∧
      ∃ L : ℕ, IsMaxBeautifulLen L nums ∧ r.val = (nums.val.length : ℤ) - (L : ℤ)) := by
  sorry

/-- For every nums satisfying the preconditions, the function returns a result r; it does not overflow, panic, or fail.
  Preconditions: Let n = len(nums). 0 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000) :
    ∃ r : I64, min_deletion nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000), ∃ r : I64, min_deletion nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n.
  Preconditions: Let n = len(nums). 0 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000) :
    ∀ r : I64, min_deletion nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000), ∀ r : I64, min_deletion nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, the integer n - r is even (equivalently, r and n have the same parity).
  Preconditions: Let n = len(nums). 0 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_4 (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000) :
    ∀ r : I64, min_deletion nums = ok r → Even ((nums.val.length : ℤ) - r.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000), ∀ r : I64, min_deletion nums = ok r → Even ((nums.val.length : ℤ) - r.val)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if nums itself is beautiful, i.e., n is even and nums[2j] != nums[2j+1] for every j with 0 <= j < n/2.
  Preconditions: Let n = len(nums). 0 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_5 (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000) :
    ∀ r : I64, min_deletion nums = ok r → (r.val = 0 ↔ Beautiful nums.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000), ∀ r : I64, min_deletion nums = ok r → (r.val = 0 ↔ Beautiful nums.val)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: n = len(nums) = 0. -/
theorem spec_6 (nums : Slice I64)
    (hn0 : nums.val.length = 0) :
    ∀ r : I64, min_deletion nums = ok r → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hn0 : nums.val.length = 0), ∀ r : I64, min_deletion nums = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: n = len(nums) = 1. -/
theorem spec_7 (nums : Slice I64)
    (hn1 : nums.val.length = 1) :
    ∀ r : I64, min_deletion nums = ok r → r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hn1 : nums.val.length = 1), ∀ r : I64, min_deletion nums = ok r → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, r = n.
  Preconditions: Let n = len(nums). 0 <= n <= 100000, for every i with 0 <= i < n, 0 <= nums[i] <= 100000, and for every i,j with 0 <= i < n and 0 <= j < n, nums[i] = nums[j]. -/
theorem spec_8 (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
    (hconst : ∀ i (hi : i < nums.val.length) (j) (hj : j < nums.val.length),
      nums.val[i]'hi = nums.val[j]'hj) :
    ∀ r : I64, min_deletion nums = ok r → r.val = (nums.val.length : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
    (hconst : ∀ i (hi : i < nums.val.length) (j) (hj : j < nums.val.length),
      nums.val[i]'hi = nums.val[j]'hj), ∀ r : I64, min_deletion nums = ok r → r.val = (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r <= n - 2.
  Preconditions: Let n = len(nums). 0 <= n <= 100000, for every i with 0 <= i < n, 0 <= nums[i] <= 100000, and there exist indices i,j with 0 <= i < j < n and nums[i] != nums[j]. -/
theorem spec_9 (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
    (hwit : ∃ i j : ℕ, i < j ∧ j < nums.val.length ∧ nums.val[i]! ≠ nums.val[j]!) :
    ∀ r : I64, min_deletion nums = ok r → r.val ≤ (nums.val.length : ℤ) - 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
    (hwit : ∃ i j : ℕ, i < j ∧ j < nums.val.length ∧ nums.val[i]! ≠ nums.val[j]!), ∀ r : I64, min_deletion nums = ok r → r.val ≤ (nums.val.length : ℤ) - 2) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: Let n = len(nums). 0 <= n <= 100000, for every i with 0 <= i < n, 0 <= nums[i] <= 100000, and n is odd. -/
theorem spec_10 (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
    (hodd : nums.val.length % 2 = 1) :
    ∀ r : I64, min_deletion nums = ok r → 1 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
    (hodd : nums.val.length % 2 = 1), ∀ r : I64, min_deletion nums = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, every beautiful subsequence b of nums has length at most n - r. Here a subsequence b of length m is beautiful iff m is even and b[2j] != b[2j+1] for every j with 0 <= j < m/2.
  Preconditions: Let n = len(nums). 0 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_11 (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000) :
    ∀ r : I64, min_deletion nums = ok r →
      ∀ b : List I64, IsSubsequence b nums → Beautiful b →
        (b.length : ℤ) ≤ (nums.val.length : ℤ) - r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000), ∀ r : I64, min_deletion nums = ok r →
      ∀ b : List I64, IsSubsequence b nums → Beautiful b →
        (b.length : ℤ) ≤ (nums.val.length : ℤ) - r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a beautiful subsequence b of nums with len(b) = n - r. Here a subsequence b of length m is beautiful iff m is even and b[2j] != b[2j+1] for every j with 0 <= j < m/2.
  Preconditions: Let n = len(nums). 0 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_12 (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000) :
    ∀ r : I64, min_deletion nums = ok r →
      ∃ b : List I64,
        IsSubsequence b nums ∧ Beautiful b ∧
          (b.length : ℤ) = (nums.val.length : ℤ) - r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000), ∀ r : I64, min_deletion nums = ok r →
      ∃ b : List I64,
        IsSubsequence b nums ∧ Beautiful b ∧
          (b.length : ℤ) = (nums.val.length : ℤ) - r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= 2.
  Preconditions: Let n = len(nums). 0 <= n <= 100000, for every i with 0 <= i < n, 0 <= nums[i] <= 100000, n is even, and nums is not beautiful (i.e., there exists j with 0 <= j < n/2 and nums[2j] = nums[2j+1]). -/
theorem spec_13 (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
    (heven : nums.val.length % 2 = 0)
    (hnot : ¬ Beautiful nums.val) :
    ∀ r : I64, min_deletion nums = ok r → 2 ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64)
    (hn : nums.val.length ≤ 100000)
    (hval : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
    (heven : nums.val.length % 2 = 0)
    (hnot : ¬ Beautiful nums.val), ∀ r : I64, min_deletion nums = ok r → 2 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if nums[0] != nums[1] then r = 0, and if nums[0] = nums[1] then r = 2.
  Preconditions: Let n = len(nums) = 2, and 0 <= nums[0] <= 100000 and 0 <= nums[1] <= 100000. -/
theorem spec_14 (nums : Slice I64)
    (hn2 : nums.val.length = 2)
    (h0 : 0 ≤ (nums.val[0]!).val ∧ (nums.val[0]!).val ≤ 100000)
    (h1 : 0 ≤ (nums.val[1]!).val ∧ (nums.val[1]!).val ≤ 100000) :
    ∀ r : I64, min_deletion nums = ok r →
      (nums.val[0]! ≠ nums.val[1]! → r.val = 0) ∧
        (nums.val[0]! = nums.val[1]! → r.val = 2) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64)
    (hn2 : nums.val.length = 2)
    (h0 : 0 ≤ (nums.val[0]!).val ∧ (nums.val[0]!).val ≤ 100000)
    (h1 : 0 ≤ (nums.val[1]!).val ∧ (nums.val[1]!).val ≤ 100000), ∀ r : I64, min_deletion nums = ok r →
      (nums.val[0]! ≠ nums.val[1]! → r.val = 0) ∧
        (nums.val[0]! = nums.val[1]! → r.val = 2)) := by
  sorry

end AegisSpec.MinDeletion
