import Aegis.ArrayNesting.Code.Funs

/-!
# Specifications of `Aegis.ArrayNesting.array_nesting`

LeetCode problem `array-nesting`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ArrayNesting

def numsList (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def nlen (nums : Slice Std.I64) : ℕ := (Slice.len nums).val

def get (nums : Slice Std.I64) (i : ℕ) : ℤ := (numsList nums).getD i 0

def iter (nums : Slice Std.I64) : ℕ → ℕ → ℤ
  | 0, k => (k : ℤ)
  | t + 1, k => get nums (Int.toNat (iter nums t k))

noncomputable def cycleLen (nums : Slice Std.I64) (k : ℕ) : ℕ :=
  sInf {t : ℕ | 0 < t ∧ iter nums t k = (k : ℤ)}

noncomputable def maxCycleLen (nums : Slice Std.I64) : ℕ :=
  ((List.range (nlen nums)).map (fun k => cycleLen nums k)).foldr max 0

noncomputable def inv (nums : Slice Std.I64) (j : ℕ) : ℕ :=
  sInf {i : ℕ | i < nlen nums ∧ get nums i = (j : ℤ)}

noncomputable def iterInv (nums : Slice Std.I64) : ℕ → ℕ → ℤ
  | 0, k => (k : ℤ)
  | t + 1, k => (inv nums (Int.toNat (iterInv nums t k)) : ℤ)

noncomputable def invCycleLen (nums : Slice Std.I64) (j : ℕ) : ℕ :=
  sInf {t : ℕ | 0 < t ∧ iterInv nums t j = (j : ℤ)}

noncomputable def maxInvCycleLen (nums : Slice Std.I64) : ℕ :=
  ((List.range (nlen nums)).map (fun j => invCycleLen nums j)).foldr max 0

def isIdentity (nums : Slice Std.I64) : Prop := ∀ i, i < nlen nums → get nums i = (i : ℤ)

def cycleElemsNodup (nums : Slice Std.I64) (k : ℕ) : Prop :=
  ((List.range (cycleLen nums k)).map (fun t => iter nums (t + 1) k)).Nodup

/-- Let n = len(nums). For k with 0 <= k < n, define f^0(k) = k and f^{t+1}(k) = nums[f^t(k)] for every t >= 0. Because the preconditions say nums is a permutation of [0,n-1], for each such k there is a least positive integer L(k) with f^{L(k)}(k) = k. The function returns a result r, and r = max { L(k) | 0 <= k < n }. Equivalently, r is the maximum length of the set s[k] = {nums[k], nums[nums[k]], ...} taken until immediately before the first repeated value occurs; for every k, the number of distinct elements in s[k] is exactly L(k).
  Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] is an integer satisfying 0 <= nums[i] < n. For every i, j with 0 <= i < n and 0 <= j < n, if nums[i] = nums[j] then i = j. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j) :
    ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r ∧
      r.val = (maxCycleLen nums : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j), ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r ∧
      r.val = (maxCycleLen nums : ℤ)) := by
  sorry

/-- The function returns a result r and does not fail: it does not panic, does not access nums out of bounds, and does not overflow a 64-bit integer.
  Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] is an integer satisfying 0 <= nums[i] < n. For every i, j with 0 <= i < n and 0 <= j < n, if nums[i] = nums[j] then i = j. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j) :
    ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j), ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] is an integer satisfying 0 <= nums[i] < n. For every i, j with 0 <= i < n and 0 <= j < n, if nums[i] = nums[j] then i = j. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j) :
    ∀ r, Aegis.ArrayNesting.array_nesting nums = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j), ∀ r, Aegis.ArrayNesting.array_nesting nums = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= len(nums).
  Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] is an integer satisfying 0 <= nums[i] < n. For every i, j with 0 <= i < n and 0 <= j < n, if nums[i] = nums[j] then i = j. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j) :
    ∀ r, Aegis.ArrayNesting.array_nesting nums = ok r → r.val ≤ (nlen nums : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j), ∀ r, Aegis.ArrayNesting.array_nesting nums = ok r → r.val ≤ (nlen nums : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < n, L(k) <= r, where L(k) is the least positive integer t such that f^t(k) = k, with f^0(k) = k and f^{t+1}(k) = nums[f^t(k)].
  Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] is an integer satisfying 0 <= nums[i] < n. For every i, j with 0 <= i < n and 0 <= j < n, if nums[i] = nums[j] then i = j. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j) :
    ∀ r, Aegis.ArrayNesting.array_nesting nums = ok r →
      ∀ k, k < nlen nums → (cycleLen nums k : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j), ∀ r, Aegis.ArrayNesting.array_nesting nums = ok r →
      ∀ k, k < nlen nums → (cycleLen nums k : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an index k with 0 <= k < n such that L(k) = r, where L(k) is the least positive integer t such that f^t(k) = k, with f^0(k) = k and f^{t+1}(k) = nums[f^t(k)]. Equivalently, some set s[k] has length exactly r.
  Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] is an integer satisfying 0 <= nums[i] < n. For every i, j with 0 <= i < n and 0 <= j < n, if nums[i] = nums[j] then i = j. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j) :
    ∀ r, Aegis.ArrayNesting.array_nesting nums = ok r →
      ∃ k, k < nlen nums ∧ (cycleLen nums k : ℤ) = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j), ∀ r, Aegis.ArrayNesting.array_nesting nums = ok r →
      ∃ k, k < nlen nums ∧ (cycleLen nums k : ℤ) = r.val) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] is an integer satisfying 0 <= nums[i] < n. For every i, j with 0 <= i < n and 0 <= j < n, if nums[i] = nums[j] then i = j. Additionally, len(nums) = 1. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j)
    (hlen_one : nlen nums = 1) :
    ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r ∧ r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j)
    (hlen_one : nlen nums = 1), ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result r and r = n.
  Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] is an integer satisfying 0 <= nums[i] < n. For every i, j with 0 <= i < n and 0 <= j < n, if nums[i] = nums[j] then i = j. Additionally, the permutation nums consists of exactly one cycle of length n, so repeated application of i -> nums[i] visits all n indices before returning to the starting index. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j)
    (hsingle : ∀ k, k < nlen nums → cycleLen nums k = nlen nums) :
    ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r ∧ r.val = (nlen nums : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j)
    (hsingle : ∀ k, k < nlen nums → cycleLen nums k = nlen nums), ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r ∧ r.val = (nlen nums : ℤ)) := by
  sorry

/-- The function returns a result r and r >= 2.
  Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] is an integer satisfying 0 <= nums[i] < n. For every i, j with 0 <= i < n and 0 <= j < n, if nums[i] = nums[j] then i = j. Additionally, there exists k with 0 <= k < n and nums[k] != k. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j)
    (hnontrivial : ∃ k, k < nlen nums ∧ get nums k ≠ (k : ℤ)) :
    ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r ∧ 2 ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j)
    (hnontrivial : ∃ k, k < nlen nums ∧ get nums k ≠ (k : ℤ)), ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r ∧ 2 ≤ r.val) := by
  sorry

/-- Let inv be the inverse permutation of nums, so for every j with 0 <= j < n, inv[j] is the unique i with nums[i] = j. Whenever the function returns r for nums, the maximum cycle length of inv (the maximum over j of the least positive t with inv^t(j) = j) is also r.
  Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] is an integer satisfying 0 <= nums[i] < n. For every i, j with 0 <= i < n and 0 <= j < n, if nums[i] = nums[j] then i = j. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j) :
    ∀ r, Aegis.ArrayNesting.array_nesting nums = ok r →
      (maxInvCycleLen nums : ℤ) = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j), ∀ r, Aegis.ArrayNesting.array_nesting nums = ok r →
      (maxInvCycleLen nums : ℤ) = r.val) := by
  sorry

/-- The function returns a result r; if nums[i] = i for every i with 0 <= i < n then r = 1, and otherwise r = 2.
  Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] is an integer satisfying 0 <= nums[i] < n. For every i, j with 0 <= i < n and 0 <= j < n, if nums[i] = nums[j] then i = j. Additionally, nums[nums[i]] = i for every i with 0 <= i < n. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j)
    (hinvol : ∀ i, i < nlen nums → get nums (Int.toNat (get nums i)) = (i : ℤ)) :
    ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r ∧
      (isIdentity nums → r.val = 1) ∧ (¬ isIdentity nums → r.val = 2) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nlen nums)
    (hlen_le : nlen nums ≤ 100000)
    (hrange : ∀ i, i < nlen nums → 0 ≤ get nums i ∧ get nums i < (nlen nums : ℤ))
    (hinj : ∀ i j, i < nlen nums → j < nlen nums → get nums i = get nums j → i = j)
    (hinvol : ∀ i, i < nlen nums → get nums (Int.toNat (get nums i)) = (i : ℤ)), ∃ r, Aegis.ArrayNesting.array_nesting nums = ok r ∧
      (isIdentity nums → r.val = 1) ∧ (¬ isIdentity nums → r.val = 2)) := by
  sorry

end AegisSpec.ArrayNesting
