import Aegis.MinIncrementOperations.Code.Funs

/-!
# Specifications of `Aegis.MinIncrementOperations.min_increment_operations`

LeetCode problem `minimum-increment-operations-to-make-array-beautiful`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinIncrementOperations (min_increment_operations)

namespace AegisSpec.MinIncrementOperations

def ints (a : Slice Std.I64) : List ℤ := a.val.map IScalar.val

def lval (b : List ℤ) (i : ℕ) : ℤ := b.getD i 0

def raiseCost (x k : ℤ) : ℤ := max 0 (k - x)

def max3 (a b c : ℤ) : ℤ := max a (max b c)

def listMax (b : List ℤ) : ℤ := b.foldr max 0

def Between (xs b : List ℤ) (k : ℤ) : Prop :=
  b.length = xs.length ∧
    ∀ i, i < b.length → lval xs i ≤ lval b i ∧ lval b i ≤ max (lval xs i) k

def Beautiful (b : List ℤ) (k : ℤ) : Prop :=
  ∀ l hi, l ≤ hi → hi < b.length → 3 ≤ hi - l + 1 → ∃ t, l ≤ t ∧ t ≤ hi ∧ k ≤ lval b t

def WindowOK (b : List ℤ) (k : ℤ) : Prop :=
  ∀ i, i + 2 < b.length → k ≤ max3 (lval b i) (lval b (i + 1)) (lval b (i + 2))

def totalInc (xs b : List ℤ) : ℤ := ∑ i ∈ Finset.range xs.length, (lval b i - lval xs i)

def fullCost (xs : List ℤ) (k : ℤ) : ℤ := ∑ i ∈ Finset.range xs.length, raiseCost (lval xs i) k

def residueCost (xs : List ℤ) (k : ℤ) (c : ℕ) : ℤ :=
  ∑ i ∈ (Finset.range xs.length).filter (fun i => i % 3 = c), raiseCost (lval xs i) k

def Hitting (xs : List ℤ) (s : Finset ℕ) : Prop :=
  ∀ i, i + 2 < xs.length → i ∈ s ∨ i + 1 ∈ s ∨ i + 2 ∈ s

def selectedCost (xs : List ℤ) (k : ℤ) (s : Finset ℕ) : ℤ :=
  ∑ i ∈ s, raiseCost (lval xs i) k

def ceilDiv3 (m : ℕ) : ℕ := (m + 2) / 3

theorem ceilDiv3_isLeast (m : ℕ) :
    3 * ceilDiv3 m ≥ m ∧ ∀ t : ℕ, 3 * t ≥ m → ceilDiv3 m ≤ t := by
  refine ⟨?_, ?_⟩
  · unfold ceilDiv3
    have h1 := Nat.div_add_mod (m + 2) 3
    have h2 := Nat.mod_lt (m + 2) (by norm_num : 0 < 3)
    omega
  · intro t ht
    unfold ceilDiv3
    rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 3)]
    omega

/-- The function returns a result r, and r is the minimum total number of unit increment operations needed to turn nums into an array b of length n such that every contiguous subarray of b of length at least 3 has maximum at least k. Formally, r is the least integer m for which there exists an integer array b of length n with: (1) nums[i] <= b[i] <= max(nums[i], k) for every i with 0 <= i < n; (2) for every l and hi with 0 <= l <= hi < n and hi - l + 1 >= 3, max_{l <= t <= hi} b[t] >= k; and (3) m = sum_{i=0}^{n-1} (b[i] - nums[i]).
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∃ r, min_increment_operations nums k = ok r ∧
      (∃ b : List ℤ, Between (ints nums) b k.val ∧ Beautiful b k.val ∧
        totalInc (ints nums) b = r.val) ∧
      (∀ b : List ℤ, Between (ints nums) b k.val → Beautiful b k.val →
        r.val ≤ totalInc (ints nums) b) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∃ r, min_increment_operations nums k = ok r ∧
      (∃ b : List ℤ, Between (ints nums) b k.val ∧ Beautiful b k.val ∧
        totalInc (ints nums) b = r.val) ∧
      (∀ b : List ℤ, Between (ints nums) b k.val → Beautiful b k.val →
        r.val ≤ totalInc (ints nums) b)) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic occurs).
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∃ r, min_increment_operations nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∃ r, min_increment_operations nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= sum_{i=0}^{n-1} max(0, k - nums[i]).
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r, min_increment_operations nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ fullCost (ints nums) k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r, min_increment_operations nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ fullCost (ints nums) k.val) := by
  sorry

/-- Whenever the function returns a result r, r <= min( sum_{0 <= i < n, i mod 3 = 0} max(0, k - nums[i]), sum_{0 <= i < n, i mod 3 = 1} max(0, k - nums[i]), sum_{0 <= i < n, i mod 3 = 2} max(0, k - nums[i]) ).
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r, min_increment_operations nums k = ok r →
      r.val ≤ min (min (residueCost (ints nums) k.val 0) (residueCost (ints nums) k.val 1))
        (residueCost (ints nums) k.val 2) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r, min_increment_operations nums k = ok r →
      r.val ≤ min (min (residueCost (ints nums) k.val 0) (residueCost (ints nums) k.val 1))
        (residueCost (ints nums) k.val 2)) := by
  sorry

/-- Whenever the function returns a result r, r >= max(0, k - max_{0 <= i < n} nums[i]).
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r, min_increment_operations nums k = ok r →
      max 0 (k.val - listMax (ints nums)) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r, min_increment_operations nums k = ok r →
      max 0 (k.val - listMax (ints nums)) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer array b of length n such that nums[i] <= b[i] <= max(nums[i], k) for every i with 0 <= i < n, every contiguous subarray of b of length at least 3 has maximum at least k, and sum_{i=0}^{n-1} (b[i] - nums[i]) = r.
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r, min_increment_operations nums k = ok r →
      ∃ b : List ℤ, Between (ints nums) b k.val ∧ Beautiful b k.val ∧
        totalInc (ints nums) b = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r, min_increment_operations nums k = ok r →
      ∃ b : List ℤ, Between (ints nums) b k.val ∧ Beautiful b k.val ∧
        totalInc (ints nums) b = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer array b of length n satisfying nums[i] <= b[i] <= max(nums[i], k) for every i with 0 <= i < n and every contiguous subarray of b of length at least 3 has maximum at least k, it holds that sum_{i=0}^{n-1} (b[i] - nums[i]) >= r.
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r, min_increment_operations nums k = ok r →
      ∀ b : List ℤ, Between (ints nums) b k.val → Beautiful b k.val →
        r.val ≤ totalInc (ints nums) b := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r, min_increment_operations nums k = ok r →
      ∀ b : List ℤ, Between (ints nums) b k.val → Beautiful b k.val →
        r.val ≤ totalInc (ints nums) b) := by
  sorry

/-- Whenever the function returns a result r, r equals the minimum, over all subsets S of {0,1,...,n-1} such that for every i with 0 <= i <= n-3 the intersection S ∩ {i, i+1, i+2} is nonempty, of the sum_{j in S} max(0, k - nums[j]).
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r, min_increment_operations nums k = ok r →
      (∃ s : Finset ℕ, s ⊆ Finset.range (ints nums).length ∧ Hitting (ints nums) s ∧
        selectedCost (ints nums) k.val s = r.val) ∧
      (∀ s : Finset ℕ, s ⊆ Finset.range (ints nums).length → Hitting (ints nums) s →
        r.val ≤ selectedCost (ints nums) k.val s) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r, min_increment_operations nums k = ok r →
      (∃ s : Finset ℕ, s ⊆ Finset.range (ints nums).length ∧ Hitting (ints nums) s ∧
        selectedCost (ints nums) k.val s = r.val) ∧
      (∀ s : Finset ℕ, s ⊆ Finset.range (ints nums).length → Hitting (ints nums) s →
        r.val ≤ selectedCost (ints nums) k.val s)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i <= n-3, max(nums[i], nums[i+1], nums[i+2]) >= k.
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r, min_increment_operations nums k = ok r →
      (r.val = 0 ↔ WindowOK (ints nums) k.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r, min_increment_operations nums k = ok r →
      (r.val = 0 ↔ WindowOK (ints nums) k.val)) := by
  sorry

/-- Whenever the function returns a result r, r = max(0, k - max(nums[0], nums[1], nums[2])).
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, n = 3, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hn : nums.val.length = 3)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r, min_increment_operations nums k = ok r →
      r.val = max 0 (k.val - max3 (lval (ints nums) 0) (lval (ints nums) 1)
        (lval (ints nums) 2)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : nums.val.length = 3)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r, min_increment_operations nums k = ok r →
      r.val = max 0 (k.val - max3 (lval (ints nums) 0) (lval (ints nums) 1)
        (lval (ints nums) 2))) := by
  sorry

/-- Whenever the function returns a result r, r = k * ceil((n - 2) / 3), where ceil((n - 2) / 3) is the smallest integer s with 3s >= n - 2.
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, nums[i] = 0 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hzero : ∀ i, i < nums.val.length → lval (ints nums) i = 0)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r, min_increment_operations nums k = ok r →
      r.val = k.val * (ceilDiv3 (nums.val.length - 2) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hzero : ∀ i, i < nums.val.length → lval (ints nums) i = 0)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r, min_increment_operations nums k = ok r →
      r.val = k.val * (ceilDiv3 (nums.val.length - 2) : ℤ)) := by
  sorry

/-- If the function returns r on (nums, k) and returns r' on (nums', k), then r' <= r.
  Preconditions: Let n with 3 <= n <= 10^5 and k with 0 <= k <= 10^9 be fixed. Let nums and nums' be two slices of 64-bit signed integers, both of length n, satisfying 0 <= nums[i] <= 10^9 and 0 <= nums'[i] <= 10^9 for every i with 0 <= i < n, and nums[i] <= nums'[i] for every i with 0 <= i < n. -/
theorem spec_12 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlen : nums'.val.length = nums.val.length)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hlo' : ∀ i, i < nums'.val.length → 0 ≤ lval (ints nums') i)
    (hhi' : ∀ i, i < nums'.val.length → lval (ints nums') i ≤ 10 ^ 9)
    (hle : ∀ i, i < nums.val.length → lval (ints nums) i ≤ lval (ints nums') i)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r r', min_increment_operations nums k = ok r →
      min_increment_operations nums' k = ok r' → r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlen : nums'.val.length = nums.val.length)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hlo' : ∀ i, i < nums'.val.length → 0 ≤ lval (ints nums') i)
    (hhi' : ∀ i, i < nums'.val.length → lval (ints nums') i ≤ 10 ^ 9)
    (hle : ∀ i, i < nums.val.length → lval (ints nums) i ≤ lval (ints nums') i)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r r', min_increment_operations nums k = ok r →
      min_increment_operations nums' k = ok r' → r'.val ≤ r.val) := by
  sorry

/-- If the function returns r on (nums, k) and returns r' on (nums', k), then r' = r.
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. Fix an index p with 0 <= p < n and nums[p] >= k. Let v be an integer with k <= v <= 10^9, and let nums' be the array obtained from nums by replacing nums[p] with v. -/
theorem spec_13 (nums nums' : Slice Std.I64) (k : Std.I64) (p : ℕ) (v : ℤ)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hp : p < nums.val.length)
    (hpk : k.val ≤ lval (ints nums) p)
    (hv : k.val ≤ v) (hvub : v ≤ 10 ^ 9)
    (hlen : nums'.val.length = nums.val.length)
    (hp' : lval (ints nums') p = v)
    (hother : ∀ i, i < nums.val.length → i ≠ p → lval (ints nums') i = lval (ints nums) i)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hlo' : ∀ i, i < nums'.val.length → 0 ≤ lval (ints nums') i)
    (hhi' : ∀ i, i < nums'.val.length → lval (ints nums') i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r r', min_increment_operations nums k = ok r →
      min_increment_operations nums' k = ok r' → r'.val = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (p : ℕ) (v : ℤ)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hp : p < nums.val.length)
    (hpk : k.val ≤ lval (ints nums) p)
    (hv : k.val ≤ v) (hvub : v ≤ 10 ^ 9)
    (hlen : nums'.val.length = nums.val.length)
    (hp' : lval (ints nums') p = v)
    (hother : ∀ i, i < nums.val.length → i ≠ p → lval (ints nums') i = lval (ints nums) i)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hlo' : ∀ i, i < nums'.val.length → 0 ≤ lval (ints nums') i)
    (hhi' : ∀ i, i < nums'.val.length → lval (ints nums') i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r r', min_increment_operations nums k = ok r →
      min_increment_operations nums' k = ok r' → r'.val = r.val) := by
  sorry

/-- If the function returns r1 on (nums, k1) and returns r2 on (nums, k2), then r1 <= r2.
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n. Let k1 and k2 be integers with 0 <= k1 <= k2 <= 10^9. -/
theorem spec_14 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk1 : 0 ≤ k1.val) (hk1ub : k1.val ≤ 10 ^ 9)
    (hk2 : 0 ≤ k2.val) (hk2ub : k2.val ≤ 10 ^ 9)
    (hkk : k1.val ≤ k2.val) :
    ∀ r1 r2, min_increment_operations nums k1 = ok r1 →
      min_increment_operations nums k2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk1 : 0 ≤ k1.val) (hk1ub : k1.val ≤ 10 ^ 9)
    (hk2 : 0 ≤ k2.val) (hk2ub : k2.val ≤ 10 ^ 9)
    (hkk : k1.val ≤ k2.val), ∀ r1 r2, min_increment_operations nums k1 = ok r1 →
      min_increment_operations nums k2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer array b of length n such that: (1) for every i with 0 <= i < n, b[i] = nums[i] or b[i] = max(nums[i], k); (2) every contiguous subarray of b of length at least 3 has maximum at least k; and (3) sum_{i=0}^{n-1} (b[i] - nums[i]) = r.
  Preconditions: Let n = len(nums). nums is a 0-indexed slice of 64-bit signed integers, 3 <= n <= 10^5, 0 <= nums[i] <= 10^9 for every i with 0 <= i < n, and 0 <= k <= 10^9. -/
theorem spec_15 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9) :
    ∀ r, min_increment_operations nums k = ok r →
      ∃ b : List ℤ, b.length = nums.val.length ∧
        (∀ i, i < nums.val.length →
          lval b i = lval (ints nums) i ∨ lval b i = max (lval (ints nums) i) k.val) ∧
        Beautiful b k.val ∧ totalInc (ints nums) b = r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 3 ≤ nums.val.length) (hnub : nums.val.length ≤ 10 ^ 5)
    (hlo : ∀ i, i < nums.val.length → 0 ≤ lval (ints nums) i)
    (hhi : ∀ i, i < nums.val.length → lval (ints nums) i ≤ 10 ^ 9)
    (hk : 0 ≤ k.val) (hkub : k.val ≤ 10 ^ 9), ∀ r, min_increment_operations nums k = ok r →
      ∃ b : List ℤ, b.length = nums.val.length ∧
        (∀ i, i < nums.val.length →
          lval b i = lval (ints nums) i ∨ lval b i = max (lval (ints nums) i) k.val) ∧
        Beautiful b k.val ∧ totalInc (ints nums) b = r.val) := by
  sorry

end AegisSpec.MinIncrementOperations
