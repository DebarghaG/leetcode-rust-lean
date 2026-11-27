import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-subarray-elements-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.MinOperations

namespace AegisSpec.MinOperations

def nth (nums : Slice Std.I64) (i : ℕ) : ℤ := (nums.val[i]!).val

def winSize (k : Std.I64) : ℕ := k.val.toNat

def IsMinOf (S : Set ℤ) (m : ℤ) : Prop := m ∈ S ∧ ∀ v ∈ S, m ≤ v

def windowCost (nums : Slice Std.I64) (s k : ℕ) (t : ℤ) : ℤ :=
  ∑ j ∈ Finset.range k, |nth nums (s + j) - t|

def windowCosts (nums : Slice Std.I64) (s k : ℕ) : Set ℤ :=
  {v : ℤ | ∃ t : ℤ, v = windowCost nums s k t}

def allWindowCosts (nums : Slice Std.I64) (k : ℕ) : Set ℤ :=
  {v : ℤ | ∃ (s : ℕ) (t : ℤ), s + k ≤ nums.val.length ∧ v = windowCost nums s k t}

def revWindowCost (nums : Slice Std.I64) (s k : ℕ) (t : ℤ) : ℤ :=
  ∑ j ∈ Finset.range k, |nth nums (nums.val.length - 1 - (s + j)) - t|

def revWindowCosts (nums : Slice Std.I64) (k : ℕ) : Set ℤ :=
  {v : ℤ | ∃ (s : ℕ) (t : ℤ), s + k ≤ nums.val.length ∧ v = revWindowCost nums s k t}

def shiftedWindowCost (nums : Slice Std.I64) (s k : ℕ) (c t : ℤ) : ℤ :=
  ∑ j ∈ Finset.range k, |(nth nums (s + j) + c) - t|

def shiftedWindowCosts (nums : Slice Std.I64) (k : ℕ) (c : ℤ) : Set ℤ :=
  {v : ℤ | ∃ (s : ℕ) (t : ℤ), s + k ≤ nums.val.length ∧ v = shiftedWindowCost nums s k c t}

def totalCost (nums : Slice Std.I64) (t : ℤ) : ℤ :=
  ∑ i ∈ Finset.range nums.val.length, |nth nums i - t|

def totalCosts (nums : Slice Std.I64) : Set ℤ :=
  {v : ℤ | ∃ t : ℤ, v = totalCost nums t}

def pairCosts (nums : Slice Std.I64) : Set ℤ :=
  {v : ℤ | ∃ i : ℕ, i + 1 < nums.val.length ∧ v = |nth nums (i + 1) - nth nums i|}

def IsMedian (nums : Slice Std.I64) (s k : ℕ) (m : ℤ) : Prop :=
  ((Finset.range k).filter (fun j => nth nums (s + j) < m)).card ≤ k / 2 ∧
  ((Finset.range k).filter (fun j => m < nth nums (s + j))).card ≤ k / 2

def medianCosts (nums : Slice Std.I64) (k : ℕ) : Set ℤ :=
  {v : ℤ | ∃ (s : ℕ) (m : ℤ), s + k ≤ nums.val.length ∧ IsMedian nums s k m ∧
    v = windowCost nums s k m}

/-- The function returns a result r and r = min { sum_{j=0}^{k-1} |nums[s+j] - t| : 0 <= s <= n-k and t is an integer }.
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, 2 <= k <= n, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. All integers, absolute values, and sums in the statement are mathematical integers, not machine-wrapped values. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r ∧
      IsMinOf (allWindowCosts nums (winSize k)) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r ∧
      IsMinOf (allWindowCosts nums (winSize k)) r.val) := by
  sorry

/-- The function does not fail: for every input satisfying the preconditions it returns a result r.
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, 2 <= k <= n, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, 2 <= k <= n, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. All integers, absolute values, and sums in the statement are mathematical integers. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and for every integer s with 0 <= s <= n-k and every integer t, r <= sum_{j=0}^{k-1} |nums[s+j] - t|.
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, 2 <= k <= n, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. All integers, absolute values, and sums in the statement are mathematical integers. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r ∧
      ∀ (s : ℕ) (t : ℤ), s + winSize k ≤ nums.val.length →
        r.val ≤ windowCost nums s (winSize k) t := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r ∧
      ∀ (s : ℕ) (t : ℤ), s + winSize k ≤ nums.val.length →
        r.val ≤ windowCost nums s (winSize k) t) := by
  sorry

/-- The function returns a result r and there exists an integer s with 0 <= s <= n-k such that r = min { sum_{j=0}^{k-1} |nums[s+j] - t| : t is an integer }.
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, 2 <= k <= n, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. All integers, absolute values, and sums in the statement are mathematical integers. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r ∧
      ∃ s : ℕ, s + winSize k ≤ nums.val.length ∧
        IsMinOf (windowCosts nums s (winSize k)) r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r ∧
      ∃ s : ℕ, s + winSize k ≤ nums.val.length ∧
        IsMinOf (windowCosts nums s (winSize k)) r.val) := by
  sorry

/-- The function returns a result r and r = 0 if and only if there exists an integer s with 0 <= s <= n-k such that nums[s] = nums[s+1] = ... = nums[s+k-1].
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, 2 <= k <= n, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r ∧
      (r.val = 0 ↔ ∃ s : ℕ, s + winSize k ≤ nums.val.length ∧
        ∀ j : ℕ, j < winSize k → nth nums (s + j) = nth nums s) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r ∧
      (r.val = 0 ↔ ∃ s : ℕ, s + winSize k ≤ nums.val.length ∧
        ∀ j : ℕ, j < winSize k → nth nums (s + j) = nth nums s)) := by
  sorry

/-- The function returns a result r and r = min { |nums[i] - nums[i+1]| : 0 <= i <= n-2 }.
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, k = 2, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. All integers and absolute values in the statement are mathematical integers. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk : k.val = 2)
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r ∧ IsMinOf (pairCosts nums) r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk : k.val = 2)
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r ∧ IsMinOf (pairCosts nums) r.val) := by
  sorry

/-- The function returns a result r and r <= (k-1)*2000000.
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, 2 <= k <= n, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. All integers, absolute values, and sums in the statement are mathematical integers. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r ∧ r.val ≤ (k.val - 1) * 2000000 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r ∧ r.val ≤ (k.val - 1) * 2000000) := by
  sorry

/-- The function returns a result r and r <= min { sum_{i=0}^{n-1} |nums[i] - t| : t is an integer }.
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, 2 <= k <= n, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. All integers, absolute values, and sums in the statement are mathematical integers. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r ∧
      ∃ m : ℤ, IsMinOf (totalCosts nums) m ∧ r.val ≤ m := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r ∧
      ∃ m : ℤ, IsMinOf (totalCosts nums) m ∧ r.val ≤ m) := by
  sorry

/-- The function returns a result r and r = min { sum_{j=0}^{k-1} |nums[n-1-(s+j)] - t| : 0 <= s <= n-k and t is an integer }.
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, 2 <= k <= n, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. All integers, absolute values, and sums in the statement are mathematical integers. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r ∧
      IsMinOf (revWindowCosts nums (winSize k)) r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r ∧
      IsMinOf (revWindowCosts nums (winSize k)) r.val) := by
  sorry

/-- For every integer c, the function returns a result r and r = min { sum_{j=0}^{k-1} |(nums[s+j] + c) - t| : 0 <= s <= n-k and t is an integer }.
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, 2 <= k <= n, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. All integers, absolute values, and sums in the statement are mathematical integers. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r ∧
      ∀ c : ℤ, IsMinOf (shiftedWindowCosts nums (winSize k) c) r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r ∧
      ∀ c : ℤ, IsMinOf (shiftedWindowCosts nums (winSize k) c) r.val) := by
  sorry

/-- The function returns a result r and for every integer s with 0 <= s <= n-k, if m_s is any median of the multiset { nums[s+j] : 0 <= j < k }, then sum_{j=0}^{k-1} |nums[s+j] - m_s| = min { sum_{j=0}^{k-1} |nums[s+j] - t| : t is an integer }; consequently r = min { sum_{j=0}^{k-1} |nums[s+j] - m_s| : 0 <= s <= n-k }.
  Preconditions: Let n = len(nums). The input satisfies 2 <= n <= 100000, 2 <= k <= n, and for every i with 0 <= i < n, -1000000 <= nums[i] <= 1000000. All integers, absolute values, and sums in the statement are mathematical integers. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums k = ok r ∧
      (∀ (s : ℕ) (m : ℤ), s + winSize k ≤ nums.val.length →
        IsMedian nums s (winSize k) m →
        IsMinOf (windowCosts nums s (winSize k)) (windowCost nums s (winSize k) m)) ∧
      IsMinOf (medianCosts nums (winSize k)) r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hbounds : ∀ i : ℕ, i < nums.val.length →
      -1000000 ≤ nth nums i ∧ nth nums i ≤ 1000000), ∃ r : Std.I64, min_operations nums k = ok r ∧
      (∀ (s : ℕ) (m : ℤ), s + winSize k ≤ nums.val.length →
        IsMedian nums s (winSize k) m →
        IsMinOf (windowCosts nums s (winSize k)) (windowCost nums s (winSize k) m)) ∧
      IsMinOf (medianCosts nums (winSize k)) r.val) := by
  sorry

end AegisSpec.MinOperations
