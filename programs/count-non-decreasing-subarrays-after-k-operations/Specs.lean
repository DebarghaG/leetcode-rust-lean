import Aegis.CountNonDecreasingSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountNonDecreasingSubarrays.count_non_decreasing_subarrays`

LeetCode problem `count-non-decreasing-subarrays-after-k-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountNonDecreasingSubarrays

open Aegis.CountNonDecreasingSubarrays

def entry (nums : Slice Std.I64) (i : ℕ) : ℤ := (nums.val[i]!).val

def maxOn (a : ℕ → ℤ) (l : ℕ) : ℕ → ℤ
  | 0 => a l
  | k + 1 => max (maxOn a l k) (a (l + k + 1))

theorem le_maxOn (a : ℕ → ℤ) (l : ℕ) :
    ∀ k j, j ≤ k → a (l + j) ≤ maxOn a l k := by
  intro k
  induction k with
  | zero =>
    intro j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    simp [maxOn]
  | succ k ih =>
    intro j hj
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact le_trans (ih j (Nat.lt_succ_iff.mp hlt)) (le_max_left _ _)
    · have hjk : j = k + 1 := Nat.le_antisymm hj hge
      subst hjk
      exact le_trans (le_max_right (maxOn a l k) (a (l + k + 1))) (le_refl _)

theorem maxOn_achieved (a : ℕ → ℤ) (l : ℕ) :
    ∀ k, ∃ j, j ≤ k ∧ maxOn a l k = a (l + j) := by
  intro k
  induction k with
  | zero => exact ⟨0, le_rfl, by simp [maxOn]⟩
  | succ k ih =>
    by_cases h : maxOn a l k ≤ a (l + k + 1)
    · refine ⟨k + 1, le_rfl, ?_⟩
      rw [maxOn, max_eq_right h]
      congr 1
    · obtain ⟨j, hj, he⟩ := ih
      exact ⟨j, Nat.le_succ_of_le hj, by rw [maxOn, max_eq_left (le_of_not_ge h), ← he]⟩

def cost (a : ℕ → ℤ) (l u : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc l u, (maxOn a l (i - l) - a i)

def totalCost (a : ℕ → ℤ) (n : ℕ) : ℤ := cost a 0 (n - 1)

def pairs (n : ℕ) : Finset (ℕ × ℕ) := (Finset.range n).product (Finset.range n)

def countPairs (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P] : ℕ :=
  ((pairs n).filter (fun p => p.1 ≤ p.2 ∧ P p.1 p.2)).card

def countStep (a : ℕ → ℤ) (k : ℤ) (n : ℕ) : ℕ :=
  ((Finset.range (n - 1)).filter (fun i => a i ≤ a (i + 1) + k)).card

def IsNondecWindow (a : ℕ → ℤ) (l u : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc l u, i < u → a i ≤ a (i + 1)

instance instDecidableIsNondecWindow (a : ℕ → ℤ) :
    DecidableRel (fun l u => IsNondecWindow a l u) :=
  fun l u => by
  unfold IsNondecWindow
  infer_instance

theorem isNondecWindow_iff (a : ℕ → ℤ) (l u : ℕ) :
    IsNondecWindow a l u ↔ ∀ i, l ≤ i → i < u → a i ≤ a (i + 1) := by
  constructor
  · intro h i hli hiu
    exact h i (Finset.mem_Icc.mpr ⟨hli, le_of_lt hiu⟩) hiu
  · intro h i hi hiu
    exact h i (Finset.mem_Icc.mp hi).1 hiu

/-- The function returns a result res and res = #{(l,u) | 0 <= l <= u < n and C(l,u) <= k}, where n = len(nums) and C(l,u) = sum_{i=l}^{u} (max{nums[j] | l <= j <= i} - nums[i]).
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000) :
    ∃ r : Std.I64,
      count_non_decreasing_subarrays nums k = ok r ∧
        r.val = (countPairs n (fun l u => cost (entry nums) l u ≤ k.val) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000), ∃ r : Std.I64,
      count_non_decreasing_subarrays nums k = ok r ∧
        r.val = (countPairs n (fun l u => cost (entry nums) l u ≤ k.val) : ℤ)) := by
  sorry

/-- For every nums and k satisfying the preconditions, the function returns a result res; it does not fail.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000) :
    ∃ r : Std.I64, count_non_decreasing_subarrays nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000), ∃ r : Std.I64, count_non_decreasing_subarrays nums k = ok r) := by
  sorry

/-- Whenever the function returns a result res, res <= n*(n+1)/2, where n = len(nums).
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r) :
    r.val ≤ ((n * (n + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r), r.val ≤ ((n * (n + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result res, res >= D, where n = len(nums) and D = #{(l,u) | 0 <= l <= u < n and for every i with l <= i < u, nums[i] <= nums[i+1]}.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r) :
    (countPairs n (fun l u => IsNondecWindow (entry nums) l u) : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r), (countPairs n (fun l u => IsNondecWindow (entry nums) l u) : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result res, res >= n + L, where n = len(nums) and L = #{i | 0 <= i < n-1 and nums[i] <= nums[i+1] + k}.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r) :
    (n : ℤ) + (countStep (entry nums) k.val n : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r), (n : ℤ) + (countStep (entry nums) k.val n : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result res, if k < T then res < n*(n+1)/2, where n = len(nums) and T = C(0,n-1) = sum_{i=0}^{n-1} (max{nums[j] | 0 <= j <= i} - nums[i]).
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r)
    (hkT : k.val < totalCost (entry nums) n) :
    r.val < ((n * (n + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r)
    (hkT : k.val < totalCost (entry nums) n), r.val < ((n * (n + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result res, if k >= T then res = n*(n+1)/2, where n = len(nums) and T = C(0,n-1) = sum_{i=0}^{n-1} (max{nums[j] | 0 <= j <= i} - nums[i]).
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r)
    (hTk : totalCost (entry nums) n ≤ k.val) :
    r.val = ((n * (n + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r)
    (hTk : totalCost (entry nums) n ≤ k.val), r.val = ((n * (n + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result res, if for every i with 0 <= i < n-1 we have nums[i] > nums[i+1] + k, then res = n, where n = len(nums).
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r)
    (hdec : ∀ i, i < n - 1 → entry nums (i + 1) + k.val < entry nums i) :
    r.val = (n : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r)
    (hdec : ∀ i, i < n - 1 → entry nums (i + 1) + k.val < entry nums i), r.val = (n : ℤ)) := by
  sorry

/-- Whenever the function returns a result res for (nums,k), for every integer k' with k <= k' <= 1000000000, if the function returns res' for (nums,k'), then res <= res'.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r) :
    ∀ (k' : Std.I64), k.val ≤ k'.val → k'.val ≤ 1000000000 →
      ∀ (r' : Std.I64), count_non_decreasing_subarrays nums k' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r), ∀ (k' : Std.I64), k.val ≤ k'.val → k'.val ≤ 1000000000 →
      ∀ (r' : Std.I64), count_non_decreasing_subarrays nums k' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns a result res for (nums,k), for every integer c and every slice nums' of length n with nums'[i] = nums[i] + c for every i with 0 <= i < n and 1 <= nums'[i] <= 1000000000 for every i, if the function returns res' for (nums',k), then res' = res.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r) :
    ∀ (c : ℤ) (nums' : Slice Std.I64), nums'.val.length = n →
      (∀ i, i < n → entry nums' i = entry nums i + c) →
        (∀ i, i < n → 1 ≤ entry nums' i) →
          (∀ i, i < n → entry nums' i ≤ 1000000000) →
            ∀ (r' : Std.I64), count_non_decreasing_subarrays nums' k = ok r' →
              r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hval_lo : ∀ i, i < n → 1 ≤ entry nums i)
    (hval_hi : ∀ i, i < n → entry nums i ≤ 1000000000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (r : Std.I64) (hr : count_non_decreasing_subarrays nums k = ok r), ∀ (c : ℤ) (nums' : Slice Std.I64), nums'.val.length = n →
      (∀ i, i < n → entry nums' i = entry nums i + c) →
        (∀ i, i < n → 1 ≤ entry nums' i) →
          (∀ i, i < n → entry nums' i ≤ 1000000000) →
            ∀ (r' : Std.I64), count_non_decreasing_subarrays nums' k = ok r' →
              r'.val = r.val) := by
  sorry

end AegisSpec.CountNonDecreasingSubarrays
