import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `maximum-array-hopping-score-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxScore

open Aegis.MaxScore

def len (nums : Slice Std.I64) : Nat := nums.val.length

def elem (nums : Slice Std.I64) (i : Nat) : Int :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def hops (p : List Nat) : List (Nat × Nat) := p.zip p.tail

def score (f : Nat → Int) (p : List Nat) : Int :=
  ((hops p).map (fun q => ((q.2 : Int) - (q.1 : Int)) * f q.2)).sum

def IsHopPath (n : Nat) (p : List Nat) : Prop :=
  2 ≤ p.length ∧ p.head? = some 0 ∧ p.getLast? = some (n - 1) ∧
    (hops p).Forall (fun q => q.1 < q.2)

def tailSum (nums : Slice Std.I64) : Int :=
  (((List.range (len nums)).drop 1).map (fun j => elem nums j)).sum

def weightedTailSum (nums : Slice Std.I64) : Int :=
  (((List.range (len nums)).drop 1).map (fun (j : Nat) => (j : Int) * elem nums j)).sum

def maxElem (nums : Slice Std.I64) : Int :=
  (nums.val.map (fun x => x.val)).foldr max 0

/-- The function returns a result r and r equals the maximum, over all valid hopping sequences from index 0 to index len(nums)-1, of the sequence's score. A valid hopping sequence is a sequence of indices p_0, p_1, ..., p_m such that m >= 1, p_0 = 0, p_m = len(nums)-1, and p_t < p_{t+1} for every 0 <= t < m; its score is sum_{t=0}^{m-1} (p_{t+1} - p_t) * nums[p_{t+1}].
  Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000) :
    ∃ r : Std.I64, max_score nums = ok r ∧
      (∀ p : List Nat, IsHopPath (len nums) p → score (elem nums) p ≤ r.val) ∧
      (∃ p : List Nat, IsHopPath (len nums) p ∧ score (elem nums) p = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000), ∃ r : Std.I64, max_score nums = ok r ∧
      (∀ p : List Nat, IsHopPath (len nums) p → score (elem nums) p ≤ r.val) ∧
      (∃ p : List Nat, IsHopPath (len nums) p ∧ score (elem nums) p = r.val)) := by
  sorry

/-- Whenever the function returns a result r, there exists a valid hopping sequence p_0, p_1, ..., p_m from index 0 to index len(nums)-1 (m >= 1, p_0 = 0, p_m = len(nums)-1, p_t < p_{t+1}) whose score sum_{t=0}^{m-1} (p_{t+1} - p_t) * nums[p_{t+1}] equals r.
  Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000) :
    ∀ (r : Std.I64), max_score nums = ok r →
      ∃ p : List Nat, IsHopPath (len nums) p ∧ score (elem nums) p = r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ (r : Std.I64), max_score nums = ok r →
      ∃ p : List Nat, IsHopPath (len nums) p ∧ score (elem nums) p = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every valid hopping sequence p_0, p_1, ..., p_m from index 0 to index len(nums)-1 (m >= 1, p_0 = 0, p_m = len(nums)-1, p_t < p_{t+1}), the sequence's score sum_{t=0}^{m-1} (p_{t+1} - p_t) * nums[p_{t+1}] is at most r.
  Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000) :
    ∀ (r : Std.I64), max_score nums = ok r →
      ∀ p : List Nat, IsHopPath (len nums) p → score (elem nums) p ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ (r : Std.I64), max_score nums = ok r →
      ∀ p : List Nat, IsHopPath (len nums) p → score (elem nums) p ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= (len(nums) - 1) * nums[len(nums)-1].
  Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000) :
    ∀ (r : Std.I64), max_score nums = ok r →
      r.val ≥ ((len nums : Int) - 1) * elem nums (len nums - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ (r : Std.I64), max_score nums = ok r →
      r.val ≥ ((len nums : Int) - 1) * elem nums (len nums - 1)) := by
  sorry

/-- Whenever the function returns a result r, r >= sum_{j=1}^{len(nums)-1} nums[j].
  Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000) :
    ∀ (r : Std.I64), max_score nums = ok r → r.val ≥ tailSum nums := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ (r : Std.I64), max_score nums = ok r → r.val ≥ tailSum nums) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{j=1}^{len(nums)-1} j * nums[j].
  Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000) :
    ∀ (r : Std.I64), max_score nums = ok r → r.val ≤ weightedTailSum nums := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ (r : Std.I64), max_score nums = ok r → r.val ≤ weightedTailSum nums) := by
  sorry

/-- Whenever the function returns a result r, r <= (len(nums) - 1) * M, where M is the maximum of nums[0], nums[1], ..., nums[len(nums)-1].
  Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000) :
    ∀ (r : Std.I64), max_score nums = ok r →
      r.val ≤ ((len nums : Int) - 1) * maxElem nums := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ (r : Std.I64), max_score nums = ok r →
      r.val ≤ ((len nums : Int) - 1) * maxElem nums) := by
  sorry

/-- Whenever max_score(nums) returns a result r and max_score(nums') returns a result r', we have r' = r + (len(nums) - 1) * c.
  Preconditions: len(nums) >= 2, len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; len(nums') = len(nums), and for every i with 0 <= i < len(nums'), 1 <= nums'[i] <= 100000; and there is an integer c such that nums'[i] = nums[i] + c for every i with 0 <= i < len(nums). -/
theorem spec_8 (nums nums' : Slice Std.I64) (c : Int)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hlen : len nums' = len nums)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 100000)
    (hc : ∀ i, i < len nums → elem nums' i = elem nums i + c) :
    ∀ (r r' : Std.I64), max_score nums = ok r → max_score nums' = ok r' →
      r'.val = r.val + ((len nums : Int) - 1) * c := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : Int)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hlen : len nums' = len nums)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 100000)
    (hc : ∀ i, i < len nums → elem nums' i = elem nums i + c), ∀ (r r' : Std.I64), max_score nums = ok r → max_score nums' = ok r' →
      r'.val = r.val + ((len nums : Int) - 1) * c) := by
  sorry

/-- If nums[i] <= nums[i+1] for every i with 0 <= i < len(nums)-1 (i.e., nums is non-decreasing), then whenever the function returns a result r, r = (len(nums) - 1) * nums[len(nums)-1].
  Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hmono : ∀ i, i < len nums - 1 → elem nums i ≤ elem nums (i + 1)) :
    ∀ (r : Std.I64), max_score nums = ok r →
      r.val = ((len nums : Int) - 1) * elem nums (len nums - 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hmono : ∀ i, i < len nums - 1 → elem nums i ≤ elem nums (i + 1)), ∀ (r : Std.I64), max_score nums = ok r →
      r.val = ((len nums : Int) - 1) * elem nums (len nums - 1)) := by
  sorry

/-- If nums[i] >= nums[i+1] for every i with 0 <= i < len(nums)-1 (i.e., nums is non-increasing), then whenever the function returns a result r, r = sum_{j=1}^{len(nums)-1} nums[j].
  Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hmono : ∀ i, i < len nums - 1 → elem nums (i + 1) ≤ elem nums i) :
    ∀ (r : Std.I64), max_score nums = ok r → r.val = tailSum nums := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hmono : ∀ i, i < len nums - 1 → elem nums (i + 1) ≤ elem nums i), ∀ (r : Std.I64), max_score nums = ok r → r.val = tailSum nums) := by
  sorry

/-- The function returns a result r (i.e., it does not fail due to arithmetic overflow, out-of-bounds access, or panic) for every nums satisfying the preconditions.
  Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000) :
    ∃ r : Std.I64, max_score nums = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000), ∃ r : Std.I64, max_score nums = ok r) := by
  sorry

/-- For every k with 0 < k < len(nums)-1, whenever the function returns a result r, r >= k * nums[k] + (len(nums) - 1 - k) * nums[len(nums)-1].
  Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000) :
    ∀ (k : Nat), 0 < k → k < len nums - 1 →
      ∀ (r : Std.I64), max_score nums = ok r →
        r.val ≥ (k : Int) * elem nums k +
          ((len nums : Int) - 1 - (k : Int)) * elem nums (len nums - 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ (k : Nat), 0 < k → k < len nums - 1 →
      ∀ (r : Std.I64), max_score nums = ok r →
        r.val ≥ (k : Int) * elem nums k +
          ((len nums : Int) - 1 - (k : Int)) * elem nums (len nums - 1)) := by
  sorry

/-- Whenever max_score(nums) returns a result r and max_score(nums') returns a result r', we have r <= r'.
  Preconditions: len(nums) >= 2, len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; len(nums') = len(nums), and for every i with 0 <= i < len(nums'), 1 <= nums'[i] <= 100000; and for every i with 0 <= i < len(nums), nums[i] <= nums'[i]. -/
theorem spec_13 (nums nums' : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hlen : len nums' = len nums)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 100000)
    (hle : ∀ i, i < len nums → elem nums i ≤ elem nums' i) :
    ∀ (r r' : Std.I64), max_score nums = ok r → max_score nums' = ok r' →
      r.val ≤ r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen_lb : 2 ≤ len nums) (hlen_ub : len nums ≤ 1000)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hlen : len nums' = len nums)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 100000)
    (hle : ∀ i, i < len nums → elem nums i ≤ elem nums' i), ∀ (r r' : Std.I64), max_score nums = ok r → max_score nums' = ok r' →
      r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaxScore
