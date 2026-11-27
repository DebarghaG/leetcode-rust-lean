import Aegis.MaximumSumOfHeights.Code.Funs

/-!
# Specifications of `Aegis.MaximumSumOfHeights.maximum_sum_of_heights`

LeetCode problem `beautiful-towers-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumSumOfHeights

namespace AegisSpec.MaximumSumOfHeights

def sliceInts (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def idx (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def lmax (l : List ℤ) : ℤ :=
  match l with
  | [] => 0
  | x :: xs => xs.foldr max x

def lmin (l : List ℤ) : ℤ :=
  match l with
  | [] => 0
  | x :: xs => xs.foldr min x

def IsMountain (heights : List ℤ) : Prop :=
  ∃ p, p < heights.length ∧
    (∀ j, 1 ≤ j → j ≤ p → idx heights (j - 1) ≤ idx heights j) ∧
    (∀ k, p ≤ k → k + 1 < heights.length → idx heights (k + 1) ≤ idx heights k)

def WithinLimits (hs ms : List ℤ) : Prop :=
  ∀ i, i < ms.length → 1 ≤ idx hs i ∧ idx hs i ≤ idx ms i

/-- For every such maxHeights, the function returns a result r and r is the maximum over all integer sequences heights of length n of sum_{i=0}^{n-1} heights[i], subject to: (i) 1 <= heights[i] <= maxHeights[i] for every 0 <= i < n; and (ii) heights is a mountain, meaning there exists a peak index p with 0 <= p < n such that heights[j-1] <= heights[j] for every 1 <= j <= p and heights[k+1] <= heights[k] for every p <= k < n-1. Thus heights is nondecreasing up to p and nonincreasing from p onward.
  Preconditions: n = len(maxHeights), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= maxHeights[i] <= 1000000000. -/
theorem spec_1 (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000) :
    ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      (∀ heights : List ℤ, heights.length = n →
        WithinLimits heights (sliceInts maxHeights) → IsMountain heights →
        heights.sum ≤ r.val) ∧
      (∃ heights : List ℤ, heights.length = n ∧
        WithinLimits heights (sliceInts maxHeights) ∧ IsMountain heights ∧
        heights.sum = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000), ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      (∀ heights : List ℤ, heights.length = n →
        WithinLimits heights (sliceInts maxHeights) → IsMountain heights →
        heights.sum ≤ r.val) ∧
      (∃ heights : List ℤ, heights.length = n ∧
        WithinLimits heights (sliceInts maxHeights) ∧ IsMountain heights ∧
        heights.sum = r.val)) := by
  sorry

/-- For every such maxHeights, the Lean function returns a success value r rather than failing; no arithmetic overflow, out-of-bounds access, or panic occurs during the call.
  Preconditions: n = len(maxHeights), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= maxHeights[i] <= 1000000000. -/
theorem spec_2 (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000) :
    ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000), ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r) := by
  sorry

/-- For every such maxHeights, the function returns a result r and r <= sum_{i=0}^{n-1} maxHeights[i].
  Preconditions: n = len(maxHeights), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= maxHeights[i] <= 1000000000. -/
theorem spec_3 (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000) :
    ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      r.val ≤ (sliceInts maxHeights).sum := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000), ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      r.val ≤ (sliceInts maxHeights).sum) := by
  sorry

/-- For every such maxHeights, let M = max_{0 <= i < n} maxHeights[i]. The function returns a result r and r >= M + n - 1.
  Preconditions: n = len(maxHeights), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= maxHeights[i] <= 1000000000. -/
theorem spec_4 (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000) :
    ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      lmax (sliceInts maxHeights) + (n : ℤ) - 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000), ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      lmax (sliceInts maxHeights) + (n : ℤ) - 1 ≤ r.val) := by
  sorry

/-- For every such maxHeights, let m = min_{0 <= i < n} maxHeights[i]. The function returns a result r and r >= n * m.
  Preconditions: n = len(maxHeights), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= maxHeights[i] <= 1000000000. -/
theorem spec_5 (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000) :
    ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      (n : ℤ) * lmin (sliceInts maxHeights) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000), ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      (n : ℤ) * lmin (sliceInts maxHeights) ≤ r.val) := by
  sorry

/-- For every such maxHeights, the function returns a result r and there exists an integer sequence heights of length n such that: (i) 1 <= heights[i] <= maxHeights[i] for every 0 <= i < n; (ii) heights is a mountain, meaning there exists p with 0 <= p < n such that heights[j-1] <= heights[j] for every 1 <= j <= p and heights[k+1] <= heights[k] for every p <= k < n-1; and (iii) sum_{i=0}^{n-1} heights[i] = r.
  Preconditions: n = len(maxHeights), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= maxHeights[i] <= 1000000000. -/
theorem spec_6 (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000) :
    ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      ∃ heights : List ℤ, heights.length = n ∧
        WithinLimits heights (sliceInts maxHeights) ∧ IsMountain heights ∧
        heights.sum = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000), ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      ∃ heights : List ℤ, heights.length = n ∧
        WithinLimits heights (sliceInts maxHeights) ∧ IsMountain heights ∧
        heights.sum = r.val) := by
  sorry

/-- For every such maxHeights, the function returns a result r and for every integer sequence heights of length n that satisfies (i) 1 <= heights[i] <= maxHeights[i] for every 0 <= i < n and (ii) heights is a mountain in the sense above, one has sum_{i=0}^{n-1} heights[i] <= r.
  Preconditions: n = len(maxHeights), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= maxHeights[i] <= 1000000000. -/
theorem spec_7 (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000) :
    ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      ∀ heights : List ℤ, heights.length = n →
        WithinLimits heights (sliceInts maxHeights) → IsMountain heights →
        heights.sum ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000), ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      ∀ heights : List ℤ, heights.length = n →
        WithinLimits heights (sliceInts maxHeights) → IsMountain heights →
        heights.sum ≤ r.val) := by
  sorry

/-- For every such maxHeights, the function returns a result r and r = sum_{i=0}^{n-1} maxHeights[i].
  Preconditions: n = len(maxHeights), 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= maxHeights[i] <= 1000000000, and for every i with 0 <= i < n-1, maxHeights[i] <= maxHeights[i+1]. -/
theorem spec_8 (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000)
    (hsorted : ∀ i, i + 1 < n → idx (sliceInts maxHeights) i ≤
      idx (sliceInts maxHeights) (i + 1)) :
    ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      r.val = (sliceInts maxHeights).sum := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (maxHeights : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000)
    (hsorted : ∀ i, i + 1 < n → idx (sliceInts maxHeights) i ≤
      idx (sliceInts maxHeights) (i + 1)), ∃ r : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      r.val = (sliceInts maxHeights).sum) := by
  sorry

/-- For every such A and B, the function returns results r_A on A and r_B on B, and r_A <= r_B.
  Preconditions: A and B are Slice Std.I64 values with the same length n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= A[i] <= B[i] <= 1000000000. -/
theorem spec_9 (A B : Slice Std.I64) (n : ℕ)
    (hnA : n = A.val.length) (hnB : n = B.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts A) i ∧ idx (sliceInts A) i ≤ idx (sliceInts B) i ∧
      idx (sliceInts B) i ≤ 1000000000) :
    ∃ rA rB : Std.I64, maximum_sum_of_heights A = ok rA ∧
      maximum_sum_of_heights B = ok rB ∧ rA.val ≤ rB.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (A B : Slice Std.I64) (n : ℕ)
    (hnA : n = A.val.length) (hnB : n = B.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts A) i ∧ idx (sliceInts A) i ≤ idx (sliceInts B) i ∧
      idx (sliceInts B) i ≤ 1000000000), ∃ rA rB : Std.I64, maximum_sum_of_heights A = ok rA ∧
      maximum_sum_of_heights B = ok rB ∧ rA.val ≤ rB.val) := by
  sorry

/-- For every such maxHeights, let rev be the length-n Slice defined by rev[i] = maxHeights[n-1-i] for 0 <= i < n. Let r and r_rev be the results returned by the function on maxHeights and rev respectively. Then r = r_rev.
  Preconditions: n = len(maxHeights), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= maxHeights[i] <= 1000000000. -/
theorem spec_10 (maxHeights rev : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000)
    (hrev : rev.val = maxHeights.val.reverse) :
    ∃ r r_rev : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      maximum_sum_of_heights rev = ok r_rev ∧ r.val = r_rev.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (maxHeights rev : Slice Std.I64) (n : ℕ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hlim : ∀ i, i < n → 1 ≤ idx (sliceInts maxHeights) i ∧
      idx (sliceInts maxHeights) i ≤ 1000000000)
    (hrev : rev.val = maxHeights.val.reverse), ∃ r r_rev : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      maximum_sum_of_heights rev = ok r_rev ∧ r.val = r_rev.val) := by
  sorry

/-- Let scaled be the length-n Slice with scaled[i] = c*maxHeights[i]. Let r and r_scaled be the results returned by the function on maxHeights and scaled respectively. Then r_scaled = c*r.
  Preconditions: c is a positive integer, n = len(maxHeights), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= c*maxHeights[i] <= 1000000000. -/
theorem spec_11 (maxHeights scaled : Slice Std.I64) (n : ℕ) (c : ℤ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hc_pos : 1 ≤ c)
    (hlim : ∀ i, i < n → 1 ≤ c * idx (sliceInts maxHeights) i ∧
      c * idx (sliceInts maxHeights) i ≤ 1000000000)
    (hscaled_len : scaled.val.length = n)
    (hscaled : ∀ i, i < n → idx (sliceInts scaled) i = c * idx (sliceInts maxHeights) i) :
    ∃ r r_scaled : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      maximum_sum_of_heights scaled = ok r_scaled ∧ r_scaled.val = c * r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (maxHeights scaled : Slice Std.I64) (n : ℕ) (c : ℤ)
    (hn : n = maxHeights.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hc_pos : 1 ≤ c)
    (hlim : ∀ i, i < n → 1 ≤ c * idx (sliceInts maxHeights) i ∧
      c * idx (sliceInts maxHeights) i ≤ 1000000000)
    (hscaled_len : scaled.val.length = n)
    (hscaled : ∀ i, i < n → idx (sliceInts scaled) i = c * idx (sliceInts maxHeights) i), ∃ r r_scaled : Std.I64, maximum_sum_of_heights maxHeights = ok r ∧
      maximum_sum_of_heights scaled = ok r_scaled ∧ r_scaled.val = c * r.val) := by
  sorry

end AegisSpec.MaximumSumOfHeights
