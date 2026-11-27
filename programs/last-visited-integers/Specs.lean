import Aegis.LastVisitedIntegers.Code.Funs

/-!
# Specifications of `Aegis.LastVisitedIntegers.last_visited_integers`

LeetCode problem `last-visited-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LastVisitedIntegers

open Aegis.LastVisitedIntegers (last_visited_integers)

def inVals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def outVals (r : alloc.vec.Vec I64) : List ℤ := r.val.map (fun x => x.val)

def Admissible (z : ℤ) : Prop := z = -1 ∨ (1 ≤ z ∧ z ≤ 100)

def ValidInput (l : List ℤ) : Prop :=
  1 ≤ l.length ∧ l.length ≤ 100 ∧ ∀ (i : ℕ) (z : ℤ), l[i]? = some z → Admissible z

def negOneIdxs (l : List ℤ) : List ℕ :=
  (List.range l.length).filter fun i => l[i]? = some (-1)

def prevNonNegOneIdxsDecr (l : List ℤ) (i : ℕ) : List ℕ :=
  ((List.range i).filter fun p => l[p]? ≠ some (-1)).reverse

def prevNonNegOneIdxs (l : List ℤ) (i : ℕ) : List ℕ :=
  (List.range i).filter fun p => l[p]? ≠ some (-1)

def negOneBlockLen (l : List ℤ) (i : ℕ) : ℕ :=
  ((List.range (i + 1)).filter fun j => ∀ q, j ≤ q → q ≤ i → l[q]? = some (-1)).length

def countNonNegOne (l : List ℤ) (a b : ℕ) : ℕ :=
  ((List.range b).filter fun p => a ≤ p ∧ l[p]? ≠ some (-1)).length

def IsMaxNonNegOneBelow (l : List ℤ) (i p : ℕ) : Prop :=
  p < i ∧ l[p]? ≠ some (-1) ∧ ∀ q, p < q → q < i → l[q]? = some (-1)

def IsSrcIdx (l : List ℤ) (i p : ℕ) (v : ℤ) : Prop :=
  p < i ∧ l[p]? = some v ∧ countNonNegOne l (p + 1) i = negOneBlockLen l i - 1

/-- Let i_0 < i_1 < ... < i_{L-1} be the indices i with 0 <= i < len(nums) and nums[i] == -1, so L is the number of -1 entries in nums. The function returns a vector r with len(r) = L such that for every t with 0 <= t < L: let k be the number of indices j with 0 <= j <= i_t such that nums[q] == -1 for every q with j <= q <= i_t (the length of the maximal contiguous block of -1s ending at i_t), and let p_1 > p_2 > ... > p_m be the indices p with 0 <= p < i_t and nums[p] != -1, listed in strictly decreasing order (m is the number of such indices). If k <= m then r[t] = nums[p_k]; if k > m then r[t] = -1.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), nums[i] == -1 or 1 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice I64) (h : ValidInput (inVals nums)) :
    ∃ r : alloc.vec.Vec I64,
      last_visited_integers nums = ok r ∧
      (outVals r).length = (negOneIdxs (inVals nums)).length ∧
      (∀ (t it : ℕ), (negOneIdxs (inVals nums))[t]? = some it →
        (negOneBlockLen (inVals nums) it ≤ (prevNonNegOneIdxs (inVals nums) it).length →
          ∀ (p : ℕ) (z : ℤ),
            (prevNonNegOneIdxsDecr (inVals nums) it)[negOneBlockLen (inVals nums) it - 1]? =
                some p →
              (inVals nums)[p]? = some z → (outVals r)[t]? = some z) ∧
        ((prevNonNegOneIdxs (inVals nums) it).length < negOneBlockLen (inVals nums) it →
          (outVals r)[t]? = some (-1))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput (inVals nums)), ∃ r : alloc.vec.Vec I64,
      last_visited_integers nums = ok r ∧
      (outVals r).length = (negOneIdxs (inVals nums)).length ∧
      (∀ (t it : ℕ), (negOneIdxs (inVals nums))[t]? = some it →
        (negOneBlockLen (inVals nums) it ≤ (prevNonNegOneIdxs (inVals nums) it).length →
          ∀ (p : ℕ) (z : ℤ),
            (prevNonNegOneIdxsDecr (inVals nums) it)[negOneBlockLen (inVals nums) it - 1]? =
                some p →
              (inVals nums)[p]? = some z → (outVals r)[t]? = some z) ∧
        ((prevNonNegOneIdxs (inVals nums) it).length < negOneBlockLen (inVals nums) it →
          (outVals r)[t]? = some (-1)))) := by
  sorry

/-- Let L be the number of indices i with 0 <= i < len(nums) and nums[i] == -1. The function returns a vector r with len(r) = L.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), nums[i] == -1 or 1 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice I64) (h : ValidInput (inVals nums)) :
    ∃ r : alloc.vec.Vec I64,
      last_visited_integers nums = ok r ∧
      (outVals r).length = (negOneIdxs (inVals nums)).length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput (inVals nums)), ∃ r : alloc.vec.Vec I64,
      last_visited_integers nums = ok r ∧
      (outVals r).length = (negOneIdxs (inVals nums)).length) := by
  sorry

/-- For every t with 0 <= t < len(r), either r[t] == -1 or 1 <= r[t] <= 100.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), nums[i] == -1 or 1 <= nums[i] <= 100. -/
theorem spec_3 (nums : Slice I64) (h : ValidInput (inVals nums)) :
    ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t : ℕ) (z : ℤ), (outVals r)[t]? = some z → Admissible z := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput (inVals nums)), ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t : ℕ) (z : ℤ), (outVals r)[t]? = some z → Admissible z) := by
  sorry

/-- The function returns a result r (it does not fail) for every nums satisfying the preconditions.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), nums[i] == -1 or 1 <= nums[i] <= 100. -/
theorem spec_4 (nums : Slice I64) (h : ValidInput (inVals nums)) :
    ∃ r : alloc.vec.Vec I64, last_visited_integers nums = ok r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput (inVals nums)), ∃ r : alloc.vec.Vec I64, last_visited_integers nums = ok r) := by
  sorry

/-- For every t with 0 <= t < len(r), if r[t] != -1, letting i_t be the t-th index (0-based) with nums[i_t] == -1, there exists an index p such that 0 <= p < i_t, nums[p] != -1, and r[t] = nums[p].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), nums[i] == -1 or 1 <= nums[i] <= 100. -/
theorem spec_5 (nums : Slice I64) (h : ValidInput (inVals nums)) :
    ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t it : ℕ) (z : ℤ), (negOneIdxs (inVals nums))[t]? = some it →
        (outVals r)[t]? = some z → z ≠ -1 →
        ∃ p, p < it ∧ (inVals nums)[p]? = some z := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput (inVals nums)), ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t it : ℕ) (z : ℤ), (negOneIdxs (inVals nums))[t]? = some it →
        (outVals r)[t]? = some z → z ≠ -1 →
        ∃ p, p < it ∧ (inVals nums)[p]? = some z) := by
  sorry

/-- For every t with 0 <= t < len(r), letting i_t be the t-th index with nums[i_t] == -1 and k the length of the maximal contiguous block of -1s ending at i_t, we have r[t] == -1 if and only if the number of indices p with 0 <= p < i_t and nums[p] != -1 is strictly less than k.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), nums[i] == -1 or 1 <= nums[i] <= 100. -/
theorem spec_6 (nums : Slice I64) (h : ValidInput (inVals nums)) :
    ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t it : ℕ) (z : ℤ), (negOneIdxs (inVals nums))[t]? = some it →
        (outVals r)[t]? = some z →
        (z = -1 ↔
          (prevNonNegOneIdxs (inVals nums) it).length <
            negOneBlockLen (inVals nums) it) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput (inVals nums)), ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t it : ℕ) (z : ℤ), (negOneIdxs (inVals nums))[t]? = some it →
        (outVals r)[t]? = some z →
        (z = -1 ↔
          (prevNonNegOneIdxs (inVals nums) it).length <
            negOneBlockLen (inVals nums) it)) := by
  sorry

/-- For every t with 0 <= t < len(r) and r[t] != -1, letting i_t be the t-th index with nums[i_t] == -1, k the length of the maximal contiguous block of -1s ending at i_t, and p_1 > p_2 > ... > p_m the indices p with 0 <= p < i_t and nums[p] != -1 in strictly decreasing order (m = number of such indices), we have k <= m and r[t] = nums[p_k].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), nums[i] == -1 or 1 <= nums[i] <= 100. -/
theorem spec_7 (nums : Slice I64) (h : ValidInput (inVals nums)) :
    ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t it : ℕ) (z : ℤ), (negOneIdxs (inVals nums))[t]? = some it →
        (outVals r)[t]? = some z → z ≠ -1 →
        negOneBlockLen (inVals nums) it ≤ (prevNonNegOneIdxs (inVals nums) it).length ∧
          ∀ p,
            (prevNonNegOneIdxsDecr (inVals nums) it)[negOneBlockLen (inVals nums) it - 1]? =
                some p →
              (inVals nums)[p]? = some z := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput (inVals nums)), ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t it : ℕ) (z : ℤ), (negOneIdxs (inVals nums))[t]? = some it →
        (outVals r)[t]? = some z → z ≠ -1 →
        negOneBlockLen (inVals nums) it ≤ (prevNonNegOneIdxs (inVals nums) it).length ∧
          ∀ p,
            (prevNonNegOneIdxsDecr (inVals nums) it)[negOneBlockLen (inVals nums) it - 1]? =
                some p →
              (inVals nums)[p]? = some z) := by
  sorry

/-- For every t with 0 <= t < len(r), if i_t == 0 or nums[i_t - 1] != -1 (so the -1 at i_t starts a new maximal contiguous block of -1s), then: if there is at least one index p with 0 <= p < i_t and nums[p] != -1, r[t] = nums[p] where p is the largest such index; otherwise r[t] = -1.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), nums[i] == -1 or 1 <= nums[i] <= 100. -/
theorem spec_8 (nums : Slice I64) (h : ValidInput (inVals nums)) :
    ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t it : ℕ) (z : ℤ), (negOneIdxs (inVals nums))[t]? = some it →
        (it = 0 ∨ (inVals nums)[it - 1]? ≠ some (-1)) →
        (outVals r)[t]? = some z →
        ((∃ p, IsMaxNonNegOneBelow (inVals nums) it p) →
          ∀ p, IsMaxNonNegOneBelow (inVals nums) it p → (inVals nums)[p]? = some z) ∧
        ((¬ ∃ p, IsMaxNonNegOneBelow (inVals nums) it p) → z = -1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput (inVals nums)), ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t it : ℕ) (z : ℤ), (negOneIdxs (inVals nums))[t]? = some it →
        (it = 0 ∨ (inVals nums)[it - 1]? ≠ some (-1)) →
        (outVals r)[t]? = some z →
        ((∃ p, IsMaxNonNegOneBelow (inVals nums) it p) →
          ∀ p, IsMaxNonNegOneBelow (inVals nums) it p → (inVals nums)[p]? = some z) ∧
        ((¬ ∃ p, IsMaxNonNegOneBelow (inVals nums) it p) → z = -1)) := by
  sorry

/-- For any t with 0 <= t < len(r) and r[t] != -1, define the source index of r[t] as the unique p such that 0 <= p < i_t, nums[p] = r[t], and the number of positive entries in nums[p+1 .. i_t-1] equals k(i_t) - 1, where i_t is the t-th -1 index and k(i_t) is the length of the maximal contiguous block of -1s ending at i_t. For every t with 0 <= t < len(r) - 1, if i_{t+1} = i_t + 1 and both r[t] != -1 and r[t+1] != -1, then the source index of r[t+1] is strictly less than the source index of r[t].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), nums[i] == -1 or 1 <= nums[i] <= 100. -/
theorem spec_9 (nums : Slice I64) (h : ValidInput (inVals nums)) :
    ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t : ℕ), t + 1 < (outVals r).length →
      ∀ (it it' : ℕ), (negOneIdxs (inVals nums))[t]? = some it →
        (negOneIdxs (inVals nums))[t + 1]? = some it' → it' = it + 1 →
      ∀ (z z' : ℤ), (outVals r)[t]? = some z → (outVals r)[t + 1]? = some z' →
        z ≠ -1 → z' ≠ -1 →
      ∀ (p p' : ℕ), IsSrcIdx (inVals nums) it p z →
        IsSrcIdx (inVals nums) it' p' z' → p' < p := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput (inVals nums)), ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t : ℕ), t + 1 < (outVals r).length →
      ∀ (it it' : ℕ), (negOneIdxs (inVals nums))[t]? = some it →
        (negOneIdxs (inVals nums))[t + 1]? = some it' → it' = it + 1 →
      ∀ (z z' : ℤ), (outVals r)[t]? = some z → (outVals r)[t + 1]? = some z' →
        z ≠ -1 → z' ≠ -1 →
      ∀ (p p' : ℕ), IsSrcIdx (inVals nums) it p z →
        IsSrcIdx (inVals nums) it' p' z' → p' < p) := by
  sorry

/-- For every t with 0 <= t < len(r), let i_t be the t-th index with nums[i_t] == -1. For any array nums' satisfying the preconditions and agreeing with nums on all indices j with 0 <= j <= i_t, the t-th element of the result computed from nums' equals r[t].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), nums[i] == -1 or 1 <= nums[i] <= 100. -/
theorem spec_10 (nums : Slice I64) (h : ValidInput (inVals nums)) :
    ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t it : ℕ), (negOneIdxs (inVals nums))[t]? = some it →
        ∀ (nums' : Slice I64), ValidInput (inVals nums') →
          (∀ j, j ≤ it → (inVals nums')[j]? = (inVals nums)[j]?) →
            ∀ (r' : alloc.vec.Vec I64), last_visited_integers nums' = ok r' →
              (outVals r')[t]? = (outVals r)[t]? := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput (inVals nums)), ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t it : ℕ), (negOneIdxs (inVals nums))[t]? = some it →
        ∀ (nums' : Slice I64), ValidInput (inVals nums') →
          (∀ j, j ≤ it → (inVals nums')[j]? = (inVals nums)[j]?) →
            ∀ (r' : alloc.vec.Vec I64), last_visited_integers nums' = ok r' →
              (outVals r')[t]? = (outVals r)[t]?) := by
  sorry

/-- Let i_0 < i_1 < ... < i_{L-1} be the indices i with 0 <= i < len(nums) and nums[i] == -1. For every t with 0 <= t < L - 1, if i_{t+1} = i_t + 1 and r[t] == -1, then r[t+1] == -1.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), nums[i] == -1 or 1 <= nums[i] <= 100. -/
theorem spec_11 (nums : Slice I64) (h : ValidInput (inVals nums)) :
    ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t : ℕ), t + 1 < (negOneIdxs (inVals nums)).length →
      ∀ (it it' : ℕ), (negOneIdxs (inVals nums))[t]? = some it →
        (negOneIdxs (inVals nums))[t + 1]? = some it' → it' = it + 1 →
        (outVals r)[t]? = some (-1) → (outVals r)[t + 1]? = some (-1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput (inVals nums)), ∀ (r : alloc.vec.Vec I64), last_visited_integers nums = ok r →
      ∀ (t : ℕ), t + 1 < (negOneIdxs (inVals nums)).length →
      ∀ (it it' : ℕ), (negOneIdxs (inVals nums))[t]? = some it →
        (negOneIdxs (inVals nums))[t + 1]? = some it' → it' = it + 1 →
        (outVals r)[t]? = some (-1) → (outVals r)[t + 1]? = some (-1)) := by
  sorry

end AegisSpec.LastVisitedIntegers
