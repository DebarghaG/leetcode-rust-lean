import Aegis.Intersection.Code.Funs

/-!
# Specifications of `Aegis.Intersection.intersection`

LeetCode problem `intersection-of-multiple-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Intersection

def vals (v : alloc.vec.Vec Std.I64) : List Int :=
  v.val.map (fun x => x.val)

def matrix (nums : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  nums.val.map vals

def entry (l : List Int) (i : Nat) : Int := l.getD i 0

def OccursIn (x : Int) (l : List Int) : Prop :=
  ∃ j : Nat, j < l.length ∧ entry l j = x

def OccursInEveryRow (rows : List (List Int)) (x : Int) : Prop :=
  ∀ r ∈ rows, OccursIn x r

def rowValues (l : List Int) : Finset Int :=
  l.toFinset

def commonValues (rows : List (List Int)) : Finset Int :=
  match rows with
  | [] => ∅
  | r :: rs => rs.foldl (fun acc row => acc ∩ rowValues row) (rowValues r)

def StrictlyIncreasing (l : List Int) : Prop :=
  ∀ p : Nat, p + 1 < l.length → entry l p < entry l (p + 1)

def Pre (nums : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  let rows := matrix nums
  1 ≤ rows.length ∧
  rows.length ≤ 1000 ∧
  (∀ r ∈ rows, 1 ≤ r.length) ∧
  (rows.map (fun r => r.length)).sum ≤ 1000 ∧
  (∀ r ∈ rows, ∀ x ∈ r, 1 ≤ x ∧ x ≤ 1000) ∧
  (∀ r ∈ rows, r.Nodup)

/-- Whenever the function returns a result r, the following hold: (1) r is strictly increasing, i.e. for every p with 0 <= p < len(r)-1, r[p] < r[p+1]; and (2) for every integer x, x occurs in r (there exists q with 0 <= q < len(r) and r[q] = x) if and only if x occurs in every row nums[i] (for every i with 0 <= i < len(nums) there exists j with 0 <= j < len(nums[i]) and nums[i][j] = x).
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), len(nums[i]) >= 1; the sum of len(nums[i]) over all i with 0 <= i < len(nums) is at most 1000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 1000; for every i, j, and k with 0 <= i < len(nums), 0 <= j < len(nums[i]), 0 <= k < len(nums[i]), and j != k, nums[i][j] != nums[i][k]. -/
theorem spec_1 (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums) :
    ∀ r, Aegis.Intersection.intersection nums = ok r →
      StrictlyIncreasing (vals r) ∧
      (∀ x : Int, OccursIn x (vals r) ↔ OccursInEveryRow (matrix nums) x) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums), ∀ r, Aegis.Intersection.intersection nums = ok r →
      StrictlyIncreasing (vals r) ∧
      (∀ x : Int, OccursIn x (vals r) ↔ OccursInEveryRow (matrix nums) x)) := by
  sorry

/-- Whenever the function returns a result r, for every q with 0 <= q < len(r) and every i with 0 <= i < len(nums), the value r[q] occurs in nums[i], i.e. there exists j with 0 <= j < len(nums[i]) and nums[i][j] = r[q].
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), len(nums[i]) >= 1; the sum of len(nums[i]) over all i with 0 <= i < len(nums) is at most 1000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 1000; for every i, j, and k with 0 <= i < len(nums), 0 <= j < len(nums[i]), 0 <= k < len(nums[i]), and j != k, nums[i][j] != nums[i][k]. -/
theorem spec_2 (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums) :
    ∀ r, Aegis.Intersection.intersection nums = ok r →
      ∀ q : Nat, q < (vals r).length →
        ∀ i : Nat, ∀ hi : i < (matrix nums).length,
          OccursIn (entry (vals r) q) ((matrix nums).get ⟨i, hi⟩) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums), ∀ r, Aegis.Intersection.intersection nums = ok r →
      ∀ q : Nat, q < (vals r).length →
        ∀ i : Nat, ∀ hi : i < (matrix nums).length,
          OccursIn (entry (vals r) q) ((matrix nums).get ⟨i, hi⟩)) := by
  sorry

/-- Whenever the function returns a result r, for every integer x, if x occurs in every row nums[i] (for every i with 0 <= i < len(nums) there exists j with 0 <= j < len(nums[i]) and nums[i][j] = x), then there exists q with 0 <= q < len(r) and r[q] = x.
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), len(nums[i]) >= 1; the sum of len(nums[i]) over all i with 0 <= i < len(nums) is at most 1000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 1000; for every i, j, and k with 0 <= i < len(nums), 0 <= j < len(nums[i]), 0 <= k < len(nums[i]), and j != k, nums[i][j] != nums[i][k]. -/
theorem spec_3 (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums) :
    ∀ r, Aegis.Intersection.intersection nums = ok r →
      ∀ x : Int, OccursInEveryRow (matrix nums) x → OccursIn x (vals r) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums), ∀ r, Aegis.Intersection.intersection nums = ok r →
      ∀ x : Int, OccursInEveryRow (matrix nums) x → OccursIn x (vals r)) := by
  sorry

/-- Whenever the function returns a result r, for every p with 0 <= p < len(r)-1, r[p] < r[p+1].
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), len(nums[i]) >= 1; the sum of len(nums[i]) over all i with 0 <= i < len(nums) is at most 1000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 1000; for every i, j, and k with 0 <= i < len(nums), 0 <= j < len(nums[i]), 0 <= k < len(nums[i]), and j != k, nums[i][j] != nums[i][k]. -/
theorem spec_4 (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums) :
    ∀ r, Aegis.Intersection.intersection nums = ok r →
      StrictlyIncreasing (vals r) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums), ∀ r, Aegis.Intersection.intersection nums = ok r →
      StrictlyIncreasing (vals r)) := by
  sorry

/-- Whenever the function returns a result r, for every p and q with 0 <= p < len(r) and 0 <= q < len(r), if p != q then r[p] != r[q].
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), len(nums[i]) >= 1; the sum of len(nums[i]) over all i with 0 <= i < len(nums) is at most 1000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 1000; for every i, j, and k with 0 <= i < len(nums), 0 <= j < len(nums[i]), 0 <= k < len(nums[i]), and j != k, nums[i][j] != nums[i][k]. -/
theorem spec_5 (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums) :
    ∀ r, Aegis.Intersection.intersection nums = ok r →
      ∀ p q : Nat, p < (vals r).length → q < (vals r).length → p ≠ q →
        entry (vals r) p ≠ entry (vals r) q := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums), ∀ r, Aegis.Intersection.intersection nums = ok r →
      ∀ p q : Nat, p < (vals r).length → q < (vals r).length → p ≠ q →
        entry (vals r) p ≠ entry (vals r) q) := by
  sorry

/-- Whenever the function returns a result r, for every p with 0 <= p < len(r), 1 <= r[p] and r[p] <= 1000.
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), len(nums[i]) >= 1; the sum of len(nums[i]) over all i with 0 <= i < len(nums) is at most 1000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 1000; for every i, j, and k with 0 <= i < len(nums), 0 <= j < len(nums[i]), 0 <= k < len(nums[i]), and j != k, nums[i][j] != nums[i][k]. -/
theorem spec_6 (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums) :
    ∀ r, Aegis.Intersection.intersection nums = ok r →
      ∀ p : Nat, p < (vals r).length → 1 ≤ entry (vals r) p ∧ entry (vals r) p ≤ 1000 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums), ∀ r, Aegis.Intersection.intersection nums = ok r →
      ∀ p : Nat, p < (vals r).length → 1 ≤ entry (vals r) p ∧ entry (vals r) p ≤ 1000) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= 1000 and, for every i with 0 <= i < len(nums), len(r) <= len(nums[i]).
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), len(nums[i]) >= 1; the sum of len(nums[i]) over all i with 0 <= i < len(nums) is at most 1000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 1000; for every i, j, and k with 0 <= i < len(nums), 0 <= j < len(nums[i]), 0 <= k < len(nums[i]), and j != k, nums[i][j] != nums[i][k]. -/
theorem spec_7 (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums) :
    ∀ r, Aegis.Intersection.intersection nums = ok r →
      (vals r).length ≤ 1000 ∧
      ∀ i : Nat, ∀ hi : i < (matrix nums).length,
        (vals r).length ≤ ((matrix nums).get ⟨i, hi⟩).length := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums), ∀ r, Aegis.Intersection.intersection nums = ok r →
      (vals r).length ≤ 1000 ∧
      ∀ i : Nat, ∀ hi : i < (matrix nums).length,
        (vals r).length ≤ ((matrix nums).get ⟨i, hi⟩).length) := by
  sorry

/-- Whenever the function returns a result r, len(r) is equal to the number of distinct integers x that occur in every row nums[i] (for every i with 0 <= i < len(nums) there exists j with 0 <= j < len(nums[i]) and nums[i][j] = x).
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), len(nums[i]) >= 1; the sum of len(nums[i]) over all i with 0 <= i < len(nums) is at most 1000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 1000; for every i, j, and k with 0 <= i < len(nums), 0 <= j < len(nums[i]), 0 <= k < len(nums[i]), and j != k, nums[i][j] != nums[i][k]. -/
theorem spec_8 (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums) :
    ∀ r, Aegis.Intersection.intersection nums = ok r →
      (vals r).length = (commonValues (matrix nums)).card := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums), ∀ r, Aegis.Intersection.intersection nums = ok r →
      (vals r).length = (commonValues (matrix nums)).card) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail by arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), len(nums[i]) >= 1; the sum of len(nums[i]) over all i with 0 <= i < len(nums) is at most 1000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 1000; for every i, j, and k with 0 <= i < len(nums), 0 <= j < len(nums[i]), 0 <= k < len(nums[i]), and j != k, nums[i][j] != nums[i][k]. -/
theorem spec_9 (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums) :
    ∃ r, Aegis.Intersection.intersection nums = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums), ∃ r, Aegis.Intersection.intersection nums = ok r) := by
  sorry

/-- Whenever the function returns a result r and len(r) > 0, r[0] and r[len(r)-1] occur in every row nums[i], and for every integer x that occurs in every row nums[i], r[0] <= x <= r[len(r)-1].
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), len(nums[i]) >= 1; the sum of len(nums[i]) over all i with 0 <= i < len(nums) is at most 1000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 1000; for every i, j, and k with 0 <= i < len(nums), 0 <= j < len(nums[i]), 0 <= k < len(nums[i]), and j != k, nums[i][j] != nums[i][k]. -/
theorem spec_10 (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums) :
    ∀ r, Aegis.Intersection.intersection nums = ok r →
      0 < (vals r).length →
        OccursInEveryRow (matrix nums) (entry (vals r) 0) ∧
        OccursInEveryRow (matrix nums) (entry (vals r) ((vals r).length - 1)) ∧
        (∀ x : Int, OccursInEveryRow (matrix nums) x →
          entry (vals r) 0 ≤ x ∧ x ≤ entry (vals r) ((vals r).length - 1)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums), ∀ r, Aegis.Intersection.intersection nums = ok r →
      0 < (vals r).length →
        OccursInEveryRow (matrix nums) (entry (vals r) 0) ∧
        OccursInEveryRow (matrix nums) (entry (vals r) ((vals r).length - 1)) ∧
        (∀ x : Int, OccursInEveryRow (matrix nums) x →
          entry (vals r) 0 ≤ x ∧ x ≤ entry (vals r) ((vals r).length - 1))) := by
  sorry

/-- For every input nums' satisfying the same preconditions and every bijection pi from the row indices {0, ..., len(nums)-1} to the row indices of nums' such that, for every i with 0 <= i < len(nums), the set of values occurring in nums'[i] equals the set of values occurring in nums[pi(i)], if intersection(nums) returns r and intersection(nums') returns r', then r = r'.
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), len(nums[i]) >= 1; the sum of len(nums[i]) over all i with 0 <= i < len(nums) is at most 1000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 1000; for every i, j, and k with 0 <= i < len(nums), 0 <= j < len(nums[i]), 0 <= k < len(nums[i]), and j != k, nums[i][j] != nums[i][k]. -/
theorem spec_11 (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums)
    (nums' : Slice (alloc.vec.Vec Std.I64)) (hpre' : Pre nums')
    (π : Fin (matrix nums).length ≃ Fin (matrix nums').length)
    (hπ : ∀ i : Fin (matrix nums).length,
      rowValues ((matrix nums').get (π i)) = rowValues ((matrix nums).get i)) :
    ∀ r, Aegis.Intersection.intersection nums = ok r →
      ∀ r', Aegis.Intersection.intersection nums' = ok r' → vals r = vals r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre nums)
    (nums' : Slice (alloc.vec.Vec Std.I64)) (hpre' : Pre nums')
    (π : Fin (matrix nums).length ≃ Fin (matrix nums').length)
    (hπ : ∀ i : Fin (matrix nums).length,
      rowValues ((matrix nums').get (π i)) = rowValues ((matrix nums).get i)), ∀ r, Aegis.Intersection.intersection nums = ok r →
      ∀ r', Aegis.Intersection.intersection nums' = ok r' → vals r = vals r') := by
  sorry

end AegisSpec.Intersection
