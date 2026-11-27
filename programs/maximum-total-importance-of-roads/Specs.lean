import Aegis.MaximumImportance.Code.Funs

/-!
# Specifications of `Aegis.MaximumImportance.maximum_importance`

LeetCode problem `maximum-total-importance-of-roads`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumImportance

open Aegis.MaximumImportance Aeneas.Std

def roadCities (e : alloc.vec.Vec Std.I64) : List Int := e.val.map (fun x => x.val)

def roadFirst (e : alloc.vec.Vec Std.I64) : Int := (roadCities e).getD 0 0

def roadSecond (e : alloc.vec.Vec Std.I64) : Int := (roadCities e).getD 1 0

def roadPair (e : alloc.vec.Vec Std.I64) : Int × Int :=
  if roadFirst e ≤ roadSecond e then (roadFirst e, roadSecond e)
  else (roadSecond e, roadFirst e)

def degree (roads : Slice (alloc.vec.Vec Std.I64)) (i : Int) : Int :=
  ((roads.val.filter (fun e => roadFirst e = i ∨ roadSecond e = i)).length : Int)

def degreeList (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64)) : List Int :=
  (List.range n.val.toNat).map (fun k => degree roads (k : Int))

def sortedDegrees (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64)) : List Int :=
  (degreeList n roads).insertionSort (· ≤ ·)

def IsImportanceAssignment (n : Std.I64) (f : Int → Int) : Prop :=
  (∀ i, 0 ≤ i → i < n.val → 1 ≤ f i ∧ f i ≤ n.val) ∧
  (∀ i, 0 ≤ i → i < n.val → ∀ j, 0 ≤ j → j < n.val → f i = f j → i = j) ∧
  (∀ v, 1 ≤ v → v ≤ n.val → ∃ i, 0 ≤ i ∧ i < n.val ∧ f i = v)

def IsCityPermutation (n : Std.I64) (π : Int → Int) : Prop :=
  (∀ i, 0 ≤ i → i < n.val → 0 ≤ π i ∧ π i < n.val) ∧
  (∀ i, 0 ≤ i → i < n.val → ∀ j, 0 ≤ j → j < n.val → π i = π j → i = j) ∧
  (∀ v, 0 ≤ v → v < n.val → ∃ i, 0 ≤ i ∧ i < n.val ∧ π i = v)

def totalImportance (roads : Slice (alloc.vec.Vec Std.I64)) (f : Int → Int) : Int :=
  (roads.val.map (fun e => f (roadFirst e) + f (roadSecond e))).sum

def ValidInput (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  2 ≤ n.val ∧ n.val ≤ 50000 ∧
  1 ≤ roads.val.length ∧ roads.val.length ≤ 50000 ∧
  (∀ e ∈ roads.val, (roadCities e).length = 2) ∧
  (∀ e ∈ roads.val,
    0 ≤ roadFirst e ∧ roadFirst e < n.val ∧
    0 ≤ roadSecond e ∧ roadSecond e < n.val ∧
    roadFirst e ≠ roadSecond e) ∧
  roads.val.Pairwise (fun e₁ e₂ => roadPair e₁ ≠ roadPair e₂)

/-- whenever the function returns a result r, r is the maximum over all bijections f from {0,...,n-1} to {1,...,n} of the total importance sum_{j=0}^{len(roads)-1} (f(roads[j][0]) + f(roads[j][1])). That is, for every such bijection f, sum_{j=0}^{len(roads)-1} (f(roads[j][0]) + f(roads[j][1])) <= r, and there exists at least one such bijection f for which equality holds.
  Preconditions: 2 <= n <= 50000, 1 <= len(roads) <= 50000, every road has length 2, for every j in 0..len(roads)-1, 0 <= roads[j][0] < n, 0 <= roads[j][1] < n, roads[j][0] != roads[j][1], and no two roads are the same unordered pair. -/
theorem spec_1 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads) :
    ∀ r : Std.I64, maximum_importance n roads = Result.ok r →
      (∀ f : Int → Int, IsImportanceAssignment n f → totalImportance roads f ≤ r.val) ∧
      (∃ f : Int → Int, IsImportanceAssignment n f ∧ totalImportance roads f = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads), ∀ r : Std.I64, maximum_importance n roads = Result.ok r →
      (∀ f : Int → Int, IsImportanceAssignment n f → totalImportance roads f ≤ r.val) ∧
      (∃ f : Int → Int, IsImportanceAssignment n f ∧ totalImportance roads f = r.val)) := by
  sorry

/-- whenever the function returns a result r, let d(i) for i in 0..n-1 be the number of roads incident to city i (i.e., the number of j in 0..len(roads)-1 with roads[j][0]=i or roads[j][1]=i). Let s_1 <= s_2 <= ... <= s_n be the nondecreasing rearrangement of (d(0),...,d(n-1)). Then r = sum_{k=1}^{n} k * s_k.
  Preconditions: 2 <= n <= 50000, 1 <= len(roads) <= 50000, every road has length 2, for every j in 0..len(roads)-1, 0 <= roads[j][0] < n, 0 <= roads[j][1] < n, roads[j][0] != roads[j][1], and no two roads are the same unordered pair. -/
theorem spec_2 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads) :
    ∀ r : Std.I64, maximum_importance n roads = Result.ok r →
      r.val = ∑ k ∈ Finset.range n.val.toNat,
        ((k : Int) + 1) * (sortedDegrees n roads).getD k 0 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads), ∀ r : Std.I64, maximum_importance n roads = Result.ok r →
      r.val = ∑ k ∈ Finset.range n.val.toNat,
        ((k : Int) + 1) * (sortedDegrees n roads).getD k 0) := by
  sorry

/-- the function returns a result r (i.e., it does not fail due to arithmetic overflow, out-of-bounds access, or panic) for every input satisfying the preconditions.
  Preconditions: 2 <= n <= 50000, 1 <= len(roads) <= 50000, every road has length 2, for every j in 0..len(roads)-1, 0 <= roads[j][0] < n, 0 <= roads[j][1] < n, roads[j][0] != roads[j][1], and no two roads are the same unordered pair. -/
theorem spec_3 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads) :
    ∃ r : Std.I64, maximum_importance n roads = Result.ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads), ∃ r : Std.I64, maximum_importance n roads = Result.ok r) := by
  sorry

/-- whenever the function returns a result r, r >= 3 * len(roads).
  Preconditions: 2 <= n <= 50000, 1 <= len(roads) <= 50000, every road has length 2, for every j in 0..len(roads)-1, 0 <= roads[j][0] < n, 0 <= roads[j][1] < n, roads[j][0] != roads[j][1], and no two roads are the same unordered pair. -/
theorem spec_4 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads) :
    ∀ r : Std.I64, maximum_importance n roads = Result.ok r →
      3 * (roads.val.length : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads), ∀ r : Std.I64, maximum_importance n roads = Result.ok r →
      3 * (roads.val.length : Int) ≤ r.val) := by
  sorry

/-- whenever the function returns a result r, r <= (2*n - 1) * len(roads).
  Preconditions: 2 <= n <= 50000, 1 <= len(roads) <= 50000, every road has length 2, for every j in 0..len(roads)-1, 0 <= roads[j][0] < n, 0 <= roads[j][1] < n, roads[j][0] != roads[j][1], and no two roads are the same unordered pair. -/
theorem spec_5 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads) :
    ∀ r : Std.I64, maximum_importance n roads = Result.ok r →
      r.val ≤ (2 * n.val - 1) * (roads.val.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads), ∀ r : Std.I64, maximum_importance n roads = Result.ok r →
      r.val ≤ (2 * n.val - 1) * (roads.val.length : Int)) := by
  sorry

/-- whenever the function returns results r1 for (n, roads1) and r2 for (n, roads2), we have r1 = r2.
  Preconditions: for any n, roads1, roads2 satisfying the preconditions of spec_1 with the same n, and such that the multiset of degrees of roads1 equals the multiset of degrees of roads2 (i.e., there is a permutation π of {0,...,n-1} with d1(i) = d2(π(i)) for all i). -/
theorem spec_6 (n : Std.I64) (roads1 roads2 : Slice (alloc.vec.Vec Std.I64))
    (h1 : ValidInput n roads1) (h2 : ValidInput n roads2)
    (hdeg : ∃ π : Int → Int, IsCityPermutation n π ∧
      ∀ i, 0 ≤ i → i < n.val → degree roads1 i = degree roads2 (π i)) :
    ∀ r1 r2 : Std.I64, maximum_importance n roads1 = Result.ok r1 →
      maximum_importance n roads2 = Result.ok r2 → r1 = r2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (roads1 roads2 : Slice (alloc.vec.Vec Std.I64))
    (h1 : ValidInput n roads1) (h2 : ValidInput n roads2)
    (hdeg : ∃ π : Int → Int, IsCityPermutation n π ∧
      ∀ i, 0 ≤ i → i < n.val → degree roads1 i = degree roads2 (π i)), ∀ r1 r2 : Std.I64, maximum_importance n roads1 = Result.ok r1 →
      maximum_importance n roads2 = Result.ok r2 → r1 = r2) := by
  sorry

/-- whenever the function returns results r1 for (n, roads1) and r2 for (n, roads2), we have r1 <= r2.
  Preconditions: for any n, roads1, roads2 satisfying the preconditions of spec_1 with the same n, and such that for every i in 0..n-1, d1(i) <= d2(i) (where d1, d2 are the degree functions of roads1, roads2). -/
theorem spec_7 (n : Std.I64) (roads1 roads2 : Slice (alloc.vec.Vec Std.I64))
    (h1 : ValidInput n roads1) (h2 : ValidInput n roads2)
    (hdeg : ∀ i, 0 ≤ i → i < n.val → degree roads1 i ≤ degree roads2 i) :
    ∀ r1 r2 : Std.I64, maximum_importance n roads1 = Result.ok r1 →
      maximum_importance n roads2 = Result.ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (roads1 roads2 : Slice (alloc.vec.Vec Std.I64))
    (h1 : ValidInput n roads1) (h2 : ValidInput n roads2)
    (hdeg : ∀ i, 0 ≤ i → i < n.val → degree roads1 i ≤ degree roads2 i), ∀ r1 r2 : Std.I64, maximum_importance n roads1 = Result.ok r1 →
      maximum_importance n roads2 = Result.ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- whenever the function returns a result r, let σ be any permutation of {0,...,n-1} such that d(σ(0)) <= d(σ(1)) <= ... <= d(σ(n-1)), where d(i) is the number of roads incident to city i. Define f(σ(k)) = k+1 for k=0..n-1. Then sum_{j=0}^{len(roads)-1} (f(roads[j][0]) + f(roads[j][1])) = r.
  Preconditions: 2 <= n <= 50000, 1 <= len(roads) <= 50000, every road has length 2, for every j in 0..len(roads)-1, 0 <= roads[j][0] < n, 0 <= roads[j][1] < n, roads[j][0] != roads[j][1], and no two roads are the same unordered pair. -/
theorem spec_8 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads) :
    ∀ r : Std.I64, maximum_importance n roads = Result.ok r →
      ∀ σ : Int → Int, IsCityPermutation n σ →
        (∀ a b, 0 ≤ a → a < n.val → 0 ≤ b → b < n.val → a ≤ b →
          degree roads (σ a) ≤ degree roads (σ b)) →
        ∀ f : Int → Int,
          (∀ k, 0 ≤ k → k < n.val → f (σ k) = k + 1) →
          totalImportance roads f = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n roads), ∀ r : Std.I64, maximum_importance n roads = Result.ok r →
      ∀ σ : Int → Int, IsCityPermutation n σ →
        (∀ a b, 0 ≤ a → a < n.val → 0 ≤ b → b < n.val → a ≤ b →
          degree roads (σ a) ≤ degree roads (σ b)) →
        ∀ f : Int → Int,
          (∀ k, 0 ≤ k → k < n.val → f (σ k) = k + 1) →
          totalImportance roads f = r.val) := by
  sorry

end AegisSpec.MaximumImportance
