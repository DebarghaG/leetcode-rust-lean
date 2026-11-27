import Aegis.MinDistance.Code.Funs
import Mathlib.Data.Real.Basic

/-!
# Specifications of `Aegis.MinDistance.min_distance`

LeetCode problem `allocate-mailboxes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option maxHeartbeats 1000000

namespace AegisSpec.MinDistance

open scoped BigOperators

def nHouses (houses : Slice Std.I64) : ℕ := houses.val.length

def houseVals (houses : Slice Std.I64) : List ℤ := houses.val.map (fun x => x.val)

def kInt (k : Std.I64) : ℤ := k.val

def kNat (k : Std.I64) : ℕ := k.val.toNat

def entry (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def HousesWellFormed (houses : Slice Std.I64) : Prop :=
  (1 ≤ nHouses houses ∧ nHouses houses ≤ 100) ∧
    (∀ x ∈ houses.val, 1 ≤ x.val ∧ x.val ≤ 10000) ∧
    (houseVals houses).Pairwise (· ≠ ·)

def ValidInput (houses : Slice Std.I64) (k : Std.I64) : Prop :=
  HousesWellFormed houses ∧ 1 ≤ kInt k ∧ kInt k ≤ (nHouses houses : ℤ)

noncomputable def nearestDist (x : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, _ => 0
  | (k + 1), m => min |x - m 0| (nearestDist x k fun j => m (j + 1))

noncomputable def totalDistance (houses : Slice Std.I64) (k : ℕ) (m : ℕ → ℝ) : ℝ :=
  ((houseVals houses).map (fun x => nearestDist (x : ℝ) k m)).sum

def minDistToSelection (l : List ℤ) (x : ℤ) : List ℕ → ℤ
  | [] => 0
  | j :: js => js.foldr (fun j' acc => min |x - entry l j'| acc) |x - entry l j|

def selectionCost (houses : Slice Std.I64) (js : List ℕ) : ℤ :=
  ((houseVals houses).map (fun x => minDistToSelection (houseVals houses) x js)).sum

def IsIndexSelection (n k : ℕ) (js : List ℕ) : Prop :=
  js.length = k ∧ js.Pairwise (· < ·) ∧ ∀ j ∈ js, j < n

def IsSortOf (h l : List ℤ) : Prop := h.Perm l ∧ h.Pairwise (· ≤ ·)

noncomputable def segmentCost (h : List ℤ) (a b : ℕ) : ℤ :=
  if a < b then ∑ i ∈ Finset.Ico a b, |entry h i - entry h (a + (b - a - 1) / 2)| else 0

noncomputable def cutCost (h : List ℤ) (p : List ℕ) : ℤ :=
  ((p.zip p.tail).map (fun q : ℕ × ℕ => segmentCost h q.1 q.2)).sum

def IsCutSequence (n k : ℕ) (p : List ℕ) : Prop :=
  p.length = k + 1 ∧ p.head? = some 0 ∧ p.getLast? = some n ∧ p.Pairwise (· ≤ ·)

/-- Whenever min_distance(houses, k) returns a result r, r is the minimum, over all k-tuples (m_1, ..., m_k) of street positions (real numbers; the value is unchanged if positions are restricted to integers or to house locations, and allowing repeated positions does not change the value because k <= n), of the total distance sum_{i=0}^{n-1} min_{1 <= j <= k} |houses[i] - m_j|. In other words, r is the least possible sum, over all houses, of the distance from that house to its nearest of the k allocated mailboxes.
  Preconditions: Let n = len(houses). The preconditions are: 1 <= n <= 100; k, viewed as a mathematical integer, satisfies 1 <= k <= n; for every i with 0 <= i < n, 1 <= houses[i] <= 10000; and houses[i] != houses[j] for all 0 <= i < j < n. All mentioned values are within the 64-bit signed integer range. -/
theorem spec_1 (houses : Slice Std.I64) (k r : Std.I64) (hpre : ValidInput houses k)
    (hres : Aegis.MinDistance.min_distance houses k = ok r) :
    ∃ m : ℕ → ℝ,
      totalDistance houses (kNat k) m = (r.val : ℝ) ∧
        ∀ m' : ℕ → ℝ, (r.val : ℝ) ≤ totalDistance houses (kNat k) m' := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (houses : Slice Std.I64) (k r : Std.I64) (hpre : ValidInput houses k)
    (hres : Aegis.MinDistance.min_distance houses k = ok r), ∃ m : ℕ → ℝ,
      totalDistance houses (kNat k) m = (r.val : ℝ) ∧
        ∀ m' : ℕ → ℝ, (r.val : ℝ) ≤ totalDistance houses (kNat k) m') := by
  sorry

/-- For every input satisfying the preconditions, min_distance(houses, k) returns a result (Result.ok r for some 64-bit integer r); it does not fail, panic, or overflow.
  Preconditions: Let n = len(houses). The preconditions are: 1 <= n <= 100; k, viewed as a mathematical integer, satisfies 1 <= k <= n; for every i with 0 <= i < n, 1 <= houses[i] <= 10000; and houses[i] != houses[j] for all 0 <= i < j < n. All mentioned values are within the 64-bit signed integer range. -/
theorem spec_2 (houses : Slice Std.I64) (k : Std.I64) (hpre : ValidInput houses k) :
    ∃ r : Std.I64, Aegis.MinDistance.min_distance houses k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (houses : Slice Std.I64) (k : Std.I64) (hpre : ValidInput houses k), ∃ r : Std.I64, Aegis.MinDistance.min_distance houses k = ok r) := by
  sorry

/-- Whenever min_distance(houses, k) returns a result r, for every index j with 0 <= j < n, r <= sum_{i=0}^{n-1} |houses[i] - houses[j]|.
  Preconditions: Let n = len(houses). The preconditions are: 1 <= n <= 100; k, viewed as a mathematical integer, satisfies 1 <= k <= n; for every i with 0 <= i < n, 1 <= houses[i] <= 10000; and houses[i] != houses[j] for all 0 <= i < j < n. All mentioned values are within the 64-bit signed integer range. -/
theorem spec_3 (houses : Slice Std.I64) (k r : Std.I64) (hpre : ValidInput houses k)
    (hres : Aegis.MinDistance.min_distance houses k = ok r) :
    ∀ j : ℕ, j < nHouses houses →
      r.val ≤ ((houseVals houses).map (fun x => |x - entry (houseVals houses) j|)).sum := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (houses : Slice Std.I64) (k r : Std.I64) (hpre : ValidInput houses k)
    (hres : Aegis.MinDistance.min_distance houses k = ok r), ∀ j : ℕ, j < nHouses houses →
      r.val ≤ ((houseVals houses).map (fun x => |x - entry (houseVals houses) j|)).sum) := by
  sorry

/-- Whenever min_distance(houses, k) returns a result r, r = 0 if and only if k = n.
  Preconditions: Let n = len(houses). The preconditions are: 1 <= n <= 100; k, viewed as a mathematical integer, satisfies 1 <= k <= n; for every i with 0 <= i < n, 1 <= houses[i] <= 10000; and houses[i] != houses[j] for all 0 <= i < j < n. All mentioned values are within the 64-bit signed integer range. -/
theorem spec_4 (houses : Slice Std.I64) (k r : Std.I64) (hpre : ValidInput houses k)
    (hres : Aegis.MinDistance.min_distance houses k = ok r) :
    (r.val = 0 ↔ kInt k = (nHouses houses : ℤ)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (houses : Slice Std.I64) (k r : Std.I64) (hpre : ValidInput houses k)
    (hres : Aegis.MinDistance.min_distance houses k = ok r), (r.val = 0 ↔ kInt k = (nHouses houses : ℤ))) := by
  sorry

/-- Whenever min_distance(houses, k) returns r and min_distance(houses', k) returns r', we have r = r'.
  Preconditions: Let n = len(houses). The preconditions are: 1 <= n <= 100; k, viewed as a mathematical integer, satisfies 1 <= k <= n; for every i with 0 <= i < n, 1 <= houses[i] <= 10000; and houses[i] != houses[j] for all 0 <= i < j < n. Let houses' be any reordering of the same n house locations; it satisfies the same preconditions. All mentioned values are within the 64-bit signed integer range. -/
theorem spec_5 (houses houses' : Slice Std.I64) (k r r' : Std.I64)
    (hpre : ValidInput houses k) (hpre' : ValidInput houses' k)
    (hperm : (houseVals houses').Perm (houseVals houses))
    (hres : Aegis.MinDistance.min_distance houses k = ok r)
    (hres' : Aegis.MinDistance.min_distance houses' k = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (houses houses' : Slice Std.I64) (k r r' : Std.I64)
    (hpre : ValidInput houses k) (hpre' : ValidInput houses' k)
    (hperm : (houseVals houses').Perm (houseVals houses))
    (hres : Aegis.MinDistance.min_distance houses k = ok r)
    (hres' : Aegis.MinDistance.min_distance houses' k = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever min_distance(houses, k1) returns r1 and min_distance(houses, k2) returns r2, we have r1 >= r2.
  Preconditions: Let n = len(houses). The preconditions are: 1 <= n <= 100; for every i with 0 <= i < n, 1 <= houses[i] <= 10000; and houses[i] != houses[j] for all 0 <= i < j < n. Let k1 and k2 be integers with 1 <= k1 <= k2 <= n. All mentioned values are within the 64-bit signed integer range. -/
theorem spec_6 (houses : Slice Std.I64) (k1 k2 r1 r2 : Std.I64)
    (hhouses : HousesWellFormed houses)
    (hk1 : 1 ≤ kInt k1) (hk12 : kInt k1 ≤ kInt k2)
    (hk2 : kInt k2 ≤ (nHouses houses : ℤ))
    (hres1 : Aegis.MinDistance.min_distance houses k1 = ok r1)
    (hres2 : Aegis.MinDistance.min_distance houses k2 = ok r2) :
    r1.val ≥ r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (houses : Slice Std.I64) (k1 k2 r1 r2 : Std.I64)
    (hhouses : HousesWellFormed houses)
    (hk1 : 1 ≤ kInt k1) (hk12 : kInt k1 ≤ kInt k2)
    (hk2 : kInt k2 ≤ (nHouses houses : ℤ))
    (hres1 : Aegis.MinDistance.min_distance houses k1 = ok r1)
    (hres2 : Aegis.MinDistance.min_distance houses k2 = ok r2), r1.val ≥ r2.val) := by
  sorry

/-- Whenever min_distance(houses, k) returns a result r, there exist k distinct indices j_1 < j_2 < ... < j_k in {0, ..., n-1} such that r = sum_{i=0}^{n-1} min_{1 <= t <= k} |houses[i] - houses[j_t]|.
  Preconditions: Let n = len(houses). The preconditions are: 1 <= n <= 100; k, viewed as a mathematical integer, satisfies 1 <= k <= n; for every i with 0 <= i < n, 1 <= houses[i] <= 10000; and houses[i] != houses[j] for all 0 <= i < j < n. All mentioned values are within the 64-bit signed integer range. -/
theorem spec_7 (houses : Slice Std.I64) (k r : Std.I64) (hpre : ValidInput houses k)
    (hres : Aegis.MinDistance.min_distance houses k = ok r) :
    ∃ js : List ℕ,
      IsIndexSelection (nHouses houses) (kNat k) js ∧ r.val = selectionCost houses js := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (houses : Slice Std.I64) (k r : Std.I64) (hpre : ValidInput houses k)
    (hres : Aegis.MinDistance.min_distance houses k = ok r), ∃ js : List ℕ,
      IsIndexSelection (nHouses houses) (kNat k) js ∧ r.val = selectionCost houses js) := by
  sorry

/-- Whenever min_distance(houses, k) returns a result r, let h be the nondecreasing sort of houses. Then r equals the minimum, over all index sequences 0 = p_0 <= p_1 <= ... <= p_k = n, of sum_{t=1}^{k} cost(p_{t-1}, p_t), where cost(a,b) = 0 if a = b, and if a < b then cost(a,b) = sum_{i=a}^{b-1} |h[i] - h[a + floor((b-a-1)/2)]|.
  Preconditions: Let n = len(houses). The preconditions are: 1 <= n <= 100; k, viewed as a mathematical integer, satisfies 1 <= k <= n; for every i with 0 <= i < n, 1 <= houses[i] <= 10000; and houses[i] != houses[j] for all 0 <= i < j < n. All mentioned values are within the 64-bit signed integer range. -/
theorem spec_8 (houses : Slice Std.I64) (k r : Std.I64) (hpre : ValidInput houses k)
    (hres : Aegis.MinDistance.min_distance houses k = ok r)
    (h : List ℤ) (hsort : IsSortOf h (houseVals houses)) :
    ∃ p : List ℕ,
      IsCutSequence (nHouses houses) (kNat k) p ∧
        r.val = cutCost h p ∧
          ∀ p' : List ℕ,
            IsCutSequence (nHouses houses) (kNat k) p' → r.val ≤ cutCost h p' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (houses : Slice Std.I64) (k r : Std.I64) (hpre : ValidInput houses k)
    (hres : Aegis.MinDistance.min_distance houses k = ok r)
    (h : List ℤ) (hsort : IsSortOf h (houseVals houses)), ∃ p : List ℕ,
      IsCutSequence (nHouses houses) (kNat k) p ∧
        r.val = cutCost h p ∧
          ∀ p' : List ℕ,
            IsCutSequence (nHouses houses) (kNat k) p' → r.val ≤ cutCost h p') := by
  sorry

/-- Whenever min_distance(houses, k) returns r and min_distance(houses', k) returns r', we have r' >= r.
  Preconditions: Let n = len(houses). The preconditions are: 1 <= n <= 100; k, viewed as a mathematical integer, satisfies 1 <= k <= n; for every i with 0 <= i < n, 1 <= houses[i] <= 10000; and houses[i] != houses[j] for all 0 <= i < j < n. Let houses' be a slice of length n+1 containing all elements of houses plus one additional integer x with 1 <= x <= 10000 distinct from every houses[i], so n+1 <= 100. All mentioned values are within the 64-bit signed integer range. -/
theorem spec_9 (houses houses' : Slice Std.I64) (k r r' : Std.I64) (x : ℤ)
    (hpre : ValidInput houses k)
    (hn : nHouses houses + 1 ≤ 100)
    (hperm : (houseVals houses').Perm (houseVals houses ++ [x]))
    (hx_low : 1 ≤ x) (hx_high : x ≤ 10000) (hx_ne : x ∉ houseVals houses)
    (hres : Aegis.MinDistance.min_distance houses k = ok r)
    (hres' : Aegis.MinDistance.min_distance houses' k = ok r') :
    r.val ≥ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (houses houses' : Slice Std.I64) (k r r' : Std.I64) (x : ℤ)
    (hpre : ValidInput houses k)
    (hn : nHouses houses + 1 ≤ 100)
    (hperm : (houseVals houses').Perm (houseVals houses ++ [x]))
    (hx_low : 1 ≤ x) (hx_high : x ≤ 10000) (hx_ne : x ∉ houseVals houses)
    (hres : Aegis.MinDistance.min_distance houses k = ok r)
    (hres' : Aegis.MinDistance.min_distance houses' k = ok r'), r.val ≥ r'.val) := by
  sorry

/-- Whenever min_distance(houses, k) returns r and min_distance(houses', k) returns r', we have r' = c * r.
  Preconditions: Let n = len(houses). The preconditions are: 1 <= n <= 100; k, viewed as a mathematical integer, satisfies 1 <= k <= n; for every i with 0 <= i < n, 1 <= houses[i] <= 10000; and houses[i] != houses[j] for all 0 <= i < j < n. Let c be an integer with c >= 1 such that 1 <= c * houses[i] <= 10000 for every i, and define houses'[i] = c * houses[i]; then houses' also satisfies the same constraints. All mentioned values are within the 64-bit signed integer range. -/
theorem spec_10 (houses houses' : Slice Std.I64) (k r r' : Std.I64) (c : ℤ)
    (hpre : ValidInput houses k)
    (hc : 1 ≤ c)
    (hscale_range : ∀ z ∈ houseVals houses, 1 ≤ c * z ∧ c * z ≤ 10000)
    (hscale : houseVals houses' = (houseVals houses).map (fun z => c * z))
    (hres : Aegis.MinDistance.min_distance houses k = ok r)
    (hres' : Aegis.MinDistance.min_distance houses' k = ok r') :
    r'.val = c * r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (houses houses' : Slice Std.I64) (k r r' : Std.I64) (c : ℤ)
    (hpre : ValidInput houses k)
    (hc : 1 ≤ c)
    (hscale_range : ∀ z ∈ houseVals houses, 1 ≤ c * z ∧ c * z ≤ 10000)
    (hscale : houseVals houses' = (houseVals houses).map (fun z => c * z))
    (hres : Aegis.MinDistance.min_distance houses k = ok r)
    (hres' : Aegis.MinDistance.min_distance houses' k = ok r'), r'.val = c * r.val) := by
  sorry

end AegisSpec.MinDistance
