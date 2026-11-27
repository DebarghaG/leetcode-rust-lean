import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `minimum-cost-for-cutting-cake-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumCost

namespace AegisSpec.MinimumCost

def values (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

def sumVal (l : List Std.I64) : ℤ := (values l).sum

def pairMinSum (h v : List Std.I64) : ℤ :=
  ((h.map (fun x => (v.map (fun y => min x.val y.val)).sum)).sum)

def occursIn (c : ℤ) (h v : List Std.I64) : Prop :=
  (∃ x ∈ h, x.val = c) ∨ (∃ y ∈ v, y.val = c)

def isMinOfEntries (c : ℤ) (h v : List Std.I64) : Prop :=
  occursIn c h v ∧ ∀ z : ℤ, occursIn z h v → c ≤ z

def isMaxOfEntries (c : ℤ) (h v : List Std.I64) : Prop :=
  occursIn c h v ∧ ∀ z : ℤ, occursIn z h v → z ≤ c

def PointwiseGE (a b : List Std.I64) : Prop :=
  List.Forall₂ (fun x y => y.val ≤ x.val) a b

def SomeEntryStrict (a b : List Std.I64) : Prop :=
  ∃ p ∈ a.zip b, p.2.val < p.1.val

/-- The function returns a result r and r = sum_{i=0}^{len(horizontalCut)-1} horizontalCut[i] + sum_{j=0}^{len(verticalCut)-1} verticalCut[j] + sum_{i=0}^{len(horizontalCut)-1} sum_{j=0}^{len(verticalCut)-1} min(horizontalCut[i], verticalCut[j]), where min is the ordinary integer minimum and every sum over an empty index set is 0.
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every 0 <= i < len(horizontalCut); and 1 <= verticalCut[j] <= 1000 for every 0 <= j < len(verticalCut). -/
theorem spec_1 (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000) :
    ∃ r : Std.I64,
      minimum_cost m n horizontalCut verticalCut = ok r ∧
        r.val = sumVal horizontalCut.val + sumVal verticalCut.val
          + pairMinSum horizontalCut.val verticalCut.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000), ∃ r : Std.I64,
      minimum_cost m n horizontalCut verticalCut = ok r ∧
        r.val = sumVal horizontalCut.val + sumVal verticalCut.val
          + pairMinSum horizontalCut.val verticalCut.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not panic, fail due to an out-of-bounds slice access, or overflow the signed 64-bit range.
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every 0 <= i < len(horizontalCut); and 1 <= verticalCut[j] <= 1000 for every 0 <= j < len(verticalCut). -/
theorem spec_2 (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000) :
    ∃ r : Std.I64, minimum_cost m n horizontalCut verticalCut = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000), ∃ r : Std.I64, minimum_cost m n horizontalCut verticalCut = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= sum_{i=0}^{len(horizontalCut)-1} horizontalCut[i] + sum_{j=0}^{len(verticalCut)-1} verticalCut[j].
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every 0 <= i < len(horizontalCut); and 1 <= verticalCut[j] <= 1000 for every 0 <= j < len(verticalCut). -/
theorem spec_3 (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r) :
    sumVal horizontalCut.val + sumVal verticalCut.val ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r), sumVal horizontalCut.val + sumVal verticalCut.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= min( (sum_{i=0}^{len(horizontalCut)-1} horizontalCut[i]) + m * (sum_{j=0}^{len(verticalCut)-1} verticalCut[j]), (sum_{j=0}^{len(verticalCut)-1} verticalCut[j]) + n * (sum_{i=0}^{len(horizontalCut)-1} horizontalCut[i]) ).
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every 0 <= i < len(horizontalCut); and 1 <= verticalCut[j] <= 1000 for every 0 <= j < len(verticalCut). -/
theorem spec_4 (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r) :
    r.val ≤ min
      (sumVal horizontalCut.val + m.val * sumVal verticalCut.val)
      (sumVal verticalCut.val + n.val * sumVal horizontalCut.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r), r.val ≤ min
      (sumVal horizontalCut.val + m.val * sumVal verticalCut.val)
      (sumVal verticalCut.val + n.val * sumVal horizontalCut.val)) := by
  sorry

/-- Let c_min be the minimum of all entries appearing in horizontalCut and verticalCut. Whenever the function returns a result r, r >= (m*n - 1) * c_min.
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every 0 <= i < len(horizontalCut); 1 <= verticalCut[j] <= 1000 for every 0 <= j < len(verticalCut); and m*n > 1. -/
theorem spec_5 (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hpos : 1 < m.val * n.val)
    (c_min : ℤ)
    (hc_min : isMinOfEntries c_min horizontalCut.val verticalCut.val)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r) :
    (m.val * n.val - 1) * c_min ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hpos : 1 < m.val * n.val)
    (c_min : ℤ)
    (hc_min : isMinOfEntries c_min horizontalCut.val verticalCut.val)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r), (m.val * n.val - 1) * c_min ≤ r.val) := by
  sorry

/-- Let c_max be the maximum of all entries appearing in horizontalCut and verticalCut. Whenever the function returns a result r, r <= (m*n - 1) * c_max.
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every 0 <= i < len(horizontalCut); 1 <= verticalCut[j] <= 1000 for every 0 <= j < len(verticalCut); and m*n > 1. -/
theorem spec_6 (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hpos : 1 < m.val * n.val)
    (c_max : ℤ)
    (hc_max : isMaxOfEntries c_max horizontalCut.val verticalCut.val)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r) :
    r.val ≤ (m.val * n.val - 1) * c_max := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hpos : 1 < m.val * n.val)
    (c_max : ℤ)
    (hc_max : isMaxOfEntries c_max horizontalCut.val verticalCut.val)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r), r.val ≤ (m.val * n.val - 1) * c_max) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{j=0}^{len(verticalCut)-1} verticalCut[j].
  Preconditions: m and n are integers with 1 <= m,n <= 100000; m = 1; len(horizontalCut) = m-1; len(verticalCut) = n-1; and 1 <= verticalCut[j] <= 1000 for every 0 <= j < len(verticalCut). -/
theorem spec_7 (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm : m.val = 1)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r) :
    r.val = sumVal verticalCut.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm : m.val = 1)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r), r.val = sumVal verticalCut.val) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i=0}^{len(horizontalCut)-1} horizontalCut[i].
  Preconditions: m and n are integers with 1 <= m,n <= 100000; n = 1; len(horizontalCut) = m-1; len(verticalCut) = n-1; and 1 <= horizontalCut[i] <= 1000 for every 0 <= i < len(horizontalCut). -/
theorem spec_8 (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hn : n.val = 1)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r) :
    r.val = sumVal horizontalCut.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hn : n.val = 1)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r), r.val = sumVal horizontalCut.val) := by
  sorry

/-- Whenever the function returns a result r, r = c * (m*n - 1).
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; and there is an integer c with 1 <= c <= 1000 such that horizontalCut[i] = c for every i and verticalCut[j] = c for every j. -/
theorem spec_9 (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 1000)
    (hHc : ∀ x ∈ horizontalCut.val, x.val = c)
    (hVc : ∀ y ∈ verticalCut.val, y.val = c)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r) :
    r.val = c * (m.val * n.val - 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 1000)
    (hHc : ∀ x ∈ horizontalCut.val, x.val = c)
    (hVc : ∀ y ∈ verticalCut.val, y.val = c)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r), r.val = c * (m.val * n.val - 1)) := by
  sorry

/-- Whenever the function returns a result r, r = horizontalCut[0] + verticalCut[0] + min(horizontalCut[0], verticalCut[0]).
  Preconditions: m and n are integers with m = 2 and n = 2; len(horizontalCut) = 1; len(verticalCut) = 1; 1 <= horizontalCut[0] <= 1000; and 1 <= verticalCut[0] <= 1000. -/
theorem spec_10 (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (a b : Std.I64)
    (hm : m.val = 2) (hn : n.val = 2)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hHa : horizontalCut.val = [a]) (hVb : verticalCut.val = [b])
    (ha : 1 ≤ a.val ∧ a.val ≤ 1000) (hb : 1 ≤ b.val ∧ b.val ≤ 1000)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r) :
    r.val = a.val + b.val + min a.val b.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (a b : Std.I64)
    (hm : m.val = 2) (hn : n.val = 2)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hHa : horizontalCut.val = [a]) (hVb : verticalCut.val = [b])
    (ha : 1 ≤ a.val ∧ a.val ≤ 1000) (hb : 1 ≤ b.val ∧ b.val ≤ 1000)
    (r : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r), r.val = a.val + b.val + min a.val b.val) := by
  sorry

/-- Let H' be any slice of length m-1 whose multiset of entries is a permutation of the multiset of horizontalCut, and let r' be the result of minimum_cost(m,n,H',verticalCut). Whenever both invocations return results r and r', r' = r.
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every i; and 1 <= verticalCut[j] <= 1000 for every j. -/
theorem spec_11 (m n : Std.I64) (horizontalCut verticalCut H' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hlenH' : (H'.val.length : ℤ) = m.val - 1)
    (hperm : List.Perm H'.val horizontalCut.val)
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m n H' verticalCut = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut H' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hlenH' : (H'.val.length : ℤ) = m.val - 1)
    (hperm : List.Perm H'.val horizontalCut.val)
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m n H' verticalCut = ok r'), r'.val = r.val) := by
  sorry

/-- Let V' be any slice of length n-1 whose multiset of entries is a permutation of the multiset of verticalCut, and let r' be the result of minimum_cost(m,n,horizontalCut,V'). Whenever both invocations return results r and r', r' = r.
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every i; and 1 <= verticalCut[j] <= 1000 for every j. -/
theorem spec_12 (m n : Std.I64) (horizontalCut verticalCut V' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hlenV' : (V'.val.length : ℤ) = n.val - 1)
    (hperm : List.Perm V'.val verticalCut.val)
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m n horizontalCut V' = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut V' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hlenV' : (V'.val.length : ℤ) = n.val - 1)
    (hperm : List.Perm V'.val verticalCut.val)
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m n horizontalCut V' = ok r'), r'.val = r.val) := by
  sorry

/-- Let r be the result of minimum_cost(m,n,horizontalCut,verticalCut) and let r_T be the result of minimum_cost(n,m,verticalCut,horizontalCut). Whenever both invocations return results, r = r_T.
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every i; and 1 <= verticalCut[j] <= 1000 for every j. -/
theorem spec_13 (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (r rT : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hrT : minimum_cost n m verticalCut horizontalCut = ok rT) :
    r.val = rT.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (r rT : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hrT : minimum_cost n m verticalCut horizontalCut = ok rT), r.val = rT.val) := by
  sorry

/-- Let r be the result of minimum_cost(m,n,horizontalCut,verticalCut) and let r' be the result of minimum_cost(m,n,H',V'). Whenever both invocations return results, r' > r.
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every i; 1 <= verticalCut[j] <= 1000 for every j. Also, H' and V' are slices with len(H')=m-1, len(V')=n-1, all entries in 1..1000, H'[i] >= horizontalCut[i] for every i, V'[j] >= verticalCut[j] for every j, and at least one of these inequalities is strict. -/
theorem spec_14 (m n : Std.I64) (horizontalCut verticalCut H' V' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hlenH' : (H'.val.length : ℤ) = m.val - 1)
    (hlenV' : (V'.val.length : ℤ) = n.val - 1)
    (hH' : ∀ x ∈ H'.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV' : ∀ y ∈ V'.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hgeH : PointwiseGE H'.val horizontalCut.val)
    (hgeV : PointwiseGE V'.val verticalCut.val)
    (hstrict : SomeEntryStrict H'.val horizontalCut.val ∨
      SomeEntryStrict V'.val verticalCut.val)
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m n H' V' = ok r') :
    r.val < r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut H' V' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hlenH' : (H'.val.length : ℤ) = m.val - 1)
    (hlenV' : (V'.val.length : ℤ) = n.val - 1)
    (hH' : ∀ x ∈ H'.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV' : ∀ y ∈ V'.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (hgeH : PointwiseGE H'.val horizontalCut.val)
    (hgeV : PointwiseGE V'.val verticalCut.val)
    (hstrict : SomeEntryStrict H'.val horizontalCut.val ∨
      SomeEntryStrict V'.val verticalCut.val)
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m n H' V' = ok r'), r.val < r'.val) := by
  sorry

/-- Let H'[i] = k*horizontalCut[i] and V'[j] = k*verticalCut[j]. Let r be the result of minimum_cost(m,n,horizontalCut,verticalCut) and let r' be the result of minimum_cost(m,n,H',V'). Whenever both invocations return results, r' = k*r.
  Preconditions: m and n are integers with 1 <= m,n <= 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every i; 1 <= verticalCut[j] <= 1000 for every j. Also, k is a positive integer such that k*horizontalCut[i] <= 1000 for every i and k*verticalCut[j] <= 1000 for every j. -/
theorem spec_15 (m n : Std.I64) (horizontalCut verticalCut H' V' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (k : ℤ) (hk : 1 ≤ k)
    (hkH : ∀ x ∈ horizontalCut.val, k * x.val ≤ 1000)
    (hkV : ∀ y ∈ verticalCut.val, k * y.val ≤ 1000)
    (hlenH' : (H'.val.length : ℤ) = m.val - 1)
    (hlenV' : (V'.val.length : ℤ) = n.val - 1)
    (hHvals : values H'.val = (values horizontalCut.val).map (fun z => k * z))
    (hVvals : values V'.val = (values verticalCut.val).map (fun z => k * z))
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m n H' V' = ok r') :
    r'.val = k * r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (m n : Std.I64) (horizontalCut verticalCut H' V' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (k : ℤ) (hk : 1 ≤ k)
    (hkH : ∀ x ∈ horizontalCut.val, k * x.val ≤ 1000)
    (hkV : ∀ y ∈ verticalCut.val, k * y.val ≤ 1000)
    (hlenH' : (H'.val.length : ℤ) = m.val - 1)
    (hlenV' : (V'.val.length : ℤ) = n.val - 1)
    (hHvals : values H'.val = (values horizontalCut.val).map (fun z => k * z))
    (hVvals : values V'.val = (values verticalCut.val).map (fun z => k * z))
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m n H' V' = ok r'), r'.val = k * r.val) := by
  sorry

/-- Let H' be the slice obtained by appending c to horizontalCut, and let r' be the result of minimum_cost(m+1,n,H',verticalCut). Let r be the result of minimum_cost(m,n,horizontalCut,verticalCut). Whenever both invocations return results, r' = r + c + sum_{j=0}^{len(verticalCut)-1} min(c, verticalCut[j]).
  Preconditions: m and n are integers with 1 <= m,n <= 100000; m < 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every i; 1 <= verticalCut[j] <= 1000 for every j; and c is an integer with 1 <= c <= 1000. -/
theorem spec_16 (m n m' : Std.I64) (horizontalCut verticalCut H' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000) (hm2' : m.val < 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm' : m'.val = m.val + 1)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 1000)
    (hlenH' : (H'.val.length : ℤ) = m'.val - 1)
    (hHvals : values H'.val = values horizontalCut.val ++ [c])
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m' n H' verticalCut = ok r') :
    r'.val = r.val + c + (verticalCut.val.map (fun y => min c y.val)).sum := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (m n m' : Std.I64) (horizontalCut verticalCut H' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000) (hm2' : m.val < 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm' : m'.val = m.val + 1)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 1000)
    (hlenH' : (H'.val.length : ℤ) = m'.val - 1)
    (hHvals : values H'.val = values horizontalCut.val ++ [c])
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m' n H' verticalCut = ok r'), r'.val = r.val + c + (verticalCut.val.map (fun y => min c y.val)).sum) := by
  sorry

/-- Let V' be the slice obtained by appending c to verticalCut, and let r' be the result of minimum_cost(m,n+1,horizontalCut,V'). Let r be the result of minimum_cost(m,n,horizontalCut,verticalCut). Whenever both invocations return results, r' = r + c + sum_{i=0}^{len(horizontalCut)-1} min(horizontalCut[i], c).
  Preconditions: m and n are integers with 1 <= m,n <= 100000; n < 100000; len(horizontalCut) = m-1; len(verticalCut) = n-1; 1 <= horizontalCut[i] <= 1000 for every i; 1 <= verticalCut[j] <= 1000 for every j; and c is an integer with 1 <= c <= 1000. -/
theorem spec_17 (m n n' : Std.I64) (horizontalCut verticalCut V' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) (hn2' : n.val < 100000)
    (hn' : n'.val = n.val + 1)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 1000)
    (hlenV' : (V'.val.length : ℤ) = n'.val - 1)
    (hVvals : values V'.val = values verticalCut.val ++ [c])
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m n' horizontalCut V' = ok r') :
    r'.val = r.val + c + (horizontalCut.val.map (fun x => min x.val c)).sum := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (m n n' : Std.I64) (horizontalCut verticalCut V' : Slice Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) (hn2' : n.val < 100000)
    (hn' : n'.val = n.val + 1)
    (hlenH : (horizontalCut.val.length : ℤ) = m.val - 1)
    (hlenV : (verticalCut.val.length : ℤ) = n.val - 1)
    (hH : ∀ x ∈ horizontalCut.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hV : ∀ y ∈ verticalCut.val, 1 ≤ y.val ∧ y.val ≤ 1000)
    (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 1000)
    (hlenV' : (V'.val.length : ℤ) = n'.val - 1)
    (hVvals : values V'.val = values verticalCut.val ++ [c])
    (r r' : Std.I64)
    (hr : minimum_cost m n horizontalCut verticalCut = ok r)
    (hr' : minimum_cost m n' horizontalCut V' = ok r'), r'.val = r.val + c + (horizontalCut.val.map (fun x => min x.val c)).sum) := by
  sorry

end AegisSpec.MinimumCost
