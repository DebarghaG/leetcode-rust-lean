import Aegis.ClosestCost.Code.Funs

/-!
# Specifications of `Aegis.ClosestCost.closest_cost`

LeetCode problem `closest-dessert-cost`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ClosestCost

open Aegis.ClosestCost

def sliceInts (s : Slice I64) : List Int := s.val.map fun x => x.val

def iabs (x : Int) : Int := if x < 0 then -x else x

def listMin : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl min x

def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

def minBase (baseCosts : Slice I64) : Int := listMin (sliceInts baseCosts)

def maxBase (baseCosts : Slice I64) : Int := listMax (sliceInts baseCosts)

def sumToppings (toppingCosts : Slice I64) : Int := (sliceInts toppingCosts).sum

def minBaseDist (baseCosts : Slice I64) (target : Int) : Int :=
  listMin ((sliceInts baseCosts).map fun b => iabs (b - target))

def maxAttainable (baseCosts toppingCosts : Slice I64) : Int :=
  maxBase baseCosts + 2 * sumToppings toppingCosts

def toppingSums : List Int → List Int
  | [] => [0]
  | t :: ts => (toppingSums ts).flatMap fun s => [s, s + t, s + 2 * t]

def Attainable (baseCosts toppingCosts : Slice I64) (x : Int) : Prop :=
  ∃ b ∈ sliceInts baseCosts, ∃ s ∈ toppingSums (sliceInts toppingCosts), x = b + s

/-- The function returns a result r and the following two properties hold: (1) r is attainable; and (2) for every attainable integer x, either |r - target| < |x - target|, or |r - target| = |x - target| and r <= x. Equivalently, r is the unique attainable cost minimizing the pair (|cost - target|, cost), with the smaller cost selected on ties.
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. All lists are 0-indexed. For 0 <= i < n and counts c_0,...,c_{m-1} in {0,1,2}, write cost(i,c) = baseCosts[i] + sum over j=0 to m-1 of c_j * toppingCosts[j]. Call an integer x attainable if x = cost(i,c) for some such i and c. These bounds imply every cost(i,c) is between 1 and 210000, so no 64-bit overflow occurs in the values discussed. -/
theorem spec_1 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      Attainable baseCosts toppingCosts r.val ∧
        ∀ x, Attainable baseCosts toppingCosts x →
          iabs (r.val - target.val) < iabs (x - target.val) ∨
            (iabs (r.val - target.val) = iabs (x - target.val) ∧ r.val ≤ x) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000), ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      Attainable baseCosts toppingCosts r.val ∧
        ∀ x, Attainable baseCosts toppingCosts x →
          iabs (r.val - target.val) < iabs (x - target.val) ∨
            (iabs (r.val - target.val) = iabs (x - target.val) ∧ r.val ≤ x)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. All lists are 0-indexed. -/
theorem spec_2 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000) :
    ∃ r, closest_cost baseCosts toppingCosts target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000), ∃ r, closest_cost baseCosts toppingCosts target = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= min over i with 0 <= i < n of baseCosts[i].
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. All lists are 0-indexed. For 0 <= i < n and counts c_0,...,c_{m-1} in {0,1,2}, write cost(i,c) = baseCosts[i] + sum over j=0 to m-1 of c_j * toppingCosts[j]. Call an integer x attainable if x = cost(i,c) for some such i and c. -/
theorem spec_3 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r, closest_cost baseCosts toppingCosts target = ok r → minBase baseCosts ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000), ∀ r, closest_cost baseCosts toppingCosts target = ok r → minBase baseCosts ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= max over i with 0 <= i < n of baseCosts[i] + 2 * (sum over j=0 to m-1 of toppingCosts[j]).
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. All lists are 0-indexed. For 0 <= i < n and counts c_0,...,c_{m-1} in {0,1,2}, write cost(i,c) = baseCosts[i] + sum over j=0 to m-1 of c_j * toppingCosts[j]. Call an integer x attainable if x = cost(i,c) for some such i and c. -/
theorem spec_4 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      r.val ≤ maxAttainable baseCosts toppingCosts := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000), ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      r.val ≤ maxAttainable baseCosts toppingCosts) := by
  sorry

/-- Whenever the function returns a result r, |r - target| <= min over i with 0 <= i < n of |baseCosts[i] - target|.
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. All lists are 0-indexed. For 0 <= i < n and counts c_0,...,c_{m-1} in {0,1,2}, write cost(i,c) = baseCosts[i] + sum over j=0 to m-1 of c_j * toppingCosts[j]. Call an integer x attainable if x = cost(i,c) for some such i and c. -/
theorem spec_5 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      iabs (r.val - target.val) ≤ minBaseDist baseCosts target.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000), ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      iabs (r.val - target.val) ≤ minBaseDist baseCosts target.val) := by
  sorry

/-- Whenever the function returns a result r, if target is attainable then r = target.
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. All lists are 0-indexed. For 0 <= i < n and counts c_0,...,c_{m-1} in {0,1,2}, write cost(i,c) = baseCosts[i] + sum over j=0 to m-1 of c_j * toppingCosts[j]. Call an integer x attainable if x = cost(i,c) for some such i and c. -/
theorem spec_6 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      Attainable baseCosts toppingCosts target.val → r.val = target.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000), ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      Attainable baseCosts toppingCosts target.val → r.val = target.val) := by
  sorry

/-- Whenever the function returns a result r, if target <= min over i with 0 <= i < n of baseCosts[i], then r = min over i with 0 <= i < n of baseCosts[i].
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. All lists are 0-indexed. For 0 <= i < n and counts c_0,...,c_{m-1} in {0,1,2}, write cost(i,c) = baseCosts[i] + sum over j=0 to m-1 of c_j * toppingCosts[j]. Call an integer x attainable if x = cost(i,c) for some such i and c. -/
theorem spec_7 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      target.val ≤ minBase baseCosts → r.val = minBase baseCosts := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000), ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      target.val ≤ minBase baseCosts → r.val = minBase baseCosts) := by
  sorry

/-- Whenever the function returns a result r, if target >= max over i with 0 <= i < n of baseCosts[i] + 2 * (sum over j=0 to m-1 of toppingCosts[j]), then r = max over i with 0 <= i < n of baseCosts[i] + 2 * (sum over j=0 to m-1 of toppingCosts[j]).
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. All lists are 0-indexed. For 0 <= i < n and counts c_0,...,c_{m-1} in {0,1,2}, write cost(i,c) = baseCosts[i] + sum over j=0 to m-1 of c_j * toppingCosts[j]. Call an integer x attainable if x = cost(i,c) for some such i and c. -/
theorem spec_8 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      maxAttainable baseCosts toppingCosts ≤ target.val →
        r.val = maxAttainable baseCosts toppingCosts := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000), ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      maxAttainable baseCosts toppingCosts ≤ target.val →
        r.val = maxAttainable baseCosts toppingCosts) := by
  sorry

/-- Whenever the function returns a result r, for every attainable integer x with x < r, we have |r - target| < |x - target|.
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. All lists are 0-indexed. For 0 <= i < n and counts c_0,...,c_{m-1} in {0,1,2}, write cost(i,c) = baseCosts[i] + sum over j=0 to m-1 of c_j * toppingCosts[j]. Call an integer x attainable if x = cost(i,c) for some such i and c. -/
theorem spec_9 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      ∀ x, Attainable baseCosts toppingCosts x → x < r.val →
        iabs (r.val - target.val) < iabs (x - target.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000), ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      ∀ x, Attainable baseCosts toppingCosts x → x < r.val →
        iabs (r.val - target.val) < iabs (x - target.val)) := by
  sorry

/-- For every pair of targets t1 and t2 with 1 <= t1 <= t2 <= 10000, let r1 be the result of closest_cost(baseCosts, toppingCosts, t1) and r2 the result of closest_cost(baseCosts, toppingCosts, t2). Whenever both calls return results, r1 <= r2.
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000. All targets mentioned below are integers in the range 1..10000. All lists are 0-indexed. These bounds imply all totals are within 64-bit range. -/
theorem spec_10 (baseCosts toppingCosts : Slice I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (target1 target2 : I64)
    (htarget1 : 1 ≤ target1.val) (htarget12 : target1.val ≤ target2.val)
    (htarget2 : target2.val ≤ 10000) :
    ∀ r1 r2, closest_cost baseCosts toppingCosts target1 = ok r1 →
      closest_cost baseCosts toppingCosts target2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (target1 target2 : I64)
    (htarget1 : 1 ≤ target1.val) (htarget12 : target1.val ≤ target2.val)
    (htarget2 : target2.val ≤ 10000), ∀ r1 r2, closest_cost baseCosts toppingCosts target1 = ok r1 →
      closest_cost baseCosts toppingCosts target2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever both calls return results, closest_cost(b', toppingCosts, target) = closest_cost(baseCosts, toppingCosts, target).
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. Let b' be any slice of length n whose entries are a permutation of baseCosts; hence b' also satisfies the same price bounds. All lists are 0-indexed. -/
theorem spec_11 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000)
    (baseCosts' : Slice I64)
    (hperm : List.Perm (sliceInts baseCosts') (sliceInts baseCosts)) :
    ∀ r r', closest_cost baseCosts toppingCosts target = ok r →
      closest_cost baseCosts' toppingCosts target = ok r' → r' = r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000)
    (baseCosts' : Slice I64)
    (hperm : List.Perm (sliceInts baseCosts') (sliceInts baseCosts)), ∀ r r', closest_cost baseCosts toppingCosts target = ok r →
      closest_cost baseCosts' toppingCosts target = ok r' → r' = r) := by
  sorry

/-- Whenever both calls return results, closest_cost(baseCosts, t', target) = closest_cost(baseCosts, toppingCosts, target).
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. Let t' be any slice of length m whose entries are a permutation of toppingCosts; hence t' also satisfies the same price bounds. All lists are 0-indexed. -/
theorem spec_12 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000)
    (toppingCosts' : Slice I64)
    (hperm : List.Perm (sliceInts toppingCosts') (sliceInts toppingCosts)) :
    ∀ r r', closest_cost baseCosts toppingCosts target = ok r →
      closest_cost baseCosts toppingCosts' target = ok r' → r' = r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000)
    (toppingCosts' : Slice I64)
    (hperm : List.Perm (sliceInts toppingCosts') (sliceInts toppingCosts)), ∀ r r', closest_cost baseCosts toppingCosts target = ok r →
      closest_cost baseCosts toppingCosts' target = ok r' → r' = r) := by
  sorry

/-- Whenever both calls return results, closest_cost(baseCosts', toppingCosts, target + c) = closest_cost(baseCosts, toppingCosts, target) + c.
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. Let c be an integer such that for every i, 1 <= baseCosts[i] + c <= 10000, and 1 <= target + c <= 10000. Let baseCosts' be the slice with baseCosts'[i] = baseCosts[i] + c. All lists are 0-indexed. -/
theorem spec_13 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000)
    (c : Int) (baseCosts' : Slice I64) (target' : I64)
    (hbase_shift : sliceInts baseCosts' = (sliceInts baseCosts).map (fun b => b + c))
    (htarget_shift : target'.val = target.val + c)
    (hbase'_bnd : ∀ x ∈ sliceInts baseCosts', 1 ≤ x ∧ x ≤ 10000)
    (htarget' : 1 ≤ target'.val ∧ target'.val ≤ 10000) :
    ∀ r r', closest_cost baseCosts toppingCosts target = ok r →
      closest_cost baseCosts' toppingCosts target' = ok r' → r'.val = r.val + c := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000)
    (c : Int) (baseCosts' : Slice I64) (target' : I64)
    (hbase_shift : sliceInts baseCosts' = (sliceInts baseCosts).map (fun b => b + c))
    (htarget_shift : target'.val = target.val + c)
    (hbase'_bnd : ∀ x ∈ sliceInts baseCosts', 1 ≤ x ∧ x ≤ 10000)
    (htarget' : 1 ≤ target'.val ∧ target'.val ≤ 10000), ∀ r r', closest_cost baseCosts toppingCosts target = ok r →
      closest_cost baseCosts' toppingCosts target' = ok r' → r'.val = r.val + c) := by
  sorry

/-- Whenever both calls return results, closest_cost(baseCosts', toppingCosts', k*target) = k * closest_cost(baseCosts, toppingCosts, target).
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. Let k be a positive integer such that for every i, 1 <= k*baseCosts[i] <= 10000; for every j, 1 <= k*toppingCosts[j] <= 10000; and 1 <= k*target <= 10000. Let baseCosts' and toppingCosts' be the slices with baseCosts'[i] = k*baseCosts[i] and toppingCosts'[j] = k*toppingCosts[j]. All lists are 0-indexed. -/
theorem spec_14 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000)
    (k : Int) (hk : 1 ≤ k) (baseCosts' toppingCosts' : Slice I64) (target' : I64)
    (hbase_scale : sliceInts baseCosts' = (sliceInts baseCosts).map (fun b => k * b))
    (htop_scale : sliceInts toppingCosts' = (sliceInts toppingCosts).map (fun t => k * t))
    (htarget_scale : target'.val = k * target.val)
    (hbase'_bnd : ∀ x ∈ sliceInts baseCosts', 1 ≤ x ∧ x ≤ 10000)
    (htop'_bnd : ∀ x ∈ sliceInts toppingCosts', 1 ≤ x ∧ x ≤ 10000)
    (htarget' : 1 ≤ target'.val ∧ target'.val ≤ 10000) :
    ∀ r r', closest_cost baseCosts toppingCosts target = ok r →
      closest_cost baseCosts' toppingCosts' target' = ok r' → r'.val = k * r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000)
    (k : Int) (hk : 1 ≤ k) (baseCosts' toppingCosts' : Slice I64) (target' : I64)
    (hbase_scale : sliceInts baseCosts' = (sliceInts baseCosts).map (fun b => k * b))
    (htop_scale : sliceInts toppingCosts' = (sliceInts toppingCosts).map (fun t => k * t))
    (htarget_scale : target'.val = k * target.val)
    (hbase'_bnd : ∀ x ∈ sliceInts baseCosts', 1 ≤ x ∧ x ≤ 10000)
    (htop'_bnd : ∀ x ∈ sliceInts toppingCosts', 1 ≤ x ∧ x ≤ 10000)
    (htarget' : 1 ≤ target'.val ∧ target'.val ≤ 10000), ∀ r r', closest_cost baseCosts toppingCosts target = ok r →
      closest_cost baseCosts' toppingCosts' target' = ok r' → r'.val = k * r.val) := by
  sorry

/-- Whenever the function returns a result r, for every attainable integer x, if r < x then target < x.
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. All lists are 0-indexed. For 0 <= i < n and counts c_0,...,c_{m-1} in {0,1,2}, write cost(i,c) = baseCosts[i] + sum over j=0 to m-1 of c_j * toppingCosts[j]. Call an integer x attainable if x = cost(i,c) for some such i and c. -/
theorem spec_15 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      ∀ x, Attainable baseCosts toppingCosts x → r.val < x → target.val < x := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000), ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      ∀ x, Attainable baseCosts toppingCosts x → r.val < x → target.val < x) := by
  sorry

/-- Whenever the function returns a result r, for every attainable integer x, if x < r then x < target.
  Preconditions: Let n = len(baseCosts) and m = len(toppingCosts). 1 <= n <= 10, 1 <= m <= 10; for every i with 0 <= i < n, 1 <= baseCosts[i] <= 10000; for every j with 0 <= j < m, 1 <= toppingCosts[j] <= 10000; and 1 <= target <= 10000. All lists are 0-indexed. For 0 <= i < n and counts c_0,...,c_{m-1} in {0,1,2}, write cost(i,c) = baseCosts[i] + sum over j=0 to m-1 of c_j * toppingCosts[j]. Call an integer x attainable if x = cost(i,c) for some such i and c. -/
theorem spec_16 (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      ∀ x, Attainable baseCosts toppingCosts x → x < r.val → x < target.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (baseCosts toppingCosts : Slice I64) (target : I64)
    (hbase_pos : 1 ≤ baseCosts.val.length) (hbase_le : baseCosts.val.length ≤ 10)
    (htop_pos : 1 ≤ toppingCosts.val.length) (htop_le : toppingCosts.val.length ≤ 10)
    (hbase_bnd : ∀ x ∈ sliceInts baseCosts, 1 ≤ x ∧ x ≤ 10000)
    (htop_bnd : ∀ x ∈ sliceInts toppingCosts, 1 ≤ x ∧ x ≤ 10000)
    (htarget : 1 ≤ target.val ∧ target.val ≤ 10000), ∀ r, closest_cost baseCosts toppingCosts target = ok r →
      ∀ x, Attainable baseCosts toppingCosts x → x < r.val → x < target.val) := by
  sorry

end AegisSpec.ClosestCost
