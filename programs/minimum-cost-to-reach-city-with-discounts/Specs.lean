import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `minimum-cost-to-reach-city-with-discounts`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumCost

def hwInts (h : alloc.vec.Vec Std.I64) : List ℤ := h.val.map (fun x => x.val)

def hwList (highways : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
  highways.val.map hwInts

def HighwayOk (n : ℤ) (e : List ℤ) : Prop :=
  ∃ a b t : ℤ, e = [a, b, t] ∧ 0 ≤ a ∧ a < n ∧ 0 ≤ b ∧ b < n ∧ a ≠ b ∧ 0 ≤ t ∧ t ≤ 100000

def InputConstraints (n : ℤ) (highways : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  2 ≤ n ∧ n ≤ 1000 ∧
  1 ≤ (hwList highways).length ∧ (hwList highways).length ≤ 1000 ∧
  (∀ e ∈ hwList highways, HighwayOk n e) ∧
  (hwList highways).Nodup

def ProblemConstraints (n : ℤ) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : ℤ) : Prop :=
  InputConstraints n highways ∧ 0 ≤ discounts ∧ discounts ≤ 500

def stepToll (p : ℤ × ℤ × List ℤ) : ℤ := p.2.2.getD 2 0

def pathSteps (hw : List (List ℤ)) (vs : List ℤ) (es : List ℕ) : List (ℤ × ℤ × List ℤ) :=
  ((vs.zip vs.tail).zip es).map (fun q => (q.1.1, q.1.2, hw.getD q.2 []))

def IsSimplePath (n : ℤ) (hw : List (List ℤ)) (vs : List ℤ) (es : List ℕ) : Prop :=
  2 ≤ vs.length ∧
  vs.head? = some 0 ∧
  vs.getLast? = some (n - 1) ∧
  vs.Nodup ∧
  es.length + 1 = vs.length ∧
  (∀ i ∈ es, i < hw.length) ∧
  ∀ p ∈ pathSteps hw vs es,
    ∃ a b t : ℤ, p.2.2 = [a, b, t] ∧
      ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a))

def pathCostWith (steps : List (ℤ × ℤ × List ℤ)) (S : Finset ℕ) : ℤ :=
  ((steps.zipIdx).map (fun q => if q.2 ∈ S then stepToll q.1 / 2 else stepToll q.1)).sum

def pathCostHalf (steps : List (ℤ × ℤ × List ℤ)) : ℤ :=
  (steps.map (fun p => stepToll p / 2)).sum

def IsPathCost (d : ℤ) (hw : List (List ℤ)) (vs : List ℤ) (es : List ℕ) (r : ℤ) : Prop :=
  ∃ S : Finset ℕ, (S.card : ℤ) ≤ d ∧ pathCostWith (pathSteps hw vs es) S = r

def HasSimplePath (n : ℤ) (hw : List (List ℤ)) : Prop :=
  ∃ (vs : List ℤ) (es : List ℕ), IsSimplePath n hw vs es

def IsMinimumPathCost (n : ℤ) (hw : List (List ℤ)) (d : ℤ) (m : ℤ) : Prop :=
  (∀ (vs : List ℤ) (es : List ℕ) (S : Finset ℕ),
      IsSimplePath n hw vs es → (S.card : ℤ) ≤ d →
        m ≤ pathCostWith (pathSteps hw vs es) S) ∧
  ∃ (vs : List ℤ) (es : List ℕ), IsSimplePath n hw vs es ∧ IsPathCost d hw vs es m

def IsMinOverPaths (n : ℤ) (hw : List (List ℤ)) (c : List ℤ → List ℕ → ℤ) (m : ℤ) : Prop :=
  (∀ (vs : List ℤ) (es : List ℕ), IsSimplePath n hw vs es → m ≤ c vs es) ∧
  ∃ (vs : List ℤ) (es : List ℕ), IsSimplePath n hw vs es ∧ c vs es = m

def Adj (hw : List (List ℤ)) (u v : ℤ) : Prop :=
  ∃ e ∈ hw, ∃ t : ℤ, e = [u, v, t] ∨ e = [v, u, t]

def Connected (hw : List (List ℤ)) (u v : ℤ) : Prop :=
  Relation.ReflTransGen (Adj hw) u v

def tollsBetween (hw : List (List ℤ)) : List ℤ :=
  hw.filterMap fun e =>
    match e with
    | [a, b, t] => if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then some t else none
    | _ => none

def IsMinOf (l : List ℤ) (m : ℤ) : Prop :=
  (∀ x ∈ l, m ≤ x) ∧ ∃ x ∈ l, m = x

/-- The function returns a result r (it does not fail). A simple path from 0 to n-1 is a sequence of distinct vertices v_0 = 0, v_1, ..., v_k = n-1 with k >= 1, together with highway indices i_1, ..., i_k such that for each j = 1..k, the endpoints of highways[i_j] are {v_{j-1}, v_j}. For such a path and a subset S of {1,...,k} with |S| <= discounts, its cost is sum_{j=1}^k c_j, where c_j = floor(t_{i_j} / 2) if j is in S, and c_j = t_{i_j} if j is not in S, with t_{i_j} = highways[i_j][2]. If no simple path from 0 to n-1 exists, then r = -1. Otherwise, r is the minimum of the costs of all simple paths from 0 to n-1 over all discount subsets S of size at most discounts.
  Preconditions: Interpreting each Std.I64 as its integer value, n, highways, and discounts satisfy the problem constraints: 2 <= n <= 1000; highways is a list with 1 <= len(highways) <= 1000; for every i with 0 <= i < len(highways), highways[i] is a list of exactly 3 integers [a_i, b_i, t_i] with 0 <= a_i < n, 0 <= b_i < n, a_i != b_i, and 0 <= t_i <= 100000; 0 <= discounts <= 500; and there are no duplicate highways (for i != j, highways[i] != highways[j]). -/
theorem spec_1 (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) :
    ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (¬ HasSimplePath n.val (hwList highways) → r.val = -1) ∧
      (HasSimplePath n.val (hwList highways) →
        IsMinimumPathCost n.val (hwList highways) discounts.val r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val), ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (¬ HasSimplePath n.val (hwList highways) → r.val = -1) ∧
      (HasSimplePath n.val (hwList highways) →
        IsMinimumPathCost n.val (hwList highways) discounts.val r.val)) := by
  sorry

/-- The function returns a result r (it does not fail). If r != -1, then 0 <= r <= (n - 1) * 100000. Consequently, r is either -1 or a nonnegative integer, and any nonnegative r fits comfortably in a 64-bit integer.
  Preconditions: Assume n, highways, and discounts satisfy the problem constraints as stated in spec_1: 2 <= n <= 1000; 1 <= len(highways) <= 1000; each highway is [a,b,t] with 0 <= a,b < n, a != b, 0 <= t <= 100000; 0 <= discounts <= 500; no duplicate highways. -/
theorem spec_2 (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) :
    ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (r.val ≠ -1 → 0 ≤ r.val ∧ r.val ≤ (n.val - 1) * 100000) ∧
      (r.val = -1 ∨ 0 ≤ r.val) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val), ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (r.val ≠ -1 → 0 ≤ r.val ∧ r.val ≤ (n.val - 1) * 100000) ∧
      (r.val = -1 ∨ 0 ≤ r.val)) := by
  sorry

/-- The function returns a result r (it does not fail). If no simple path from 0 to n-1 exists, then r = -1. Otherwise, r is the minimum over all simple paths from 0 to n-1 of the sum of the tolls of the highways on the path.
  Preconditions: Assume n, highways, and discounts satisfy the problem constraints as stated in spec_1, and additionally discounts = 0. -/
theorem spec_3 (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) (hd : discounts.val = 0) :
    ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (¬ HasSimplePath n.val (hwList highways) → r.val = -1) ∧
      (HasSimplePath n.val (hwList highways) →
        IsMinOverPaths n.val (hwList highways)
          (fun vs es => pathCostWith (pathSteps (hwList highways) vs es) ∅) r.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) (hd : discounts.val = 0), ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (¬ HasSimplePath n.val (hwList highways) → r.val = -1) ∧
      (HasSimplePath n.val (hwList highways) →
        IsMinOverPaths n.val (hwList highways)
          (fun vs es => pathCostWith (pathSteps (hwList highways) vs es) ∅) r.val)) := by
  sorry

/-- The function returns a result r (it does not fail). If no simple path from 0 to n-1 exists, then r = -1. Otherwise, r is the minimum over all simple paths from 0 to n-1 of the sum over the edges of the path of floor(toll / 2), where toll is the toll of the highway used for that edge.
  Preconditions: Assume n, highways, and discounts satisfy the problem constraints as stated in spec_1, and additionally discounts >= n - 1. -/
theorem spec_4 (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) (hd : n.val - 1 ≤ discounts.val) :
    ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (¬ HasSimplePath n.val (hwList highways) → r.val = -1) ∧
      (HasSimplePath n.val (hwList highways) →
        IsMinOverPaths n.val (hwList highways)
          (fun vs es => pathCostHalf (pathSteps (hwList highways) vs es)) r.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) (hd : n.val - 1 ≤ discounts.val), ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (¬ HasSimplePath n.val (hwList highways) → r.val = -1) ∧
      (HasSimplePath n.val (hwList highways) →
        IsMinOverPaths n.val (hwList highways)
          (fun vs es => pathCostHalf (pathSteps (hwList highways) vs es)) r.val)) := by
  sorry

/-- The function returns a result r (it does not fail). Let T be the set of tolls t such that highways contains a highway with endpoints 0 and 1 and toll t, i.e., T = { t : there exists i with {highways[i][0], highways[i][1]} = {0,1} and highways[i][2] = t }. If T is empty, then r = -1. Otherwise, if discounts >= 1, r = min { floor(t / 2) : t in T }, and if discounts = 0, r = min { t : t in T }.
  Preconditions: Assume n, highways, and discounts satisfy the problem constraints as stated in spec_1, and additionally n = 2. -/
theorem spec_5 (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) (hn : n.val = 2) :
    ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (tollsBetween (hwList highways) = [] → r.val = -1) ∧
      (tollsBetween (hwList highways) ≠ [] →
        (1 ≤ discounts.val →
          IsMinOf ((tollsBetween (hwList highways)).map (fun t => t / 2)) r.val) ∧
        (discounts.val = 0 → IsMinOf (tollsBetween (hwList highways)) r.val)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) (hn : n.val = 2), ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (tollsBetween (hwList highways) = [] → r.val = -1) ∧
      (tollsBetween (hwList highways) ≠ [] →
        (1 ≤ discounts.val →
          IsMinOf ((tollsBetween (hwList highways)).map (fun t => t / 2)) r.val) ∧
        (discounts.val = 0 → IsMinOf (tollsBetween (hwList highways)) r.val))) := by
  sorry

/-- r1 = -1 if and only if r2 = -1. Moreover, if r1 != -1, then r2 != -1 and r2 <= r1.
  Preconditions: Assume n and highways satisfy the problem constraints: 2 <= n <= 1000; 1 <= len(highways) <= 1000; each highway is [a,b,t] with 0 <= a,b < n, a != b, 0 <= t <= 100000; no duplicate highways. Let d1 and d2 be integers with 0 <= d1 <= d2 <= 500. Let r1 be the result of minimum_cost(n, highways, d1) and r2 be the result of minimum_cost(n, highways, d2). Assume both calls return results (they do not fail). -/
theorem spec_6 (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (d1 d2 : Std.I64)
    (h : InputConstraints n.val highways)
    (hd1 : 0 ≤ d1.val) (hd12 : d1.val ≤ d2.val) (hd2 : d2.val ≤ 500) :
    ∀ r1 r2 : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways d1 = ok r1 →
      Aegis.MinimumCost.minimum_cost n highways d2 = ok r2 →
      (r1.val = -1 ↔ r2.val = -1) ∧ (r1.val ≠ -1 → r2.val ≤ r1.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (d1 d2 : Std.I64)
    (h : InputConstraints n.val highways)
    (hd1 : 0 ≤ d1.val) (hd12 : d1.val ≤ d2.val) (hd2 : d2.val ≤ 500), ∀ r1 r2 : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways d1 = ok r1 →
      Aegis.MinimumCost.minimum_cost n highways d2 = ok r2 →
      (r1.val = -1 ↔ r2.val = -1) ∧ (r1.val ≠ -1 → r2.val ≤ r1.val)) := by
  sorry

/-- If r != -1, then r' != -1 and r' <= r. If r = -1, then r' is either -1 or a nonnegative integer.
  Preconditions: Assume n satisfies 2 <= n <= 1000. Let highways and highways' be two lists of highways satisfying the problem constraints (each entry [a,b,t] with 0 <= a,b < n, a != b, 0 <= t <= 100000; no duplicate entries in each list), such that every entry of highways also appears in highways' (i.e., the multiset of entries of highways is a sub-multiset of the entries of highways'). Let discounts satisfy 0 <= discounts <= 500. Let r = minimum_cost(n, highways, discounts) and r' = minimum_cost(n, highways', discounts). Assume both calls return results (they do not fail). -/
theorem spec_7 (n : Std.I64) (highways highways' : Slice (alloc.vec.Vec Std.I64))
    (discounts : Std.I64)
    (h : InputConstraints n.val highways) (h' : InputConstraints n.val highways')
    (hsub : (hwList highways).Subperm (hwList highways'))
    (hd : 0 ≤ discounts.val ∧ discounts.val ≤ 500) :
    ∀ r r' : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r →
      Aegis.MinimumCost.minimum_cost n highways' discounts = ok r' →
      (r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val) ∧
      (r.val = -1 → r'.val = -1 ∨ 0 ≤ r'.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (highways highways' : Slice (alloc.vec.Vec Std.I64))
    (discounts : Std.I64)
    (h : InputConstraints n.val highways) (h' : InputConstraints n.val highways')
    (hsub : (hwList highways).Subperm (hwList highways'))
    (hd : 0 ≤ discounts.val ∧ discounts.val ≤ 500), ∀ r r' : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r →
      Aegis.MinimumCost.minimum_cost n highways' discounts = ok r' →
      (r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val) ∧
      (r.val = -1 → r'.val = -1 ∨ 0 ≤ r'.val)) := by
  sorry

/-- minimum_cost(n, H', discounts) = minimum_cost(n, highways, discounts), provided both calls return results (they do not fail).
  Preconditions: Assume n, highways, and discounts satisfy the problem constraints as stated in spec_1. Let H' be any list that is a permutation of the list highways (same entries, each appearing the same number of times, in a possibly different order). -/
theorem spec_8 (n : Std.I64) (highways H' : Slice (alloc.vec.Vec Std.I64))
    (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) (hperm : H'.val.Perm highways.val) :
    ∀ r r' : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r →
      Aegis.MinimumCost.minimum_cost n H' discounts = ok r' → r' = r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (highways H' : Slice (alloc.vec.Vec Std.I64))
    (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) (hperm : H'.val.Perm highways.val), ∀ r r' : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r →
      Aegis.MinimumCost.minimum_cost n H' discounts = ok r' → r' = r) := by
  sorry

/-- The function returns a result r (it does not fail). If r != -1, then there exists a simple path from 0 to n-1 and a subset S of its edges with |S| <= discounts such that the cost of that path with discounts S (as defined in spec_1) equals r.
  Preconditions: Assume n, highways, and discounts satisfy the problem constraints as stated in spec_1. -/
theorem spec_9 (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) :
    ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (r.val ≠ -1 →
        ∃ (vs : List ℤ) (es : List ℕ),
          IsSimplePath n.val (hwList highways) vs es ∧
          IsPathCost discounts.val (hwList highways) vs es r.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val), ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (r.val ≠ -1 →
        ∃ (vs : List ℤ) (es : List ℕ),
          IsSimplePath n.val (hwList highways) vs es ∧
          IsPathCost discounts.val (hwList highways) vs es r.val)) := by
  sorry

/-- The function returns a result r (it does not fail). If r != -1, then for every simple path from 0 to n-1 and every subset S of its edges with |S| <= discounts, the cost of that path with discounts S (as defined in spec_1) is at least r.
  Preconditions: Assume n, highways, and discounts satisfy the problem constraints as stated in spec_1. -/
theorem spec_10 (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) :
    ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (r.val ≠ -1 →
        ∀ (vs : List ℤ) (es : List ℕ) (S : Finset ℕ),
          IsSimplePath n.val (hwList highways) vs es → (S.card : ℤ) ≤ discounts.val →
          r.val ≤ pathCostWith (pathSteps (hwList highways) vs es) S) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val), ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (r.val ≠ -1 →
        ∀ (vs : List ℤ) (es : List ℕ) (S : Finset ℕ),
          IsSimplePath n.val (hwList highways) vs es → (S.card : ℤ) ≤ discounts.val →
          r.val ≤ pathCostWith (pathSteps (hwList highways) vs es) S)) := by
  sorry

/-- The function returns a result r (it does not fail). Then r = -1 if and only if there is no path from 0 to n-1 in the undirected graph whose vertices are 0,...,n-1 and whose edges are the highways (treating each highway [a,b,t] as an undirected edge between a and b, ignoring tolls and discounts).
  Preconditions: Assume n, highways, and discounts satisfy the problem constraints as stated in spec_1. -/
theorem spec_11 (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val) :
    ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (r.val = -1 ↔ ¬ Connected (hwList highways) 0 (n.val - 1)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64)) (discounts : Std.I64)
    (h : ProblemConstraints n.val highways discounts.val), ∃ r : Std.I64,
      Aegis.MinimumCost.minimum_cost n highways discounts = ok r ∧
      (r.val = -1 ↔ ¬ Connected (hwList highways) 0 (n.val - 1))) := by
  sorry

end AegisSpec.MinimumCost
