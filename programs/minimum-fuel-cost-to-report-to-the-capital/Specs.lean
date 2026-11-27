import Aegis.MinimumFuelCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumFuelCost.minimum_fuel_cost`

LeetCode problem `minimum-fuel-cost-to-report-to-the-capital`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumFuelCost

namespace AegisSpec.MinimumFuelCost

def nVerts (roads : Slice (alloc.vec.Vec Std.I64)) : ℕ := roads.val.length + 1

def roadLen (roads : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : Option ℕ :=
  (roads.val[k]?).map fun v => v.slice.val.length

def roadEntry (roads : Slice (alloc.vec.Vec Std.I64)) (k i : ℕ) : Option ℤ :=
  (roads.val[k]?).bind fun v => (v.slice.val[i]?).map fun x => x.val

def roadEnds (roads : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : Option (ℕ × ℕ) :=
  match roadEntry roads k 0, roadEntry roads k 1 with
  | some a, some b => some (a.toNat, b.toNat)
  | _, _ => none

def RoadsOk (roads : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ k : ℕ, k < roads.val.length →
    ∃ a b : ℤ, roadLen roads k = some 2 ∧
      roadEntry roads k 0 = some a ∧ roadEntry roads k 1 = some b ∧
      0 ≤ a ∧ a < (nVerts roads : ℤ) ∧ 0 ≤ b ∧ b < (nVerts roads : ℤ) ∧ a ≠ b

def Adj (roads : Slice (alloc.vec.Vec Std.I64)) (u v : ℕ) : Prop :=
  ∃ k : ℕ, k < roads.val.length ∧
    (roadEnds roads k = some (u, v) ∨ roadEnds roads k = some (v, u))

def Reach (roads : Slice (alloc.vec.Vec Std.I64)) (u v : ℕ) : Prop :=
  Relation.ReflTransGen (Adj roads) u v

def edgeSet (roads : Slice (alloc.vec.Vec Std.I64)) : List (ℕ × ℕ) :=
  (List.range roads.val.length).filterMap fun k =>
    (roadEnds roads k).map fun p => if p.1 ≤ p.2 then p else (p.2, p.1)

def IsTree (roads : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  (∀ u : ℕ, u < nVerts roads → Reach roads 0 u) ∧
    (edgeSet roads).Nodup ∧ (edgeSet roads).length = nVerts roads - 1

def IsStar (roads : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ k : ℕ, k < roads.val.length →
    ∃ a b : ℕ, roadEnds roads k = some (a, b) ∧ (a = 0 ∨ b = 0)

def IsPathGraph (roads : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  RoadsOk roads ∧ (edgeSet roads).Nodup ∧
    (∀ k : ℕ, k < roads.val.length →
      ∃ i : ℕ, i + 1 < nVerts roads ∧
        (roadEnds roads k = some (i, i + 1) ∨ roadEnds roads k = some (i + 1, i))) ∧
    (∀ i : ℕ, i + 1 < nVerts roads →
      ∃ k : ℕ, k < roads.val.length ∧
        (roadEnds roads k = some (i, i + 1) ∨ roadEnds roads k = some (i + 1, i)))

def AdjExcept (roads : Slice (alloc.vec.Vec Std.I64)) (a b u v : ℕ) : Prop :=
  Adj roads u v ∧ ¬((u = a ∧ v = b) ∨ (u = b ∧ v = a))

def ReachExcept (roads : Slice (alloc.vec.Vec Std.I64)) (a b u v : ℕ) : Prop :=
  Relation.ReflTransGen (AdjExcept roads a b) u v

noncomputable def cutComponentSize (roads : Slice (alloc.vec.Vec Std.I64)) (a b : ℕ) : ℕ :=
  by
  classical
  exact
    ((List.range (nVerts roads)).filter fun u =>
      decide (u ≠ 0 ∧ ¬ReachExcept roads a b 0 u)).length

noncomputable def edgeComponentSize (roads : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : ℕ :=
  match roadEnds roads k with
  | some (a, b) => cutComponentSize roads a b
  | none => 0

def IsWalkFrom (roads : Slice (alloc.vec.Vec Std.I64)) : ℕ → List ℕ → Prop
  | _, [] => True
  | u, v :: vs => Adj roads u v ∧ IsWalkFrom roads v vs

def WalkTo (roads : Slice (alloc.vec.Vec Std.I64)) (u v : ℕ) (path : List ℕ) : Prop :=
  path.head? = some u ∧ path.getLast? = some v ∧ IsWalkFrom roads u path.tail

noncomputable def dist (roads : Slice (alloc.vec.Vec Std.I64)) (u v : ℕ) : ℕ :=
  by
  classical
  exact
    if h : ∃ m : ℕ, ∃ path : List ℕ, WalkTo roads u v path ∧ path.length = m + 1 then
      Nat.find h
    else 0

noncomputable def distSum (roads : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
  ((List.range (nVerts roads)).map fun u => dist roads 0 u).sum

def ceilDiv (c : ℕ) (s : ℤ) : ℤ := if 0 < s then ((c : ℤ) + s - 1) / s else 0

noncomputable def specCost (roads : Slice (alloc.vec.Vec Std.I64)) (seats : ℤ) : ℤ :=
  ((List.range roads.val.length).map fun k => ceilDiv (edgeComponentSize roads k) seats).sum

/-- The function returns a result r, and r is the minimum number of liters of fuel needed for all representatives to reach city 0, equivalently r = sum_{k=0}^{len(roads)-1} ceil(c_k / seats), where c_k is the number of vertices u in {0,...,n-1} such that the unique simple path in G from u to 0 uses the undirected edge {roads[k][0], roads[k][1]}; this c_k is the size of the component of G with that edge removed that does not contain 0. For len(roads)=0 the sum is empty and equals 0.
  Preconditions: Let n = len(roads) + 1. The problem constraints hold: 1 <= n <= 100000 (so 0 <= len(roads) <= 99999) and 1 <= seats <= 100000. For every k with 0 <= k < len(roads), len(roads[k]) = 2, 0 <= roads[k][0] < n, 0 <= roads[k][1] < n, and roads[k][0] != roads[k][1]. The undirected graph G with vertices {0,...,n-1} and edges {roads[k][0], roads[k][1]} for 0 <= k < len(roads) is a tree (connected and acyclic). -/
theorem spec_1 (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads) :
    ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r ∧ r.val = specCost roads seats.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads), ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r ∧ r.val = specCost roads seats.val) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, access roads out of bounds, or overflow in producing the returned result.
  Preconditions: Let n = len(roads) + 1. The problem constraints hold: 1 <= n <= 100000 and 1 <= seats <= 100000. For every k with 0 <= k < len(roads), len(roads[k]) = 2, 0 <= roads[k][0] < n, 0 <= roads[k][1] < n, and roads[k][0] != roads[k][1]. The undirected graph G with vertices {0,...,n-1} and edges {roads[k][0], roads[k][1]} is a tree. -/
theorem spec_2 (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads) :
    ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads), ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= len(roads).
  Preconditions: Let n = len(roads) + 1. The problem constraints hold: 1 <= n <= 100000 and 1 <= seats <= 100000. For every k with 0 <= k < len(roads), len(roads[k]) = 2, 0 <= roads[k][0] < n, 0 <= roads[k][1] < n, and roads[k][0] != roads[k][1]. The undirected graph G with vertices {0,...,n-1} and edges {roads[k][0], roads[k][1]} is a tree. -/
theorem spec_3 (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads) :
    ∀ r : Std.I64, minimum_fuel_cost roads seats = ok r → (roads.val.length : ℤ) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads), ∀ r : Std.I64, minimum_fuel_cost roads seats = ok r → (roads.val.length : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{u=0}^{n-1} dist_G(0,u), where dist_G(0,u) is the number of edges on the unique simple path in G from 0 to u, with dist_G(0,0)=0.
  Preconditions: Let n = len(roads) + 1. The problem constraints hold: 1 <= n <= 100000 and 1 <= seats <= 100000. For every k with 0 <= k < len(roads), len(roads[k]) = 2, 0 <= roads[k][0] < n, 0 <= roads[k][1] < n, and roads[k][0] != roads[k][1]. The undirected graph G with vertices {0,...,n-1} and edges {roads[k][0], roads[k][1]} is a tree. -/
theorem spec_4 (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads) :
    ∀ r : Std.I64, minimum_fuel_cost roads seats = ok r → r.val ≤ (distSum roads : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads), ∀ r : Std.I64, minimum_fuel_cost roads seats = ok r → r.val ≤ (distSum roads : ℤ)) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: roads = [] and 1 <= seats <= 100000. Thus n = len(roads) + 1 = 1, and G is the single-vertex tree {0}. -/
theorem spec_5 (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000) (hempty : roads.val = []) :
    ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000) (hempty : roads.val = []), ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: len(roads) = 1, n = len(roads) + 1 = 2, and 1 <= seats <= 100000. The unique road has endpoints 0 and 1, in either order, so G is the two-vertex tree. -/
theorem spec_6 (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hlen : roads.val.length = 1)
    (hroadlen : roadLen roads 0 = some 2)
    (hroad : roadEnds roads 0 = some (0, 1) ∨ roadEnds roads 0 = some (1, 0)) :
    ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r ∧ r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hlen : roads.val.length = 1)
    (hroadlen : roadLen roads 0 = some 2)
    (hroad : roadEnds roads 0 = some (0, 1) ∨ roadEnds roads 0 = some (1, 0)), ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r ∧ r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, r = len(roads) if and only if for every k with 0 <= k < len(roads), c_k <= seats, where c_k is the size of the component of G with edge {roads[k][0], roads[k][1]} removed that does not contain 0.
  Preconditions: Let n = len(roads) + 1. The problem constraints hold: 1 <= n <= 100000 and 1 <= seats <= 100000. For every k with 0 <= k < len(roads), len(roads[k]) = 2, 0 <= roads[k][0] < n, 0 <= roads[k][1] < n, and roads[k][0] != roads[k][1]. The undirected graph G with vertices {0,...,n-1} and edges {roads[k][0], roads[k][1]} is a tree. -/
theorem spec_7 (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads) :
    ∀ r : Std.I64, minimum_fuel_cost roads seats = ok r →
      (r.val = (roads.val.length : ℤ) ↔
        ∀ k : ℕ, k < roads.val.length → (edgeComponentSize roads k : ℤ) ≤ seats.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads), ∀ r : Std.I64, minimum_fuel_cost roads seats = ok r →
      (r.val = (roads.val.length : ℤ) ↔
        ∀ k : ℕ, k < roads.val.length → (edgeComponentSize roads k : ℤ) ≤ seats.val)) := by
  sorry

/-- The function returns a result r and r = sum_{u=0}^{n-1} dist_G(0,u), where dist_G(0,u) is the number of edges on the unique simple path in G from 0 to u, with dist_G(0,0)=0.
  Preconditions: Let n = len(roads) + 1. The problem constraints hold: 1 <= n <= 100000 and seats = 1. For every k with 0 <= k < len(roads), len(roads[k]) = 2, 0 <= roads[k][0] < n, 0 <= roads[k][1] < n, and roads[k][0] != roads[k][1]. The undirected graph G with vertices {0,...,n-1} and edges {roads[k][0], roads[k][1]} is a tree. -/
theorem spec_8 (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : seats.val = 1)
    (hroads : RoadsOk roads) (htree : IsTree roads) :
    ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r ∧ r.val = (distSum roads : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : seats.val = 1)
    (hroads : RoadsOk roads) (htree : IsTree roads), ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r ∧ r.val = (distSum roads : ℤ)) := by
  sorry

/-- If minimum_fuel_cost(roads, s1) returns r1 and minimum_fuel_cost(roads, s2) returns r2, then r1 >= r2.
  Preconditions: Let n = len(roads) + 1. The problem constraints hold: 1 <= n <= 100000. For every k with 0 <= k < len(roads), len(roads[k]) = 2, 0 <= roads[k][0] < n, 0 <= roads[k][1] < n, and roads[k][0] != roads[k][1]. The undirected graph G with vertices {0,...,n-1} and edges {roads[k][0], roads[k][1]} is a tree. Let s1 and s2 be integers with 1 <= s1 <= s2 <= 100000. -/
theorem spec_9 (roads : Slice (alloc.vec.Vec Std.I64)) (s1 s2 : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads)
    (hs1 : 1 ≤ s1.val) (hs12 : s1.val ≤ s2.val) (hs2 : s2.val ≤ 100000) :
    ∀ r1 r2 : Std.I64,
      minimum_fuel_cost roads s1 = ok r1 → minimum_fuel_cost roads s2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (s1 s2 : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads)
    (hs1 : 1 ≤ s1.val) (hs12 : s1.val ≤ s2.val) (hs2 : s2.val ≤ 100000), ∀ r1 r2 : Std.I64,
      minimum_fuel_cost roads s1 = ok r1 → minimum_fuel_cost roads s2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if len(roads) = 0.
  Preconditions: Let n = len(roads) + 1. The problem constraints hold: 1 <= n <= 100000 and 1 <= seats <= 100000. For every k with 0 <= k < len(roads), len(roads[k]) = 2, 0 <= roads[k][0] < n, 0 <= roads[k][1] < n, and roads[k][0] != roads[k][1]. The undirected graph G with vertices {0,...,n-1} and edges {roads[k][0], roads[k][1]} is a tree. -/
theorem spec_10 (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads) :
    ∀ r : Std.I64, minimum_fuel_cost roads seats = ok r →
      (r.val = 0 ↔ roads.val.length = 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads), ∀ r : Std.I64, minimum_fuel_cost roads seats = ok r →
      (r.val = 0 ↔ roads.val.length = 0)) := by
  sorry

/-- The function returns a result r and r = len(roads).
  Preconditions: Let n = len(roads) + 1. The problem constraints hold: 1 <= n <= 100000 and 1 <= seats <= 100000. For every k with 0 <= k < len(roads), len(roads[k]) = 2, 0 <= roads[k][0] < n, 0 <= roads[k][1] < n, and roads[k][0] != roads[k][1]. The undirected graph G with vertices {0,...,n-1} and edges {roads[k][0], roads[k][1]} is a tree, and every road has 0 as one of its endpoints (so G is a star centered at 0). -/
theorem spec_11 (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads) (hstar : IsStar roads) :
    ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r ∧ r.val = (roads.val.length : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads : RoadsOk roads) (htree : IsTree roads) (hstar : IsStar roads), ∃ r : Std.I64, minimum_fuel_cost roads seats = ok r ∧ r.val = (roads.val.length : ℤ)) := by
  sorry

/-- The function returns a result r and r = n*(n-1)/2.
  Preconditions: Let n = len(roads) + 1. The problem constraints hold: 1 <= n <= 100000 and seats = 1. The edges in roads are exactly the n-1 undirected pairs {i,i+1} for i = 0,...,n-2, each appearing once regardless of order or endpoint orientation, so G is the path 0-1-2-...-(n-1). -/
theorem spec_12 (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : seats.val = 1) (hpath : IsPathGraph roads) :
    ∃ r : Std.I64,
      minimum_fuel_cost roads seats = ok r ∧
        r.val = ((nVerts roads * (nVerts roads - 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (roads : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn : 1 ≤ nVerts roads ∧ nVerts roads ≤ 100000)
    (hseats : seats.val = 1) (hpath : IsPathGraph roads), ∃ r : Std.I64,
      minimum_fuel_cost roads seats = ok r ∧
        r.val = ((nVerts roads * (nVerts roads - 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- If minimum_fuel_cost(roads1, seats) returns r1 and minimum_fuel_cost(roads2, seats) returns r2, then r1 = r2.
  Preconditions: roads1 and roads2 are two lists satisfying the valid-tree preconditions, with the same n = len(roads1) + 1 = len(roads2) + 1, and they define the same undirected edge set on vertices {0,...,n-1}. The constraints 1 <= n <= 100000 and 1 <= seats <= 100000 hold. -/
theorem spec_13 (roads1 roads2 : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn1 : 1 ≤ nVerts roads1 ∧ nVerts roads1 ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads1 : RoadsOk roads1) (htree1 : IsTree roads1)
    (hroads2 : RoadsOk roads2) (htree2 : IsTree roads2)
    (hn2 : nVerts roads2 = nVerts roads1)
    (hsame : ∀ u v : ℕ, u < nVerts roads1 → v < nVerts roads1 →
      (Adj roads1 u v ↔ Adj roads2 u v)) :
    ∀ r1 r2 : Std.I64,
      minimum_fuel_cost roads1 seats = ok r1 → minimum_fuel_cost roads2 seats = ok r2 →
        r1.val = r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (roads1 roads2 : Slice (alloc.vec.Vec Std.I64)) (seats : Std.I64)
    (hn1 : 1 ≤ nVerts roads1 ∧ nVerts roads1 ≤ 100000)
    (hseats : 1 ≤ seats.val ∧ seats.val ≤ 100000)
    (hroads1 : RoadsOk roads1) (htree1 : IsTree roads1)
    (hroads2 : RoadsOk roads2) (htree2 : IsTree roads2)
    (hn2 : nVerts roads2 = nVerts roads1)
    (hsame : ∀ u v : ℕ, u < nVerts roads1 → v < nVerts roads1 →
      (Adj roads1 u v ↔ Adj roads2 u v)), ∀ r1 r2 : Std.I64,
      minimum_fuel_cost roads1 seats = ok r1 → minimum_fuel_cost roads2 seats = ok r2 →
        r1.val = r2.val) := by
  sorry

end AegisSpec.MinimumFuelCost
