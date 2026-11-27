import Aegis.CheckWays.Code.Funs

/-!
# Specifications of `Aegis.CheckWays.check_ways`

LeetCode problem `number-of-ways-to-reconstruct-a-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CheckWays (check_ways)

namespace AegisSpec.CheckWays

def toPairs (pairs : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  pairs.val.map (fun v => v.val.map (fun x => x.val))

def verts (pairs : Slice (alloc.vec.Vec Std.I64)) : Finset Int :=
  (toPairs pairs).flatten.toFinset

def edgeSet (pairs : Slice (alloc.vec.Vec Std.I64)) : Finset (Finset Int) :=
  ((toPairs pairs).map (fun l => l.toFinset)).toFinset

structure WellFormed (pairs : Slice (alloc.vec.Vec Std.I64)) : Prop where

  nonempty : pairs.val ≠ []

  two_elems : ∀ l ∈ toPairs pairs, ∃ x y : Int, l = [x, y] ∧ 1 ≤ x ∧ x < y ∧ y ≤ 500

  distinct : ((toPairs pairs).map (fun l => l.toFinset)).Nodup

def Adj (P : Finset (Finset Int)) (u v : Int) : Prop :=
  u ≠ v ∧ ({u, v} : Finset Int) ∈ P

def IsUniversal (V : Finset Int) (P : Finset (Finset Int)) (v : Int) : Prop :=
  v ∈ V ∧ ∀ u ∈ V, Adj P u v

def HasNoUniversal (V : Finset Int) (P : Finset (Finset Int)) : Prop :=
  ∀ v ∈ V, ∃ u ∈ V, u ≠ v ∧ ({u, v} : Finset Int) ∉ P

def twoSubsets (V : Finset Int) : Finset (Finset Int) :=
  V.powerset.filter (fun s => s.card = 2)

def IsComplete (V : Finset Int) (P : Finset (Finset Int)) : Prop :=
  2 ≤ V.card ∧ P = twoSubsets V

def IsStar (V : Finset Int) (P : Finset (Finset Int)) (c : Int) (L : Finset Int) : Prop :=
  V = insert c L ∧ c ∉ L ∧ 2 ≤ L.card ∧ P = L.image (fun l => ({c, l} : Finset Int))

inductive AncestorOf (E : Finset (Int × Int)) : Int → Int → Prop where
  | of_parent {c p : Int} : (c, p) ∈ E → AncestorOf E p c
  | step {c p a : Int} : (c, p) ∈ E → AncestorOf E a p → AncestorOf E a c

def RootAt (V : Finset Int) (E : Finset (Int × Int)) (r : Int) : Prop :=
  r ∈ V ∧ (∀ c, (c, r) ∉ E) ∧ ∀ v ∈ V, v ≠ r → ∃ p, (v, p) ∈ E

def IsRootedTree (V : Finset Int) (E : Finset (Int × Int)) : Prop :=
  (∀ c p, (c, p) ∈ E → c ∈ V ∧ p ∈ V ∧ c ≠ p) ∧
  (∀ c p q, (c, p) ∈ E → (c, q) ∈ E → p = q) ∧
  (∀ v, ¬ AncestorOf E v v) ∧
  (∃ r, RootAt V E r)

def IsValidTree (V : Finset Int) (P : Finset (Finset Int)) (E : Finset (Int × Int)) : Prop :=
  IsRootedTree V E ∧
    ∀ x ∈ V, ∀ y ∈ V, x ≠ y →
      (({x, y} : Finset Int) ∈ P ↔ AncestorOf E x y ∨ AncestorOf E y x)

noncomputable def trees (V : Finset Int) (P : Finset (Finset Int)) :
    Finset (Finset (Int × Int)) := by
  classical
  exact (V.product V).powerset.filter (fun E => IsValidTree V P E)

noncomputable def numTrees (V : Finset Int) (P : Finset (Finset Int)) : Nat :=
  (trees V P).card

noncomputable def count (pairs : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  numTrees (verts pairs) (edgeSet pairs)

/-- Let V be the set of all values occurring in pairs, and let P = {{x_i,y_i} : 0 <= i < len(pairs)}. Let N be the number of rooted trees T on the vertex set V such that for every two distinct x,y in V, the unordered pair {x,y} belongs to P if and only if x is an ancestor of y or y is an ancestor of x in T. (Here an ancestor of a node is a node on the root-to-node path excluding the node itself; equivalently N is the number of parent maps on V forming a rooted tree with this ancestor-comparability relation.) The function returns a result r and r = 0 if N = 0, r = 1 if N = 1, and r = 2 if N >= 2.
  Preconditions: pairs is nonempty; for every i with 0 <= i < len(pairs), pairs[i] has length 2; writing pairs[i] = [x_i,y_i], 1 <= x_i < y_i <= 500; and the unordered pairs {x_i,y_i} are pairwise distinct. -/
theorem spec_1 (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs) :
    ∃ r : Std.I64, check_ways pairs = ok r ∧
      (count pairs = 0 → r.val = 0) ∧
      (count pairs = 1 → r.val = 1) ∧
      (2 ≤ count pairs → r.val = 2) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs), ∃ r : Std.I64, check_ways pairs = ok r ∧
      (count pairs = 0 → r.val = 0) ∧
      (count pairs = 1 → r.val = 1) ∧
      (2 ≤ count pairs → r.val = 2)) := by
  sorry

/-- The function returns a result r, i.e. it does not fail with arithmetic overflow, out-of-bounds access, or a panic.
  Preconditions: pairs is nonempty; for every i with 0 <= i < len(pairs), pairs[i] has length 2; writing pairs[i] = [x_i,y_i], 1 <= x_i < y_i <= 500; and the unordered pairs {x_i,y_i} are pairwise distinct. -/
theorem spec_2 (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs) :
    ∃ r : Std.I64, check_ways pairs = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs), ∃ r : Std.I64, check_ways pairs = ok r) := by
  sorry

/-- Whenever the function returns a result r, r is one of 0, 1, or 2.
  Preconditions: pairs is nonempty; for every i with 0 <= i < len(pairs), pairs[i] has length 2; writing pairs[i] = [x_i,y_i], 1 <= x_i < y_i <= 500; and the unordered pairs {x_i,y_i} are pairwise distinct. -/
theorem spec_3 (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs) :
    ∀ r : Std.I64, check_ways pairs = ok r → r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs), ∀ r : Std.I64, check_ways pairs = ok r → r.val = 0 ∨ r.val = 1 ∨ r.val = 2) := by
  sorry

/-- The function returns 0.
  Preconditions: pairs is nonempty; for every i with 0 <= i < len(pairs), pairs[i] has length 2; writing pairs[i] = [x_i,y_i], 1 <= x_i < y_i <= 500; and the unordered pairs {x_i,y_i} are pairwise distinct. Let V be the set of all values occurring in pairs, and let P be the set of unordered pairs {x_i,y_i}. The graph G=(V,P) has no universal vertex: for every v in V there exists u in V with u != v and {u,v} not in P. -/
theorem spec_4 (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (hno : HasNoUniversal (verts pairs) (edgeSet pairs)) :
    ∃ r : Std.I64, check_ways pairs = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (hno : HasNoUniversal (verts pairs) (edgeSet pairs)), ∃ r : Std.I64, check_ways pairs = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns 2.
  Preconditions: pairs is nonempty; for every i with 0 <= i < len(pairs), pairs[i] has length 2; writing pairs[i] = [x_i,y_i], 1 <= x_i < y_i <= 500; and the unordered pairs {x_i,y_i} are pairwise distinct. Let V be the set of all values occurring in pairs, and let P be the set of unordered pairs {x_i,y_i}. The graph G=(V,P) is complete: |V| >= 2 and P is the set of all unordered pairs of distinct elements of V. -/
theorem spec_5 (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (hcomplete : IsComplete (verts pairs) (edgeSet pairs)) :
    ∃ r : Std.I64, check_ways pairs = ok r ∧ r.val = 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (hcomplete : IsComplete (verts pairs) (edgeSet pairs)), ∃ r : Std.I64, check_ways pairs = ok r ∧ r.val = 2) := by
  sorry

/-- The function returns 1.
  Preconditions: pairs is nonempty; for every i with 0 <= i < len(pairs), pairs[i] has length 2; writing pairs[i] = [x_i,y_i], 1 <= x_i < y_i <= 500; and the unordered pairs {x_i,y_i} are pairwise distinct. Let V be the set of all values occurring in pairs, and let P be the set of unordered pairs {x_i,y_i}. There is a vertex c and a set L such that V = {c} union L, c is not in L, |L| >= 2, and P = {{c,l} : l in L} with no other pairs. -/
theorem spec_6 (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (c : Int) (L : Finset Int) (hstar : IsStar (verts pairs) (edgeSet pairs) c L) :
    ∃ r : Std.I64, check_ways pairs = ok r ∧ r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (c : Int) (L : Finset Int) (hstar : IsStar (verts pairs) (edgeSet pairs) c L), ∃ r : Std.I64, check_ways pairs = ok r ∧ r.val = 1) := by
  sorry

/-- Let r be the result of check_ways(pairs) and r' be the result of check_ways(pairs'). Both calls return and r = r'.
  Preconditions: Both pairs and pairs' satisfy the problem constraints: each is nonempty, every element is a two-element vector [x,y] with 1 <= x < y <= 500, and all unordered pairs in each slice are pairwise distinct. Moreover, pairs and pairs' contain exactly the same set of unordered pairs, possibly in different orders. -/
theorem spec_7 (pairs pairs' : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (h' : WellFormed pairs') (hsame : edgeSet pairs = edgeSet pairs') :
    ∃ r r' : Std.I64, check_ways pairs = ok r ∧ check_ways pairs' = ok r' ∧ r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (pairs pairs' : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (h' : WellFormed pairs') (hsame : edgeSet pairs = edgeSet pairs'), ∃ r r' : Std.I64, check_ways pairs = ok r ∧ check_ways pairs' = ok r' ∧ r = r') := by
  sorry

/-- Whenever the function returns r = 1, the graph G=(V,P) has exactly one universal vertex: there is a unique v in V such that {v,u} is in P for every u in V with u != v.
  Preconditions: pairs is nonempty; for every i with 0 <= i < len(pairs), pairs[i] has length 2; writing pairs[i] = [x_i,y_i], 1 <= x_i < y_i <= 500; and the unordered pairs {x_i,y_i} are pairwise distinct. Let V be the set of all values occurring in pairs, and let P be the set of unordered pairs {x_i,y_i}. -/
theorem spec_8 (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (r : Std.I64) (hret : check_ways pairs = ok r) (hr : r.val = 1) :
    ∃! v : Int, IsUniversal (verts pairs) (edgeSet pairs) v := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (r : Std.I64) (hret : check_ways pairs = ok r) (hr : r.val = 1), ∃! v : Int, IsUniversal (verts pairs) (edgeSet pairs) v) := by
  sorry

/-- There exist two distinct parent maps on V, both having root u, such that in each resulting rooted tree, for every two distinct x,y in V, the pair {x,y} is in P if and only if x is an ancestor of y or y is an ancestor of x.
  Preconditions: pairs satisfies the problem constraints: it is nonempty, every element is a two-element vector [x,y] with 1 <= x < y <= 500, and all unordered pairs are distinct. Let V be the set of all values occurring in pairs and P the set of unordered pairs from pairs. Suppose the function returns r = 2 and the graph G=(V,P) has exactly one universal vertex u, meaning u is the unique element of V with {u,v} in P for every v in V with v != u. -/
theorem spec_9 (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (r : Std.I64) (hret : check_ways pairs = ok r) (hr : r.val = 2)
    (u : Int) (hu : IsUniversal (verts pairs) (edgeSet pairs) u)
    (hu' : ∀ v : Int, IsUniversal (verts pairs) (edgeSet pairs) v → v = u) :
    ∃ E₁ E₂ : Finset (Int × Int),
      E₁ ≠ E₂ ∧
      IsValidTree (verts pairs) (edgeSet pairs) E₁ ∧
      IsValidTree (verts pairs) (edgeSet pairs) E₂ ∧
      RootAt (verts pairs) E₁ u ∧ RootAt (verts pairs) E₂ u := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (r : Std.I64) (hret : check_ways pairs = ok r) (hr : r.val = 2)
    (u : Int) (hu : IsUniversal (verts pairs) (edgeSet pairs) u)
    (hu' : ∀ v : Int, IsUniversal (verts pairs) (edgeSet pairs) v → v = u), ∃ E₁ E₂ : Finset (Int × Int),
      E₁ ≠ E₂ ∧
      IsValidTree (verts pairs) (edgeSet pairs) E₁ ∧
      IsValidTree (verts pairs) (edgeSet pairs) E₂ ∧
      RootAt (verts pairs) E₁ u ∧ RootAt (verts pairs) E₂ u) := by
  sorry

/-- Then r = 2.
  Preconditions: pairs is nonempty; every pairs[i] has length 2; writing pairs[i]=[x_i,y_i], 1 <= x_i < y_i <= 500; all unordered pairs {x_i,y_i} are distinct. Let V be the occurring values, P the unordered pairs, and suppose G=(V,P) has at least two universal vertices. Suppose check_ways(pairs) returns r with r != 0. -/
theorem spec_10 (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (huni : ∃ u v : Int,
      u ≠ v ∧ IsUniversal (verts pairs) (edgeSet pairs) u ∧
        IsUniversal (verts pairs) (edgeSet pairs) v)
    (r : Std.I64) (hret : check_ways pairs = ok r) (hne : r.val ≠ 0) :
    r.val = 2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (huni : ∃ u v : Int,
      u ≠ v ∧ IsUniversal (verts pairs) (edgeSet pairs) u ∧
        IsUniversal (verts pairs) (edgeSet pairs) v)
    (r : Std.I64) (hret : check_ways pairs = ok r) (hne : r.val ≠ 0), r.val = 2) := by
  sorry

/-- Every rooted tree on V satisfying the ancestor-comparability condition for P has root u; equivalently, all valid trees are rooted at the unique universal vertex u.
  Preconditions: pairs is nonempty; every pairs[i] has length 2; writing pairs[i]=[x_i,y_i], 1 <= x_i < y_i <= 500; all unordered pairs {x_i,y_i} are distinct. Let V be the occurring values and P the unordered pairs. Suppose G=(V,P) has a unique universal vertex u, and suppose check_ways(pairs) returns a nonzero result r. -/
theorem spec_11 (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (u : Int) (hu : IsUniversal (verts pairs) (edgeSet pairs) u)
    (hu' : ∀ v : Int, IsUniversal (verts pairs) (edgeSet pairs) v → v = u)
    (r : Std.I64) (hret : check_ways pairs = ok r) (hne : r.val ≠ 0) :
    ∀ E : Finset (Int × Int),
      IsValidTree (verts pairs) (edgeSet pairs) E → RootAt (verts pairs) E u := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (pairs : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed pairs)
    (u : Int) (hu : IsUniversal (verts pairs) (edgeSet pairs) u)
    (hu' : ∀ v : Int, IsUniversal (verts pairs) (edgeSet pairs) v → v = u)
    (r : Std.I64) (hret : check_ways pairs = ok r) (hne : r.val ≠ 0), ∀ E : Finset (Int × Int),
      IsValidTree (verts pairs) (edgeSet pairs) E → RootAt (verts pairs) E u) := by
  sorry

end AegisSpec.CheckWays
