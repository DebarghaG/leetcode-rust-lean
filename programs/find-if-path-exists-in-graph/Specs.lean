import Aegis.ValidPath.Code.Funs

/-!
# Specifications of `Aegis.ValidPath.valid_path`

LeetCode problem `find-if-path-exists-in-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ValidPath

open Aegis.ValidPath

def edgeAt (edges : Slice (alloc.vec.Vec I64)) (i : Nat) : List Int :=
  match edges.val[i]? with
  | none => []
  | some e => e.val.map (fun x => x.val)

def SameUnorderedPair (l₁ l₂ : List Int) : Prop :=
  l₁ = l₂ ∨ l₁ = l₂.reverse

def InBounds (n : Int) (x : Int) : Prop :=
  0 ≤ x ∧ x < n

def GraphPre (n : I64) (edges : Slice (alloc.vec.Vec I64)) : Prop :=
  1 ≤ n.val ∧ n.val ≤ 200000 ∧ edges.val.length ≤ 200000 ∧
    (∀ i : Nat, i < edges.val.length →
      ∃ a b : Int, edgeAt edges i = [a, b] ∧ InBounds n.val a ∧ InBounds n.val b ∧
        a ≠ b) ∧
    (∀ i : Nat, ∀ j : Nat, i < j → j < edges.val.length → ∀ a b c d : Int,
      edgeAt edges i = [a, b] → edgeAt edges j = [c, d] →
        ¬((a = c ∧ b = d) ∨ (a = d ∧ b = c)))

def Adj (edges : Slice (alloc.vec.Vec I64)) (u v : Int) : Prop :=
  ∃ i : Nat, i < edges.val.length ∧ SameUnorderedPair [u, v] (edgeAt edges i)

def Walk (n : Int) (edges : Slice (alloc.vec.Vec I64)) (source destination : Int) :
    Prop :=
  ∃ (m : Nat) (v : Nat → Int),
    v 0 = source ∧ v m = destination ∧
      (∀ j : Nat, j ≤ m → InBounds n (v j)) ∧
      (∀ j : Nat, j < m → Adj edges (v j) (v (j + 1)))

def WalkSimple (n : Int) (edges : Slice (alloc.vec.Vec I64)) (source destination : Int) :
    Prop :=
  ∃ (m : Nat) (v : Nat → Int),
    v 0 = source ∧ v m = destination ∧
      (∀ j : Nat, j ≤ m → InBounds n (v j)) ∧
      (∀ j : Nat, j < m → Adj edges (v j) (v (j + 1))) ∧
      (∀ i : Nat, ∀ j : Nat, i ≤ m → j ≤ m → v i = v j → i = j)

def EdgeIncl (edges edges' : Slice (alloc.vec.Vec I64)) : Prop :=
  ∀ i : Nat, i < edges.val.length →
    ∃ j : Nat, j < edges'.val.length ∧ SameUnorderedPair (edgeAt edges i) (edgeAt edges' j)

def EdgeFlipped (edges edges' : Slice (alloc.vec.Vec I64)) : Prop :=
  edges'.val.length = edges.val.length ∧
    ∀ i : Nat, i < edges.val.length → SameUnorderedPair (edgeAt edges i) (edgeAt edges' i)

/-- Whenever valid_path n edges source destination returns a result r, r = true if and only if there exist an integer m >= 0 and vertices v_0, ..., v_m such that (1) 0 <= v_j < n for every j with 0 <= j <= m, (2) v_0 = source, (3) v_m = destination, and (4) for every j with 0 <= j < m, the unordered pair {v_j, v_{j+1}} equals the unordered pair {edges[i][0], edges[i][1]} for some i with 0 <= i < len(edges). Equivalently, r = false exactly when no such sequence exists.
  Preconditions: 1 <= n <= 200000; 0 <= len(edges) <= 200000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is not equal to the unordered pair {edges[j][0], edges[j][1]}; and 0 <= source < n and 0 <= destination < n. -/
theorem spec_1 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val) (r : Bool)
    (hres : valid_path n edges source destination = ok r) :
    (r = true ↔ Walk n.val edges source.val destination.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val) (r : Bool)
    (hres : valid_path n edges source destination = ok r), (r = true ↔ Walk n.val edges source.val destination.val)) := by
  sorry

/-- For every n, edges, source, destination satisfying the preconditions, valid_path n edges source destination returns a result (Ok true or Ok false); it does not fail by arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: 1 <= n <= 200000; 0 <= len(edges) <= 200000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is not equal to the unordered pair {edges[j][0], edges[j][1]}; and 0 <= source < n and 0 <= destination < n. -/
theorem spec_2 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val) :
    ∃ r : Bool, valid_path n edges source destination = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val), ∃ r : Bool, valid_path n edges source destination = ok r) := by
  sorry

/-- Whenever valid_path n edges source destination returns r and valid_path n edges destination source returns r', we have r = r'.
  Preconditions: 1 <= n <= 200000; 0 <= len(edges) <= 200000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is not equal to the unordered pair {edges[j][0], edges[j][1]}; and 0 <= source < n and 0 <= destination < n. -/
theorem spec_3 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val) (r r' : Bool)
    (hres : valid_path n edges source destination = ok r)
    (hres' : valid_path n edges destination source = ok r') :
    r = r' := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val) (r r' : Bool)
    (hres : valid_path n edges source destination = ok r)
    (hres' : valid_path n edges destination source = ok r'), r = r') := by
  sorry

/-- Whenever valid_path n edges source destination returns r and valid_path n edges' source destination returns r', we have r = r'.
  Preconditions: 1 <= n <= 200000; 0 <= len(edges) <= 200000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is not equal to the unordered pair {edges[j][0], edges[j][1]}; 0 <= source < n and 0 <= destination < n; and edges' is a list of the same length as edges such that for every i with 0 <= i < len(edges), edges'[i] is either [edges[i][0], edges[i][1]] or [edges[i][1], edges[i][0]], and edges' satisfies the same constraints for n. -/
theorem spec_4 (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val) (hflip : EdgeFlipped edges edges')
    (hpre' : GraphPre n edges') (r r' : Bool)
    (hres : valid_path n edges source destination = ok r)
    (hres' : valid_path n edges' source destination = ok r') :
    r = r' := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val) (hflip : EdgeFlipped edges edges')
    (hpre' : GraphPre n edges') (r r' : Bool)
    (hres : valid_path n edges source destination = ok r)
    (hres' : valid_path n edges' source destination = ok r'), r = r') := by
  sorry

/-- Whenever valid_path n edges source destination returns r and valid_path n' edges source destination returns r', we have r = r'.
  Preconditions: 1 <= n <= 200000; 0 <= len(edges) <= 200000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is not equal to the unordered pair {edges[j][0], edges[j][1]}; 0 <= source < n and 0 <= destination < n; and n <= n' <= 200000. -/
theorem spec_5 (n n' : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val) (hn : n.val ≤ n'.val) (hn' : n'.val ≤ 200000)
    (r r' : Bool) (hres : valid_path n edges source destination = ok r)
    (hres' : valid_path n' edges source destination = ok r') :
    r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n n' : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val) (hn : n.val ≤ n'.val) (hn' : n'.val ≤ 200000)
    (r r' : Bool) (hres : valid_path n edges source destination = ok r)
    (hres' : valid_path n' edges source destination = ok r'), r = r') := by
  sorry

/-- If valid_path n edges source destination returns true, then valid_path n edges' source destination returns true.
  Preconditions: 1 <= n <= 200000; 0 <= len(edges) <= 200000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is not equal to the unordered pair {edges[j][0], edges[j][1]}; 0 <= source < n and 0 <= destination < n; and edges' satisfies the same constraints for n and contains every edge of edges, meaning that for every i with 0 <= i < len(edges) there exists j with 0 <= j < len(edges') such that the unordered pair {edges'[j][0], edges'[j][1]} equals the unordered pair {edges[i][0], edges[i][1]}. -/
theorem spec_6 (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val) (hpre' : GraphPre n edges')
    (hincl : EdgeIncl edges edges')
    (hres : valid_path n edges source destination = ok true) :
    valid_path n edges' source destination = ok true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val) (hpre' : GraphPre n edges')
    (hincl : EdgeIncl edges edges')
    (hres : valid_path n edges source destination = ok true), valid_path n edges' source destination = ok true) := by
  sorry

/-- Whenever valid_path n edges source destination returns true, there exist an integer m >= 0 and vertices v_0, ..., v_m such that (1) 0 <= v_j < n for every j with 0 <= j <= m, (2) v_0 = source, (3) v_m = destination, (4) for every j with 0 <= j < m the unordered pair {v_j, v_{j+1}} is an edge of edges, and (5) v_0, ..., v_m are pairwise distinct.
  Preconditions: 1 <= n <= 200000; 0 <= len(edges) <= 200000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is not equal to the unordered pair {edges[j][0], edges[j][1]}; and 0 <= source < n and 0 <= destination < n. -/
theorem spec_7 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val)
    (hres : valid_path n edges source destination = ok true) :
    WalkSimple n.val edges source.val destination.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val)
    (hres : valid_path n edges source destination = ok true), WalkSimple n.val edges source.val destination.val) := by
  sorry

/-- Whenever valid_path n edges source destination returns Ok false, there exists a set S ⊆ {0, ..., n-1} such that source ∈ S, destination ∉ S, and for every i with 0 <= i < len(edges), either (edges[i][0] ∈ S and edges[i][1] ∈ S) or (edges[i][0] ∉ S and edges[i][1] ∉ S).
  Preconditions: 1 <= n <= 200000; 0 <= len(edges) <= 200000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is not equal to the unordered pair {edges[j][0], edges[j][1]}; and 0 <= source < n and 0 <= destination < n. -/
theorem spec_8 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val)
    (hres : valid_path n edges source destination = ok false) :
    ∃ S : Int → Prop,
      (∀ x : Int, S x → InBounds n.val x) ∧ S source.val ∧ ¬S destination.val ∧
        (∀ i : Nat, i < edges.val.length → ∀ a b : Int, edgeAt edges i = [a, b] →
          (S a ∧ S b) ∨ (¬S a ∧ ¬S b)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val)
    (hres : valid_path n edges source destination = ok false), ∃ S : Int → Prop,
      (∀ x : Int, S x → InBounds n.val x) ∧ S source.val ∧ ¬S destination.val ∧
        (∀ i : Nat, i < edges.val.length → ∀ a b : Int, edgeAt edges i = [a, b] →
          (S a ∧ S b) ∨ (¬S a ∧ ¬S b))) := by
  sorry

/-- If valid_path n edges source source2 returns true, then whenever valid_path n edges source destination returns r and valid_path n edges source2 destination returns r', we have r = r'.
  Preconditions: 1 <= n <= 200000; 0 <= len(edges) <= 200000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is not equal to the unordered pair {edges[j][0], edges[j][1]}; 0 <= source < n and 0 <= destination < n; and 0 <= source2 < n. -/
theorem spec_9 (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (source source2 destination : I64) (hpre : GraphPre n edges)
    (hsource : InBounds n.val source.val) (hsource2 : InBounds n.val source2.val)
    (hdest : InBounds n.val destination.val)
    (hconn : valid_path n edges source source2 = ok true)
    (r r' : Bool) (hres : valid_path n edges source destination = ok r)
    (hres' : valid_path n edges source2 destination = ok r') :
    r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (source source2 destination : I64) (hpre : GraphPre n edges)
    (hsource : InBounds n.val source.val) (hsource2 : InBounds n.val source2.val)
    (hdest : InBounds n.val destination.val)
    (hconn : valid_path n edges source source2 = ok true)
    (r r' : Bool) (hres : valid_path n edges source destination = ok r)
    (hres' : valid_path n edges source2 destination = ok r'), r = r') := by
  sorry

/-- Whenever valid_path n edges source destination returns r and valid_path n edges' source' destination' returns r', we have r = r'.
  Preconditions: 1 <= n <= 200000; 0 <= len(edges) <= 200000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is not equal to the unordered pair {edges[j][0], edges[j][1]}; 0 <= source < n and 0 <= destination < n; p is a bijection from {0, ..., n-1} to itself; edges' is a list of the same length as edges such that edges'[i][0] = p(edges[i][0]) and edges'[i][1] = p(edges[i][1]) for every i with 0 <= i < len(edges); and source' = p(source), destination' = p(destination). -/
theorem spec_10 (n : I64) (edges edges' : Slice (alloc.vec.Vec I64))
    (source destination source' destination' : I64) (p : Int → Int)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val)
    (hp : ∀ x : Int, InBounds n.val x → InBounds n.val (p x))
    (hpinj : ∀ x y : Int, InBounds n.val x → InBounds n.val y → p x = p y → x = y)
    (hlen : edges'.val.length = edges.val.length)
    (hmap : ∀ i : Nat, i < edges.val.length → edgeAt edges' i = (edgeAt edges i).map p)
    (hsource' : source'.val = p source.val)
    (hdest' : destination'.val = p destination.val)
    (r r' : Bool) (hres : valid_path n edges source destination = ok r)
    (hres' : valid_path n edges' source' destination' = ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : I64) (edges edges' : Slice (alloc.vec.Vec I64))
    (source destination source' destination' : I64) (p : Int → Int)
    (hpre : GraphPre n edges) (hsource : InBounds n.val source.val)
    (hdest : InBounds n.val destination.val)
    (hp : ∀ x : Int, InBounds n.val x → InBounds n.val (p x))
    (hpinj : ∀ x y : Int, InBounds n.val x → InBounds n.val y → p x = p y → x = y)
    (hlen : edges'.val.length = edges.val.length)
    (hmap : ∀ i : Nat, i < edges.val.length → edgeAt edges' i = (edgeAt edges i).map p)
    (hsource' : source'.val = p source.val)
    (hdest' : destination'.val = p destination.val)
    (r r' : Bool) (hres : valid_path n edges source destination = ok r)
    (hres' : valid_path n edges' source' destination' = ok r'), r = r') := by
  sorry

end AegisSpec.ValidPath
