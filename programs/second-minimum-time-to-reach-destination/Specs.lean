import Aegis.SecondMinimum.Code.Funs

/-!
# Specifications of `Aegis.SecondMinimum.second_minimum`

LeetCode problem `second-minimum-time-to-reach-destination`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped Classical

namespace AegisSpec.SecondMinimum

def edgeVertices (e : alloc.vec.Vec Std.I64) : List Int :=
  e.val.map (fun x => x.val)

def edgeLists (edges : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  edges.val.map edgeVertices

def edgePairs (edges : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
  (edgeLists edges).filterMap fun l =>
    match l with
    | [a, b] => some (a, b)
    | _ => none

def normalizePair (p : Int × Int) : Int × Int :=
  if p.1 ≤ p.2 then p else (p.2, p.1)

def IsEdge (edges : Slice (alloc.vec.Vec Std.I64)) (a b : Int) : Prop :=
  ∃ e ∈ edgeLists edges, e = [a, b] ∨ e = [b, a]

def ChainOfEdges (edges : Slice (alloc.vec.Vec Std.I64)) : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: tl => IsEdge edges x y ∧ ChainOfEdges edges (y :: tl)

def IsWalkBetween (edges : Slice (alloc.vec.Vec Std.I64)) (a b : Int) (vs : List Int) : Prop :=
  vs.head? = some a ∧ vs.getLast? = some b ∧ ChainOfEdges edges vs

def IsWalk (edges : Slice (alloc.vec.Vec Std.I64)) (nv : Int) (vs : List Int) : Prop :=
  IsWalkBetween edges 1 nv vs

def walkLength (vs : List Int) : Nat := vs.length - 1

def WalkLength (edges : Slice (alloc.vec.Vec Std.I64)) (nv : Int) (k : Nat) : Prop :=
  ∃ vs : List Int, IsWalk edges nv vs ∧ walkLength vs = k

def Reaches (edges : Slice (alloc.vec.Vec Std.I64)) (a b : Int) : Prop :=
  ∃ vs : List Int, IsWalkBetween edges a b vs

def intIsEven (x : Int) : Bool := x % 2 == 0

def delay (change t : Int) : Int :=
  if intIsEven (t.fdiv change) then t else (t.fdiv change + 1) * change

def A (time change : Int) : Nat → Int
  | 0 => 0
  | (k + 1) => delay change (A time change k) + time

def arrival (time change : Int) (vs : List Int) : Int :=
  (vs.drop 1).foldl (fun t _ => delay change t + time) 0

noncomputable def d1 (edges : Slice (alloc.vec.Vec Std.I64)) (nv : Int) : Nat :=
  if h : ∃ k, WalkLength edges nv k then Nat.find h else 0

noncomputable def d2 (edges : Slice (alloc.vec.Vec Std.I64)) (nv : Int) : Nat :=
  if h : ∃ k, WalkLength edges nv k ∧ d1 edges nv < k then Nat.find h else 0

structure Pre (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64) :
    Prop where

  n_ge : 2 ≤ n.val

  n_le : n.val ≤ 10000

  m_ge : n.val - 1 ≤ (edges.val.length : Int)

  m_le : (edges.val.length : Int) ≤ min 20000 (n.val * (n.val - 1) / 2)

  edge_len : ∀ e ∈ edges.val, e.val.length = 2

  edge_range : ∀ e ∈ edges.val, ∀ x ∈ e.val, 1 ≤ x.val ∧ x.val ≤ n.val

  edge_distinct : ∀ e ∈ edges.val, ∀ a b : Int, edgeVertices e = [a, b] → a ≠ b

  edge_nodup : ((edgePairs edges).map normalizePair).Nodup

  connected : ∀ v : Int, 1 ≤ v → v ≤ n.val → Reaches edges 1 v

  time_ge : 1 ≤ time.val

  time_le : time.val ≤ 1000

  change_ge : 1 ≤ change.val

  change_le : change.val ≤ 1000

/-- Let an admissible walk be a finite sequence (v_0,...,v_k) with k >= 0, v_0 = 1, v_k = n, and each consecutive pair {v_j, v_{j+1}} an edge from edges (edges are undirected). For t >= 0 let D(t) = t when floor(t/change) is even (signal green), and D(t) = (floor(t/change)+1)*change when floor(t/change) is odd (wait at a red signal to the next green). Define A_0 = 0 and A_{k+1} = D(A_k) + time. Let L = { k >= 0 : an admissible walk from 1 to n with exactly k edges exists }, d1 = min L, and d2 = min { k in L : k > d1 }. The function returns a result r with r = A_{d2}. Equivalently, r is the second smallest possible final arrival time at vertex n over all admissible walks obeying the signal rules: the smallest arrival time strictly larger than the minimum possible arrival time.
  Preconditions: n, edges, time, change satisfy all LeetCode constraints: 2 <= n <= 10^4; writing m = len(edges), n-1 <= m <= min(20000, n*(n-1)/2); every edges[i] has length 2, with 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, and edges[i][0] != edges[i][1]; no two edges join the same unordered pair of vertices; the undirected graph on vertices 1..n given by edges is connected; 1 <= time <= 1000; 1 <= change <= 1000. -/
theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change) :
    ∃ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r ∧
        r.val = A time.val change.val (d2 edges n.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change), ∃ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r ∧
        r.val = A time.val change.val (d2 edges n.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail: it does not panic, access out of bounds, or overflow 64-bit integer arithmetic.
  Preconditions: Same as spec_1. -/
theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change) :
    ∃ r : Std.I64, Aegis.SecondMinimum.second_minimum n edges time change = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change), ∃ r : Std.I64, Aegis.SecondMinimum.second_minimum n edges time change = ok r) := by
  sorry

/-- Let r be the returned value. Then r >= 2 * time.
  Preconditions: Same as spec_1. -/
theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change) :
    ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r → 2 * time.val ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change), ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r → 2 * time.val ≤ r.val) := by
  sorry

/-- Let r be the returned value. Then r <= (n + 1) * (time + change).
  Preconditions: Same as spec_1. -/
theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change) :
    ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r →
        r.val ≤ (n.val + 1) * (time.val + change.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change), ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r →
        r.val ≤ (n.val + 1) * (time.val + change.val)) := by
  sorry

/-- Using the definitions of L, d1, d2, and A_k from spec_1, d2 is either d1 + 1 or d1 + 2. Consequently, the returned value r is either A_{d1+1} or A_{d1+2}, according to which value d2 equals.
  Preconditions: Same as spec_1. -/
theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change) :
    (d2 edges n.val = d1 edges n.val + 1 ∨ d2 edges n.val = d1 edges n.val + 2) ∧
      ∀ r : Std.I64,
        Aegis.SecondMinimum.second_minimum n edges time change = ok r →
          (r.val = A time.val change.val (d1 edges n.val + 1) ∧
              d2 edges n.val = d1 edges n.val + 1) ∨
            (r.val = A time.val change.val (d1 edges n.val + 2) ∧
              d2 edges n.val = d1 edges n.val + 2) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change), (d2 edges n.val = d1 edges n.val + 1 ∨ d2 edges n.val = d1 edges n.val + 2) ∧
      ∀ r : Std.I64,
        Aegis.SecondMinimum.second_minimum n edges time change = ok r →
          (r.val = A time.val change.val (d1 edges n.val + 1) ∧
              d2 edges n.val = d1 edges n.val + 1) ∨
            (r.val = A time.val change.val (d1 edges n.val + 2) ∧
              d2 edges n.val = d1 edges n.val + 2)) := by
  sorry

/-- Using A_{d1} from spec_1, the returned value r satisfies r > A_{d1}. Thus r is strictly larger than the minimum possible arrival time at vertex n.
  Preconditions: Same as spec_1. -/
theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change) :
    ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r →
        A time.val change.val (d1 edges n.val) < r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change), ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r →
        A time.val change.val (d1 edges n.val) < r.val) := by
  sorry

/-- For every admissible walk from vertex 1 to vertex n, if its final arrival time under the signal rules is t, then t = A_{d1} or t >= r. Equivalently, no attainable final arrival time lies strictly between the minimum A_{d1} and the returned value r.
  Preconditions: Same as spec_1. -/
theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change) :
    ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r →
        ∀ vs : List Int,
          IsWalk edges n.val vs →
            arrival time.val change.val vs = A time.val change.val (d1 edges n.val) ∨
              r.val ≤ arrival time.val change.val vs := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change), ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r →
        ∀ vs : List Int,
          IsWalk edges n.val vs →
            arrival time.val change.val vs = A time.val change.val (d1 edges n.val) ∨
              r.val ≤ arrival time.val change.val vs) := by
  sorry

/-- There exists an admissible walk from vertex 1 to vertex n whose final arrival time under the signal rules equals the returned value r.
  Preconditions: Same as spec_1. -/
theorem spec_8 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change) :
    ∃ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r ∧
        ∃ vs : List Int, IsWalk edges n.val vs ∧ arrival time.val change.val vs = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change), ∃ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r ∧
        ∃ vs : List Int, IsWalk edges n.val vs ∧ arrival time.val change.val vs = r.val) := by
  sorry

/-- Let L and d1 be as in spec_1. If d1 + 1 is in L, then the returned value r equals A_{d1+1}; if d1 + 1 is not in L, then r equals A_{d1+2}.
  Preconditions: Same as spec_1. -/
theorem spec_9 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change) :
    ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r →
        (WalkLength edges n.val (d1 edges n.val + 1) →
            r.val = A time.val change.val (d1 edges n.val + 1)) ∧
          (¬ WalkLength edges n.val (d1 edges n.val + 1) →
            r.val = A time.val change.val (d1 edges n.val + 2)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change), ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r →
        (WalkLength edges n.val (d1 edges n.val + 1) →
            r.val = A time.val change.val (d1 edges n.val + 1)) ∧
          (¬ WalkLength edges n.val (d1 edges n.val + 1) →
            r.val = A time.val change.val (d1 edges n.val + 2))) := by
  sorry

/-- Let r be the returned value. Then r >= time and floor((r - time)/change) is even. Equivalently, the last edge traversal of any admissible walk attaining r starts at time r - time, when the signal is green.
  Preconditions: Same as spec_1. -/
theorem spec_10 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change) :
    ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r →
        time.val ≤ r.val ∧ ((r.val - time.val).fdiv change.val) % 2 = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (time change : Std.I64)
    (hpre : Pre n edges time change), ∀ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r →
        time.val ≤ r.val ∧ ((r.val - time.val).fdiv change.val) % 2 = 0) := by
  sorry

/-- Let edges and edges' be two edge lists satisfying the preconditions for the same n, time, and change. Let L and L' be their respective sets of attainable walk lengths from vertex 1 to vertex n. If L = L', then the function returns the same value for (n, edges, time, change) and for (n, edges', time, change).
  Preconditions: Same as spec_1, applied to both edge lists edges and edges' for the same n, time, and change. -/
theorem spec_11 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (time change : Std.I64) (hpre : Pre n edges time change) (hpre' : Pre n edges' time change)
    (hL : ∀ k : Nat, WalkLength edges n.val k ↔ WalkLength edges' n.val k) :
    ∃ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r ∧
        Aegis.SecondMinimum.second_minimum n edges' time change = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (time change : Std.I64) (hpre : Pre n edges time change) (hpre' : Pre n edges' time change)
    (hL : ∀ k : Nat, WalkLength edges n.val k ↔ WalkLength edges' n.val k), ∃ r : Std.I64,
      Aegis.SecondMinimum.second_minimum n edges time change = ok r ∧
        Aegis.SecondMinimum.second_minimum n edges' time change = ok r) := by
  sorry

end AegisSpec.SecondMinimum
