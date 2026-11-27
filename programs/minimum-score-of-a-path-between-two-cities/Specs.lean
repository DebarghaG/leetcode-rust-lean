import Aegis.MinScore.Code.Funs

/-!
# Specifications of `Aegis.MinScore.min_score`

LeetCode problem `minimum-score-of-a-path-between-two-cities`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinScore

structure Road where

  a : Int

  b : Int

  w : Int
  deriving DecidableEq, Repr

def rowInts (row : alloc.vec.Vec Std.I64) : List Int := row.val.map (fun x => x.val)

def rowToRoad (row : alloc.vec.Vec Std.I64) : Option Road :=
  match rowInts row with
  | [a, b, w] => some ⟨a, b, w⟩
  | _ => none

def roadAt (roads : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option Road :=
  (roads.val[i]?).bind rowToRoad

def nRoads (roads : Slice (alloc.vec.Vec Std.I64)) : Nat := roads.val.length

def Step (roads : Slice (alloc.vec.Vec Std.I64)) (u v w : Int) : Prop :=
  ∃ (i : Nat) (rd : Road), roadAt roads i = some rd ∧ rd.w = w ∧
    ((rd.a = u ∧ rd.b = v) ∨ (rd.a = v ∧ rd.b = u))

def Adj (roads : Slice (alloc.vec.Vec Std.I64)) (u v : Int) : Prop :=
  ∃ w : Int, Step roads u v w

def Reachable (roads : Slice (alloc.vec.Vec Std.I64)) (v : Int) : Prop :=
  Relation.ReflTransGen (Adj roads) 1 v

def reachableEdgeWeights (roads : Slice (alloc.vec.Vec Std.I64)) : Set Int :=
  {w | ∃ (i : Nat) (rd : Road), roadAt roads i = some rd ∧ Reachable roads rd.a ∧
      Reachable roads rd.b ∧ rd.w = w}

def IsMinOf (s : Set Int) (m : Int) : Prop :=
  m ∈ s ∧ ∀ x ∈ s, m ≤ x

abbrev WalkStep := Int × Int × Int

def Walk : Slice (alloc.vec.Vec Std.I64) → Int → Int → List WalkStep → Prop
  | _, x, y, [] => x = y
  | roads, x, y, (u, v, w) :: rest => u = x ∧ Step roads u v w ∧ Walk roads v y rest

def walkScore (steps : List WalkStep) : Option Int :=
  match steps with
  | [] => none
  | s :: rest => some (rest.foldl (fun acc t => Min.min acc t.2.2) s.2.2)

def ProblemConstraints (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  2 ≤ n.val ∧ n.val ≤ 100000 ∧
  1 ≤ nRoads roads ∧ nRoads roads ≤ 100000 ∧
  (∀ (i : Nat), i < nRoads roads →
      ∃ rd : Road, roadAt roads i = some rd ∧
        1 ≤ rd.a ∧ rd.a ≤ n.val ∧ 1 ≤ rd.b ∧ rd.b ≤ n.val ∧ rd.a ≠ rd.b ∧
        1 ≤ rd.w ∧ rd.w ≤ 10000) ∧
  (∀ (i j : Nat), i < nRoads roads → j < nRoads roads → i ≠ j →
      ∀ (ri rj : Road), roadAt roads i = some ri → roadAt roads j = some rj →
        ¬ ((ri.a = rj.a ∧ ri.b = rj.b) ∨ (ri.a = rj.b ∧ ri.b = rj.a))) ∧
  Reachable roads n.val

def ScaleWeights (c : Int) (roads roads' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ (i : Nat), roadAt roads' i = (roadAt roads i).map (fun rd => ⟨rd.a, rd.b, c * rd.w⟩)

/-- Whenever the function returns a result r, r is the minimum possible score of a path from city 1 to city n, where a path is a finite walk that may repeat roads and cities, and the score of such a walk is the minimum distance among the roads used by it. Equivalently, let C be the set of cities reachable from city 1 using the roads; then r = min{ roads[i][2] | 0 <= i < len(roads) and roads[i][0] in C and roads[i][1] in C }.
  Preconditions: Assume the problem constraints: n is an integer with 2 <= n <= 100000; roads is a finite list with 1 <= len(roads) <= 100000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are integers with 1 <= roads[i][0], roads[i][1] <= n and roads[i][0] != roads[i][1], and roads[i][2] is an integer with 1 <= roads[i][2] <= 10000; no undirected edge {roads[i][0], roads[i][1]} is repeated; and city n is reachable from city 1 by a finite sequence of roads, each usable in either direction. -/
theorem spec_1 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r) :
    IsMinOf (reachableEdgeWeights roads) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r), IsMinOf (reachableEdgeWeights roads) r.val) := by
  sorry

/-- The function returns a result r; it does not fail due to overflow, out-of-bounds access, or panic.
  Preconditions: Assume the problem constraints: n is an integer with 2 <= n <= 100000; roads is a finite list with 1 <= len(roads) <= 100000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are integers with 1 <= roads[i][0], roads[i][1] <= n and roads[i][0] != roads[i][1], and roads[i][2] is an integer with 1 <= roads[i][2] <= 10000; no undirected edge {roads[i][0], roads[i][1]} is repeated; and city n is reachable from city 1 by a finite sequence of roads, each usable in either direction. -/
theorem spec_2 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) :
    ∃ r : Std.I64, Aegis.MinScore.min_score n roads = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads), ∃ r : Std.I64, Aegis.MinScore.min_score n roads = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= 10000.
  Preconditions: Assume the problem constraints: n is an integer with 2 <= n <= 100000; roads is a finite list with 1 <= len(roads) <= 100000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are integers with 1 <= roads[i][0], roads[i][1] <= n and roads[i][0] != roads[i][1], and roads[i][2] is an integer with 1 <= roads[i][2] <= 10000; no undirected edge {roads[i][0], roads[i][1]} is repeated; and city n is reachable from city 1 by a finite sequence of roads, each usable in either direction. -/
theorem spec_3 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r) :
    1 ≤ r.val ∧ r.val ≤ 10000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r), 1 ≤ r.val ∧ r.val ≤ 10000) := by
  sorry

/-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(roads) such that roads[i][0] in C and roads[i][1] in C and roads[i][2] = r, where C is the set of cities reachable from city 1.
  Preconditions: Assume the problem constraints: n is an integer with 2 <= n <= 100000; roads is a finite list with 1 <= len(roads) <= 100000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are integers with 1 <= roads[i][0], roads[i][1] <= n and roads[i][0] != roads[i][1], and roads[i][2] is an integer with 1 <= roads[i][2] <= 10000; no undirected edge {roads[i][0], roads[i][1]} is repeated; and city n is reachable from city 1 by a finite sequence of roads, each usable in either direction. -/
theorem spec_4 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r) :
    ∃ (i : Nat) (rd : Road), roadAt roads i = some rd ∧ Reachable roads rd.a ∧
      Reachable roads rd.b ∧ rd.w = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r), ∃ (i : Nat) (rd : Road), roadAt roads i = some rd ∧ Reachable roads rd.a ∧
      Reachable roads rd.b ∧ rd.w = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(roads), if roads[i][0] in C and roads[i][1] in C, then roads[i][2] >= r, where C is the set of cities reachable from city 1.
  Preconditions: Assume the problem constraints: n is an integer with 2 <= n <= 100000; roads is a finite list with 1 <= len(roads) <= 100000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are integers with 1 <= roads[i][0], roads[i][1] <= n and roads[i][0] != roads[i][1], and roads[i][2] is an integer with 1 <= roads[i][2] <= 10000; no undirected edge {roads[i][0], roads[i][1]} is repeated; and city n is reachable from city 1 by a finite sequence of roads, each usable in either direction. -/
theorem spec_5 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r) :
    ∀ (i : Nat) (rd : Road), roadAt roads i = some rd → Reachable roads rd.a →
      Reachable roads rd.b → rd.w ≥ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r), ∀ (i : Nat) (rd : Road), roadAt roads i = some rd → Reachable roads rd.a →
      Reachable roads rd.b → rd.w ≥ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every finite walk W from city 1 to city n in the undirected road graph, score(W) >= r, where score(W) is the minimum distance among the roads used by W.
  Preconditions: Assume the problem constraints: n is an integer with 2 <= n <= 100000; roads is a finite list with 1 <= len(roads) <= 100000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are integers with 1 <= roads[i][0], roads[i][1] <= n and roads[i][0] != roads[i][1], and roads[i][2] is an integer with 1 <= roads[i][2] <= 10000; no undirected edge {roads[i][0], roads[i][1]} is repeated; and city n is reachable from city 1 by a finite sequence of roads, each usable in either direction. -/
theorem spec_6 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r) :
    ∀ (steps : List WalkStep) (k : Int), Walk roads 1 n.val steps →
      walkScore steps = some k → r.val ≤ k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r), ∀ (steps : List WalkStep) (k : Int), Walk roads 1 n.val steps →
      walkScore steps = some k → r.val ≤ k) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite walk W from city 1 to city n in the undirected road graph such that score(W) = r, where score(W) is the minimum distance among the roads used by W.
  Preconditions: Assume the problem constraints: n is an integer with 2 <= n <= 100000; roads is a finite list with 1 <= len(roads) <= 100000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are integers with 1 <= roads[i][0], roads[i][1] <= n and roads[i][0] != roads[i][1], and roads[i][2] is an integer with 1 <= roads[i][2] <= 10000; no undirected edge {roads[i][0], roads[i][1]} is repeated; and city n is reachable from city 1 by a finite sequence of roads, each usable in either direction. -/
theorem spec_7 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r) :
    ∃ steps : List WalkStep, Walk roads 1 n.val steps ∧ walkScore steps = some r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (r : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r), ∃ steps : List WalkStep, Walk roads 1 n.val steps ∧ walkScore steps = some r.val) := by
  sorry

/-- Whenever the function returns r on (n, roads) and r' on (n, roads'), we have r = r'.
  Preconditions: Assume the problem constraints: n is an integer with 2 <= n <= 100000; roads is a finite list with 1 <= len(roads) <= 100000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are integers with 1 <= roads[i][0], roads[i][1] <= n and roads[i][0] != roads[i][1], and roads[i][2] is an integer with 1 <= roads[i][2] <= 10000; no undirected edge {roads[i][0], roads[i][1]} is repeated; and city n is reachable from city 1 by a finite sequence of roads, each usable in either direction. Let roads' be any permutation of the rows of roads, with the same triples possibly in a different order. -/
theorem spec_8 (n : Std.I64) (roads roads' : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (h' : ProblemConstraints n roads')
    (hperm : List.Perm roads.val roads'.val) (r r' : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r)
    (hr' : Aegis.MinScore.min_score n roads' = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (roads roads' : Slice (alloc.vec.Vec Std.I64))
    (h : ProblemConstraints n roads) (h' : ProblemConstraints n roads')
    (hperm : List.Perm roads.val roads'.val) (r r' : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r)
    (hr' : Aegis.MinScore.min_score n roads' = ok r'), r = r') := by
  sorry

/-- Whenever the function returns r on (n, roads) and r' on (n, roads'), we have r' = c * r.
  Preconditions: Assume the problem constraints: n is an integer with 2 <= n <= 100000; roads is a finite list with 1 <= len(roads) <= 100000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are integers with 1 <= roads[i][0], roads[i][1] <= n and roads[i][0] != roads[i][1], and roads[i][2] is an integer with 1 <= roads[i][2] <= 10000; no undirected edge {roads[i][0], roads[i][1]} is repeated; and city n is reachable from city 1 by a finite sequence of roads, each usable in either direction. Let c be a positive integer, and let roads' be obtained from roads by replacing each distance roads[i][2] by c * roads[i][2]; assume roads' also satisfies the problem constraints, in particular every c * roads[i][2] is between 1 and 10000. -/
theorem spec_9 (n : Std.I64) (roads roads' : Slice (alloc.vec.Vec Std.I64)) (c : Int)
    (hc : 0 < c) (h : ProblemConstraints n roads) (h' : ProblemConstraints n roads')
    (hscale : ScaleWeights c roads roads') (r r' : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r)
    (hr' : Aegis.MinScore.min_score n roads' = ok r') :
    r'.val = c * r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (roads roads' : Slice (alloc.vec.Vec Std.I64)) (c : Int)
    (hc : 0 < c) (h : ProblemConstraints n roads) (h' : ProblemConstraints n roads')
    (hscale : ScaleWeights c roads roads') (r r' : Std.I64)
    (hr : Aegis.MinScore.min_score n roads = ok r)
    (hr' : Aegis.MinScore.min_score n roads' = ok r'), r'.val = c * r.val) := by
  sorry

end AegisSpec.MinScore
