import Aegis.NodesBetweenCriticalPoints.Code.Funs

/-!
# Specifications of `Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points`

LeetCode problem `find-the-minimum-and-maximum-number-of-nodes-between-critical-points`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NodesBetweenCriticalPoints

  abbrev NodeList : Type := Aegis.NodesBetweenCriticalPoints.List

  def nodeVals : NodeList → List Int
    | .Nil => []
    | .Cons x rest => x.val :: nodeVals rest

  def nodeLen (head : NodeList) : Nat := (nodeVals head).length

  def snocNode : NodeList → Std.I64 → NodeList
    | .Nil, x => .Cons x .Nil
    | .Cons y rest, x => .Cons y (snocNode rest x)

  def reverseNodes : NodeList → NodeList
    | .Nil => .Nil
    | .Cons x rest => snocNode (reverseNodes rest) x

  def outVals (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

  def outLen (v : alloc.vec.Vec Std.I64) : Nat := (outVals v).length

  def outEntry (v : alloc.vec.Vec Std.I64) (i : Nat) : Int := (outVals v).getD i 0

  def isCritical (vals : List Int) (i : Nat) : Bool :=
    match vals[i - 1]?, vals[i]?, vals[i + 1]? with
    | some a, some b, some c =>
      decide (0 < i ∧ i + 1 < vals.length ∧ ((a < b ∧ c < b) ∨ (b < a ∧ b < c)))
    | _, _, _ => false

  def critIndices (vals : List Int) : List Nat :=
    (List.range vals.length).filter (isCritical vals)

  def idxDist (i j : Nat) : Int :=
    if i ≤ j then (j : Int) - (i : Int) else (i : Int) - (j : Int)

  def listMinInt (d : Int) (l : List Int) : Int :=
    match l with
    | [] => d
    | a :: t => t.foldl (fun acc x => min acc x) a

  def listMaxInt (d : Int) (l : List Int) : Int :=
    match l with
    | [] => d
    | a :: t => t.foldl (fun acc x => max acc x) a

  def pairDistInts (l : List Nat) : List Int :=
    (l.product l).filterMap
      (fun p => if p.1 = p.2 then none else some (idxDist p.1 p.2))

  def critIdxInts (vals : List Int) : List Int :=
    (critIndices vals).map (fun i => (i : Int))

  def critGaps (vals : List Int) : List Int :=
    let l := critIdxInts vals
    (l.zip l.tail).map (fun p => p.2 - p.1)

  /-- Whenever the function returns Ok v, len(v) = 2 and, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: (i) if |C| < 2 then v[0] = -1 and v[1] = -1; (ii) if |C| >= 2 then v[0] = min{ |i-j| : i in C and j in C and i != j } and v[1] = max{ |i-j| : i in C and j in C and i != j }. The distance between nodes at indices i and j is |i-j|.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_1 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      outLen v = 2 ∧
        ((critIndices (nodeVals head)).length < 2 →
          outEntry v 0 = -1 ∧ outEntry v 1 = -1) ∧
        (2 ≤ (critIndices (nodeVals head)).length →
          outEntry v 0 = listMinInt 0 (pairDistInts (critIndices (nodeVals head))) ∧
          outEntry v 1 = listMaxInt 0 (pairDistInts (critIndices (nodeVals head)))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), outLen v = 2 ∧
          ((critIndices (nodeVals head)).length < 2 →
            outEntry v 0 = -1 ∧ outEntry v 1 = -1) ∧
          (2 ≤ (critIndices (nodeVals head)).length →
            outEntry v 0 = listMinInt 0 (pairDistInts (critIndices (nodeVals head))) ∧
            outEntry v 1 = listMaxInt 0 (pairDistInts (critIndices (nodeVals head))))) := by
    sorry

  /-- Whenever the function returns Ok v, len(v) = 2.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_2 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      outLen v = 2 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), outLen v = 2) := by
    sorry

  /-- The function returns Ok v for some vector v on every input satisfying the preconditions; in particular it does not fail with overflow, out-of-bounds access, or panic.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_3 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000) :
      ∃ v : alloc.vec.Vec Std.I64,
        Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000), ∃ v : alloc.vec.Vec Std.I64,
          Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) := by
    sorry

  /-- Whenever the function returns Ok v, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: if |C| < 2 then v = [-1, -1] (a vector of length 2 whose entries are both -1).
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_4 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      (critIndices (nodeVals head)).length < 2 → outVals v = [-1, -1] := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), (critIndices (nodeVals head)).length < 2 → outVals v = [-1, -1]) := by
    sorry

  /-- Whenever the function returns Ok v, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: if |C| >= 2 then 1 <= v[0] <= len(head)-1 and 1 <= v[1] <= len(head)-1.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_5 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      2 ≤ (critIndices (nodeVals head)).length →
        (1 ≤ outEntry v 0 ∧ outEntry v 0 ≤ (nodeLen head : Int) - 1 ∧
          1 ≤ outEntry v 1 ∧ outEntry v 1 ≤ (nodeLen head : Int) - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), 2 ≤ (critIndices (nodeVals head)).length →
          (1 ≤ outEntry v 0 ∧ outEntry v 0 ≤ (nodeLen head : Int) - 1 ∧
            1 ≤ outEntry v 1 ∧ outEntry v 1 ≤ (nodeLen head : Int) - 1)) := by
    sorry

  /-- Whenever the function returns Ok v, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: if |C| >= 2 then v[0] <= v[1].
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_6 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      2 ≤ (critIndices (nodeVals head)).length → outEntry v 0 ≤ outEntry v 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), 2 ≤ (critIndices (nodeVals head)).length → outEntry v 0 ≤ outEntry v 1) := by
    sorry

  /-- Whenever the function returns Ok v, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: if |C| >= 2 then there exist indices i and j in C with i != j such that v[0] = |i-j|.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_7 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      2 ≤ (critIndices (nodeVals head)).length →
        ∃ i ∈ critIndices (nodeVals head), ∃ j ∈ critIndices (nodeVals head),
          i ≠ j ∧ outEntry v 0 = idxDist i j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), 2 ≤ (critIndices (nodeVals head)).length →
          ∃ i ∈ critIndices (nodeVals head), ∃ j ∈ critIndices (nodeVals head),
            i ≠ j ∧ outEntry v 0 = idxDist i j) := by
    sorry

  /-- Whenever the function returns Ok v, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: if |C| >= 2 then for every indices i and j in C with i != j, v[0] <= |i-j|.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_8 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      2 ≤ (critIndices (nodeVals head)).length →
        ∀ i ∈ critIndices (nodeVals head), ∀ j ∈ critIndices (nodeVals head),
          i ≠ j → outEntry v 0 ≤ idxDist i j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), 2 ≤ (critIndices (nodeVals head)).length →
          ∀ i ∈ critIndices (nodeVals head), ∀ j ∈ critIndices (nodeVals head),
            i ≠ j → outEntry v 0 ≤ idxDist i j) := by
    sorry

  /-- Whenever the function returns Ok v, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: if |C| >= 2 then there exist indices i and j in C with i != j such that v[1] = |i-j|.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_9 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      2 ≤ (critIndices (nodeVals head)).length →
        ∃ i ∈ critIndices (nodeVals head), ∃ j ∈ critIndices (nodeVals head),
          i ≠ j ∧ outEntry v 1 = idxDist i j := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), 2 ≤ (critIndices (nodeVals head)).length →
          ∃ i ∈ critIndices (nodeVals head), ∃ j ∈ critIndices (nodeVals head),
            i ≠ j ∧ outEntry v 1 = idxDist i j) := by
    sorry

  /-- Whenever the function returns Ok v, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: if |C| >= 2 then for every indices i and j in C with i != j, v[1] >= |i-j|.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_10 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      2 ≤ (critIndices (nodeVals head)).length →
        ∀ i ∈ critIndices (nodeVals head), ∀ j ∈ critIndices (nodeVals head),
          i ≠ j → idxDist i j ≤ outEntry v 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), 2 ≤ (critIndices (nodeVals head)).length →
          ∀ i ∈ critIndices (nodeVals head), ∀ j ∈ critIndices (nodeVals head),
            i ≠ j → idxDist i j ≤ outEntry v 1) := by
    sorry

  /-- Whenever the function returns Ok v, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: if C has exactly two elements i and j with i < j, then v[0] = j-i and v[1] = j-i.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_11 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      ∀ i j : Nat, i < j → critIndices (nodeVals head) = [i, j] →
        outEntry v 0 = idxDist i j ∧ outEntry v 1 = idxDist i j := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), ∀ i j : Nat, i < j → critIndices (nodeVals head) = [i, j] →
          outEntry v 0 = idxDist i j ∧ outEntry v 1 = idxDist i j) := by
    sorry

  /-- Whenever the function returns Ok v, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: if there exists an index i such that i in C and i+1 in C, then v[0] = 1.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_12 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      (∃ i : Nat, i ∈ critIndices (nodeVals head) ∧ i + 1 ∈ critIndices (nodeVals head)) →
        outEntry v 0 = 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), (∃ i : Nat, i ∈ critIndices (nodeVals head) ∧ i + 1 ∈ critIndices (nodeVals head)) →
          outEntry v 0 = 1) := by
    sorry

  /-- Whenever the function returns Ok v, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: if |C| >= 2, let c_min = min(C) and c_max = max(C); then v[1] = c_max - c_min.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_13 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      2 ≤ (critIndices (nodeVals head)).length →
        outEntry v 1 = listMaxInt 0 (critIdxInts (nodeVals head)) -
          listMinInt 0 (critIdxInts (nodeVals head)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), 2 ≤ (critIndices (nodeVals head)).length →
          outEntry v 1 = listMaxInt 0 (critIdxInts (nodeVals head)) -
            listMinInt 0 (critIdxInts (nodeVals head))) := by
    sorry

  /-- Whenever the function returns Ok v, with C = {i | 0 < i < len(head)-1 and ((head[i] > head[i-1] and head[i] > head[i+1]) or (head[i] < head[i-1] and head[i] < head[i+1]))}: if |C| >= 2, let c_0 < c_1 < ... < c_{k-1} be the elements of C in increasing order, where k = |C|; then v[0] = min{ c_{t+1} - c_t : 0 <= t < k-1 }.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_14 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v) :
      2 ≤ (critIndices (nodeVals head)).length →
        outEntry v 0 = listMinInt 0 (critGaps (nodeVals head)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v), 2 ≤ (critIndices (nodeVals head)).length →
          outEntry v 0 = listMinInt 0 (critGaps (nodeVals head))) := by
    sorry

  /-- Let reverse(head) be the list with the same node values in reverse order. For every head satisfying the preconditions, if the function returns Ok v on head and returns Ok v' on reverse(head), then v = v'.
    Preconditions: head is a finite Nil/Cons list. Let len(head) be its number of nodes and head[i] the value at 0-based index i. Assume 2 <= len(head) <= 100000 and, for every i with 0 <= i < len(head), 1 <= head[i] <= 100000. -/
  theorem spec_15 (head : NodeList)
      (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
      (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
      (v v' : alloc.vec.Vec Std.I64)
      (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v)
      (hres' : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points (reverseNodes head) =
        ok v') :
      v = v' := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (head : NodeList)
        (hlen_lo : 2 ≤ nodeLen head) (hlen_hi : nodeLen head ≤ 100000)
        (hval : ∀ x ∈ nodeVals head, 1 ≤ x ∧ x ≤ 100000)
        (v v' : alloc.vec.Vec Std.I64)
        (hres : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points head = ok v)
        (hres' : Aegis.NodesBetweenCriticalPoints.nodes_between_critical_points (reverseNodes head) =
          ok v'), v = v') := by
    sorry

  end AegisSpec.NodesBetweenCriticalPoints
