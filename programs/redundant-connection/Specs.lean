import Aegis.FindRedundantConnection.Code.Funs

/-!
# Specifications of `Aegis.FindRedundantConnection.find_redundant_connection`

LeetCode problem `redundant-connection`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindRedundantConnection

  def numEdges (edges : Slice (alloc.vec.Vec Std.I64)) : Nat := edges.val.length

  def entry (edges : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    (edges.val[i]!).val[j]!

  def edgePair (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int × Int :=
    (entry edges i 0, entry edges i 1)

  def edgeSeq (edges : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
    (List.range (numEdges edges)).map (edgePair edges)

  def SameUnorderedPair (p q : Int × Int) : Prop :=
    (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1)

  instance decidableSameUnorderedPair (p q : Int × Int) :
      Decidable (SameUnorderedPair p q) := by
    unfold SameUnorderedPair
    infer_instance

  def Adj (E : List (Int × Int)) (u v : Int) : Prop :=
    u ≠ v ∧ ∃ p ∈ E, SameUnorderedPair p (u, v)

  def Reach (E : List (Int × Int)) (u v : Int) : Prop :=
    Relation.ReflTransGen (Adj E) u v

  def ConnectedOn (E : List (Int × Int)) (n : Nat) : Prop :=
    ∀ u v : Int, 1 ≤ u → u ≤ (n : Int) → 1 ≤ v → v ≤ (n : Int) → Reach E u v

  def ConsecutiveOnCycle (c : List Int) (a b : Int) : Prop :=
    (∃ i, i + 1 < c.length ∧ c[i]! = a ∧ c[i + 1]! = b) ∨
      (0 < c.length ∧ c[c.length - 1]! = a ∧ c[0]! = b)

  def EdgeOnCycleList (c : List Int) (a b : Int) : Prop :=
    ConsecutiveOnCycle c a b ∨ ConsecutiveOnCycle c b a

  def IsSimpleCycle (E : List (Int × Int)) (c : List Int) : Prop :=
    3 ≤ c.length ∧ c.Nodup ∧
      (∀ i, i + 1 < c.length → Adj E c[i]! c[i + 1]!) ∧
      Adj E c[c.length - 1]! c[0]!

  def HasSimpleCycle (E : List (Int × Int)) : Prop :=
    ∃ c, IsSimpleCycle E c

  def HasExactlyOneSimpleCycle (E : List (Int × Int)) : Prop :=
    ∃ c, IsSimpleCycle E c ∧
      ∀ c', IsSimpleCycle E c' → ∀ a b, EdgeOnCycleList c' a b ↔ EdgeOnCycleList c a b

  def EdgeOnSimpleCycle (E : List (Int × Int)) (a b : Int) : Prop :=
    ∃ c, IsSimpleCycle E c ∧ EdgeOnCycleList c a b

  def deleteEdge (E : List (Int × Int)) (a b : Int) : List (Int × Int) :=
    E.filter (fun p => decide (¬ SameUnorderedPair p (a, b)))

  def IsTree (E : List (Int × Int)) (n : Nat) : Prop :=
    ConnectedOn E n ∧ ¬ HasSimpleCycle E

  def IsBridge (E : List (Int × Int)) (n : Nat) (a b : Int) : Prop :=
    ¬ ConnectedOn (deleteEdge E a b) n

  def WellFormed (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    3 ≤ numEdges edges ∧ numEdges edges ≤ 1000 ∧
      (∀ i, i < numEdges edges → (edges.val[i]!).val.length = 2) ∧
      (∀ i, i < numEdges edges →
        1 ≤ entry edges i 0 ∧ entry edges i 0 ≤ (numEdges edges : Int) ∧
          1 ≤ entry edges i 1 ∧ entry edges i 1 ≤ (numEdges edges : Int) ∧
          entry edges i 0 ≠ entry edges i 1) ∧
      (∀ i j, i < j → j < numEdges edges →
        ¬ SameUnorderedPair (edgePair edges i) (edgePair edges j)) ∧
      ConnectedOn (edgeSeq edges) (numEdges edges) ∧
      HasExactlyOneSimpleCycle (edgeSeq edges)

  def IsReversal (edges edges_rev : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    numEdges edges_rev = numEdges edges ∧
      ∀ i, i < numEdges edges →
        entry edges_rev i 0 = entry edges i 1 ∧ entry edges_rev i 1 = entry edges i 0

  def frc := Aegis.FindRedundantConnection.find_redundant_connection

  /-- The function returns a result r and there exists an index k with 0 <= k < n such that: len(r) = 2; r[0] = edges[k][0]; r[1] = edges[k][1]; the graph G - edges[k], formed from G by deleting the unordered edge {edges[k][0], edges[k][1]}, is a tree on {1,...,n} (it is connected and has no simple cycle); and for every j with k < j < n, the graph G - edges[j] is not a tree on {1,...,n}.
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_1 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        ∃ k, k < numEdges edges ∧
          (r.val[0]!).val = entry edges k 0 ∧
          (r.val[1]!).val = entry edges k 1 ∧
          IsTree (deleteEdge (edgeSeq edges) (entry edges k 0) (entry edges k 1))
            (numEdges edges) ∧
          ∀ j, k < j → j < numEdges edges →
            ¬ IsTree (deleteEdge (edgeSeq edges) (entry edges j 0) (entry edges j 1))
                (numEdges edges) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          ∃ k, k < numEdges edges ∧
            (r.val[0]!).val = entry edges k 0 ∧
            (r.val[1]!).val = entry edges k 1 ∧
            IsTree (deleteEdge (edgeSeq edges) (entry edges k 0) (entry edges k 1))
              (numEdges edges) ∧
            ∀ j, k < j → j < numEdges edges →
              ¬ IsTree (deleteEdge (edgeSeq edges) (entry edges j 0) (entry edges j 1))
                  (numEdges edges)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_2 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r) := by
    sorry

  /-- The function returns a result r and len(r) = 2.
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_3 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2) := by
    sorry

  /-- The function returns a result r, len(r) = 2, and 1 <= r[0] <= n and 1 <= r[1] <= n and r[0] != r[1].
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_4 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        1 ≤ (r.val[0]!).val ∧ (r.val[0]!).val ≤ (numEdges edges : Int) ∧
        1 ≤ (r.val[1]!).val ∧ (r.val[1]!).val ≤ (numEdges edges : Int) ∧
        (r.val[0]!).val ≠ (r.val[1]!).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          1 ≤ (r.val[0]!).val ∧ (r.val[0]!).val ≤ (numEdges edges : Int) ∧
          1 ≤ (r.val[1]!).val ∧ (r.val[1]!).val ≤ (numEdges edges : Int) ∧
          (r.val[0]!).val ≠ (r.val[1]!).val) := by
    sorry

  /-- The function returns a result r, len(r) = 2, and there exists an index k with 0 <= k < n such that r[0] = edges[k][0] and r[1] = edges[k][1]; thus the returned pair is exactly one of the input edges, in its original orientation.
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_5 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        ∃ k, k < numEdges edges ∧
          (r.val[0]!).val = entry edges k 0 ∧ (r.val[1]!).val = entry edges k 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          ∃ k, k < numEdges edges ∧
            (r.val[0]!).val = entry edges k 0 ∧ (r.val[1]!).val = entry edges k 1) := by
    sorry

  /-- The function returns a result r, len(r) = 2, and there exists an index k with 0 <= k < n such that r[0] = edges[k][0], r[1] = edges[k][1], and G - edges[k] is connected, where G - edges[k] is G with the unordered edge {edges[k][0], edges[k][1]} deleted.
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_6 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        ∃ k, k < numEdges edges ∧
          (r.val[0]!).val = entry edges k 0 ∧
          (r.val[1]!).val = entry edges k 1 ∧
          ConnectedOn (deleteEdge (edgeSeq edges) (entry edges k 0) (entry edges k 1))
            (numEdges edges) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          ∃ k, k < numEdges edges ∧
            (r.val[0]!).val = entry edges k 0 ∧
            (r.val[1]!).val = entry edges k 1 ∧
            ConnectedOn (deleteEdge (edgeSeq edges) (entry edges k 0) (entry edges k 1))
              (numEdges edges)) := by
    sorry

  /-- The function returns a result r, len(r) = 2, and there exists an index k with 0 <= k < n such that r[0] = edges[k][0], r[1] = edges[k][1], and G - edges[k] has no simple cycle.
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_7 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        ∃ k, k < numEdges edges ∧
          (r.val[0]!).val = entry edges k 0 ∧
          (r.val[1]!).val = entry edges k 1 ∧
          ¬ HasSimpleCycle (deleteEdge (edgeSeq edges) (entry edges k 0) (entry edges k 1)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          ∃ k, k < numEdges edges ∧
            (r.val[0]!).val = entry edges k 0 ∧
            (r.val[1]!).val = entry edges k 1 ∧
            ¬ HasSimpleCycle (deleteEdge (edgeSeq edges) (entry edges k 0) (entry edges k 1))) := by
    sorry

  /-- The function returns a result r, len(r) = 2, and the unordered edge {r[0], r[1]} lies on the unique simple cycle of G; that is, there is a simple cycle of G in which r[0] and r[1] are consecutive vertices.
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_8 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        EdgeOnSimpleCycle (edgeSeq edges) (r.val[0]!).val (r.val[1]!).val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          EdgeOnSimpleCycle (edgeSeq edges) (r.val[0]!).val (r.val[1]!).val) := by
    sorry

  /-- The function returns a result r, len(r) = 2, and there exists an index k with 0 <= k < n such that r[0] = edges[k][0], r[1] = edges[k][1], and for every j with k < j < n, the unordered edge {edges[j][0], edges[j][1]} does not lie on the unique simple cycle of G.
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_9 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        ∃ k, k < numEdges edges ∧
          (r.val[0]!).val = entry edges k 0 ∧
          (r.val[1]!).val = entry edges k 1 ∧
          ∀ j, k < j → j < numEdges edges →
            ¬ EdgeOnSimpleCycle (edgeSeq edges) (entry edges j 0) (entry edges j 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          ∃ k, k < numEdges edges ∧
            (r.val[0]!).val = entry edges k 0 ∧
            (r.val[1]!).val = entry edges k 1 ∧
            ∀ j, k < j → j < numEdges edges →
              ¬ EdgeOnSimpleCycle (edgeSeq edges) (entry edges j 0) (entry edges j 1)) := by
    sorry

  /-- The function returns a result r, len(r) = 2, and there exists an index k with 0 <= k < n such that r[0] = edges[k][0], r[1] = edges[k][1], and for every j with k < j < n, the edge edges[j] is a bridge of G; that is, deleting {edges[j][0], edges[j][1]} from G disconnects G.
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_10 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        ∃ k, k < numEdges edges ∧
          (r.val[0]!).val = entry edges k 0 ∧
          (r.val[1]!).val = entry edges k 1 ∧
          ∀ j, k < j → j < numEdges edges →
            IsBridge (edgeSeq edges) (numEdges edges) (entry edges j 0) (entry edges j 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          ∃ k, k < numEdges edges ∧
            (r.val[0]!).val = entry edges k 0 ∧
            (r.val[1]!).val = entry edges k 1 ∧
            ∀ j, k < j → j < numEdges edges →
              IsBridge (edgeSeq edges) (numEdges edges) (entry edges j 0) (entry edges j 1)) := by
    sorry

  /-- The function returns a result r, len(r) = 2, and in G there is a path from r[0] to r[1] that does not use the edge {r[0], r[1]}; equivalently, the returned edge is not a bridge of G.
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_11 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        Reach (deleteEdge (edgeSeq edges) (r.val[0]!).val (r.val[1]!).val)
          (r.val[0]!).val (r.val[1]!).val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          Reach (deleteEdge (edgeSeq edges) (r.val[0]!).val (r.val[1]!).val)
            (r.val[0]!).val (r.val[1]!).val) := by
    sorry

  /-- The function returns a result r, len(r) = 2, and if the unordered edge {edges[n-1][0], edges[n-1][1]} lies on the unique simple cycle of G, then r[0] = edges[n-1][0] and r[1] = edges[n-1][1].
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_12 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        (EdgeOnSimpleCycle (edgeSeq edges) (entry edges (numEdges edges - 1) 0)
            (entry edges (numEdges edges - 1) 1) →
          (r.val[0]!).val = entry edges (numEdges edges - 1) 0 ∧
          (r.val[1]!).val = entry edges (numEdges edges - 1) 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          (EdgeOnSimpleCycle (edgeSeq edges) (entry edges (numEdges edges - 1) 0)
              (entry edges (numEdges edges - 1) 1) →
            (r.val[0]!).val = entry edges (numEdges edges - 1) 0 ∧
            (r.val[1]!).val = entry edges (numEdges edges - 1) 1)) := by
    sorry

  /-- The function returns a result r, len(r) = 2, and if the unordered edge {edges[n-1][0], edges[n-1][1]} does not lie on the unique simple cycle of G, then the unordered pair {r[0], r[1]} is not equal to {edges[n-1][0], edges[n-1][1]}.
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_13 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        (¬ EdgeOnSimpleCycle (edgeSeq edges) (entry edges (numEdges edges - 1) 0)
            (entry edges (numEdges edges - 1) 1) →
          ¬ SameUnorderedPair ((r.val[0]!).val, (r.val[1]!).val)
              (entry edges (numEdges edges - 1) 0, entry edges (numEdges edges - 1) 1)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          (¬ EdgeOnSimpleCycle (edgeSeq edges) (entry edges (numEdges edges - 1) 0)
              (entry edges (numEdges edges - 1) 1) →
            ¬ SameUnorderedPair ((r.val[0]!).val, (r.val[1]!).val)
                (entry edges (numEdges edges - 1) 0, entry edges (numEdges edges - 1) 1))) := by
    sorry

  /-- The function returns a result r, len(r) = 2. Let edges_rev be the input of the same length defined by edges_rev[i][0] = edges[i][1] and edges_rev[i][1] = edges[i][0] for every i with 0 <= i < n, and let r_rev be the result returned by the same function on edges_rev. Then len(r_rev) = 2 and r_rev[0] = r[1] and r_rev[1] = r[0].
    Preconditions: Let n = len(edges). The input satisfies: 3 <= n <= 1000; for every i with 0 <= i < n, len(edges[i]) = 2; for every i with 0 <= i < n, 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n and edges[i][0] != edges[i][1]; for every i,j with 0 <= i < j < n, the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct; the undirected graph G with vertex set {1,...,n} and edge set these n unordered pairs is connected and has exactly one simple cycle. -/
  theorem spec_14 (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges) :
      ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
        ∀ edges_rev : Slice (alloc.vec.Vec Std.I64), IsReversal edges edges_rev →
          ∃ r_rev, frc edges_rev = ok r_rev ∧ r_rev.val.length = 2 ∧
            (r_rev.val[0]!).val = (r.val[1]!).val ∧
            (r_rev.val[1]!).val = (r.val[0]!).val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed edges), ∃ r, frc edges = ok r ∧ r.val.length = 2 ∧
          ∀ edges_rev : Slice (alloc.vec.Vec Std.I64), IsReversal edges edges_rev →
            ∃ r_rev, frc edges_rev = ok r_rev ∧ r_rev.val.length = 2 ∧
              (r_rev.val[0]!).val = (r.val[1]!).val ∧
              (r_rev.val[1]!).val = (r.val[0]!).val) := by
    sorry

  end AegisSpec.FindRedundantConnection
