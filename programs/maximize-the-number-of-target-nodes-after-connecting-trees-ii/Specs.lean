import Aegis.MaxTargetNodes.Code.Funs

/-!
# Specifications of `Aegis.MaxTargetNodes.max_target_nodes`

LeetCode problem `maximize-the-number-of-target-nodes-after-connecting-trees-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxTargetNodes

  namespace AegisSpec.MaxTargetNodes

  def edgeList (edges : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    edges.val.map (fun e => e.val)

  def Adj (e : List (List Int)) (a b : Nat) : Prop :=
    ∃ edge ∈ e, ∃ x y : Int, edge = [x, y] ∧
      ((x = (a : Int) ∧ y = (b : Int)) ∨ (x = (b : Int) ∧ y = (a : Int)))

  inductive Walk (e : List (List Int)) : Nat → Nat → Nat → Prop where
    | nil (a : Nat) : Walk e 0 a a
    | cons {k a b c : Nat} : Adj e a b → Walk e k b c → Walk e (k + 1) a c

  noncomputable def dist (e : List (List Int)) (a b : Nat) : Nat :=
    sInf {k : Nat | Walk e k a b}

  noncomputable def color (e : List (List Int)) (v : Nat) : Nat :=
    dist e 0 v % 2

  def countWhere (N : Nat) (p : Nat → Bool) : Nat :=
    ((List.range N).filter p).length

  noncomputable def countColor (e : List (List Int)) (N c : Nat) : Nat :=
    countWhere N (fun v => decide (color e v = c))

  noncomputable def A1 (e : List (List Int)) (N : Nat) : Nat :=
    countColor e N 0

  noncomputable def B1 (e : List (List Int)) (N : Nat) : Nat :=
    N - A1 e N

  noncomputable def M2 (e : List (List Int)) (N : Nat) : Nat :=
    max (A1 e N) (B1 e N)

  noncomputable def s1 (e : List (List Int)) (N i : Nat) : Nat :=
    if color e i = 0 then A1 e N else B1 e N

  noncomputable def countEvenDist (e : List (List Int)) (N u : Nat) : Nat :=
    countWhere N (fun v => decide (dist e u v % 2 = 0))

  noncomputable def countOffsetEven (e : List (List Int)) (N off y : Nat) : Nat :=
    countWhere N (fun v => decide ((off + dist e y v) % 2 = 0))

  def i64Zero : Std.I64 := 0#i64

  def elem (r : alloc.vec.Vec Std.I64) (i : Nat) : Int :=
    (r.val.getD i i64Zero).val

  def sumElems (r : alloc.vec.Vec Std.I64) (N : Nat) : Int :=
    ((List.range N).map (fun i => elem r i)).sum

  def countVal (r : alloc.vec.Vec Std.I64) (N : Nat) (t : Int) : Nat :=
    countWhere N (fun i => decide (elem r i = t))

  def edgeEndpoints (e : List (List Int)) : List (Nat × Nat) :=
    e.filterMap fun edge =>
      match edge with
      | [x, y] => if 0 ≤ x ∧ 0 ≤ y then some (x.toNat, y.toNat) else none
      | _ => none

  def undirectedEdges (e : List (List Int)) : List (Nat × Nat) :=
    (edgeEndpoints e).map fun p => if p.1 ≤ p.2 then p else (p.2, p.1)

  def IsTreeOn (e : List (List Int)) (N : Nat) : Prop :=
    (∀ v, v < N → ∃ k, Walk e k 0 v) ∧
      (∀ p ∈ undirectedEdges e, p.1 ≠ p.2) ∧
        (undirectedEdges e).Nodup ∧
          (undirectedEdges e).length = N - 1

  def EdgesOk (edges : Slice (alloc.vec.Vec Std.I64)) (N : Nat) : Prop :=
    (∀ e ∈ edges.val, e.val.length = 2) ∧
      (∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < (N : Int)) ∧
        IsTreeOn (edgeList edges) N

  noncomputable def valueZero (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) : Nat :=
    A1 (edgeList edges1) n + M2 (edgeList edges2) m

  noncomputable def valueOne (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) : Nat :=
    B1 (edgeList edges1) n + M2 (edgeList edges2) m

  /-- The function returns Ok r with len(r) = n. Define d1(u,v) as the number of edges on the unique simple path between u and v in the tree T1 given by edges1, and d2(u,v) similarly for T2 given by edges2. Define c1(v) = d1(0,v) mod 2 for 0 <= v < n, and c2(v) = d2(0,v) mod 2 for 0 <= v < m. Let A1 = number of v with 0 <= v < n and c1(v)=0, B1 = n - A1; A2 = number of v with 0 <= v < m and c2(v)=0, B2 = m - A2; M2 = max(A2,B2). For 0 <= i < n, let s1(i) = A1 if c1(i)=0 else B1. Then for every i with 0 <= i < n, r[i] = s1(i) + M2.
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m <= 10^5; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_1 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m) (hnmax : n ≤ 10 ^ 5) (hmmax : m ≤ 10 ^ 5)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∃ r : alloc.vec.Vec Std.I64,
        max_target_nodes edges1 edges2 = ok r ∧
          r.val.length = n ∧
            ∀ i, i < n →
              elem r i =
                ((s1 (edgeList edges1) n i + M2 (edgeList edges2) m : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m) (hnmax : n ≤ 10 ^ 5) (hmmax : m ≤ 10 ^ 5)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∃ r : alloc.vec.Vec Std.I64,
          max_target_nodes edges1 edges2 = ok r ∧
            r.val.length = n ∧
              ∀ i, i < n →
                elem r i =
                  ((s1 (edgeList edges1) n i + M2 (edgeList edges2) m : Nat) : Int)) := by
    sorry

  /-- With the notation of spec_1: whenever the function returns a result r, for every i with 0 <= i < n, 1 + M2 <= r[i] <= n - 1 + M2.
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_2 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
        ∀ i, i < n →
          ((1 + M2 (edgeList edges2) m : Nat) : Int) ≤ elem r i ∧
            elem r i ≤ (((n - 1) + M2 (edgeList edges2) m : Nat) : Int) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
          ∀ i, i < n →
            ((1 + M2 (edgeList edges2) m : Nat) : Int) ≤ elem r i ∧
              elem r i ≤ (((n - 1) + M2 (edgeList edges2) m : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, the set { r[i] : 0 <= i < n } has at most two elements.
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_3 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
        ∀ i j k, i < n → j < n → k < n →
          elem r i = elem r j ∨ elem r i = elem r k ∨ elem r j = elem r k := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
          ∀ i j k, i < n → j < n → k < n →
            elem r i = elem r j ∨ elem r i = elem r k ∨ elem r j = elem r k) := by
    sorry

  /-- Let c1(v) = (distance from 0 to v in the first tree) mod 2. Whenever the function returns a result r, for every i,j with 0 <= i,j < n, if c1(i) = c1(j) then r[i] = r[j].
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_4 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
        ∀ i j, i < n → j < n → color (edgeList edges1) i = color (edgeList edges1) j →
          elem r i = elem r j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
          ∀ i j, i < n → j < n → color (edgeList edges1) i = color (edgeList edges1) j →
            elem r i = elem r j) := by
    sorry

  /-- With the notation of spec_1: whenever the function returns a result r, for every i,j with 0 <= i,j < n, if c1(i)=0 and c1(j)=1 then r[i] - r[j] = A1 - B1.
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_5 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
        ∀ i j, i < n → j < n → color (edgeList edges1) i = 0 →
          color (edgeList edges1) j = 1 →
            elem r i - elem r j =
              ((A1 (edgeList edges1) n : Nat) : Int) - ((B1 (edgeList edges1) n : Nat) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
          ∀ i j, i < n → j < n → color (edgeList edges1) i = 0 →
            color (edgeList edges1) j = 1 →
              elem r i - elem r j =
                ((A1 (edgeList edges1) n : Nat) : Int) - ((B1 (edgeList edges1) n : Nat) : Int)) := by
    sorry

  /-- With the notation of spec_1: whenever the function returns a result r, sum_{i=0}^{n-1} r[i] = A1*A1 + B1*B1 + n*M2.
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_6 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
        sumElems r n =
          ((A1 (edgeList edges1) n : Nat) : Int) * ((A1 (edgeList edges1) n : Nat) : Int) +
            ((B1 (edgeList edges1) n : Nat) : Int) * ((B1 (edgeList edges1) n : Nat) : Int) +
              (n : Int) * ((M2 (edgeList edges2) m : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
          sumElems r n =
            ((A1 (edgeList edges1) n : Nat) : Int) * ((A1 (edgeList edges1) n : Nat) : Int) +
              ((B1 (edgeList edges1) n : Nat) : Int) * ((B1 (edgeList edges1) n : Nat) : Int) +
                (n : Int) * ((M2 (edgeList edges2) m : Nat) : Int)) := by
    sorry

  /-- With the notation of spec_1: whenever the function returns a result r, the maximum element of r is max(A1,B1) + M2, and the minimum element of r is min(A1,B1) + M2.
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_7 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
        (∀ i, i < n →
            elem r i ≤
              ((max (A1 (edgeList edges1) n) (B1 (edgeList edges1) n) : Nat) : Int) +
                ((M2 (edgeList edges2) m : Nat) : Int)) ∧
          (∃ i, i < n ∧
            elem r i =
              ((max (A1 (edgeList edges1) n) (B1 (edgeList edges1) n) : Nat) : Int) +
                ((M2 (edgeList edges2) m : Nat) : Int)) ∧
            (∀ i, i < n →
              ((min (A1 (edgeList edges1) n) (B1 (edgeList edges1) n) : Nat) : Int) +
                  ((M2 (edgeList edges2) m : Nat) : Int) ≤ elem r i) ∧
              (∃ i, i < n ∧
                elem r i =
                  ((min (A1 (edgeList edges1) n) (B1 (edgeList edges1) n) : Nat) : Int) +
                    ((M2 (edgeList edges2) m : Nat) : Int)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
          (∀ i, i < n →
              elem r i ≤
                ((max (A1 (edgeList edges1) n) (B1 (edgeList edges1) n) : Nat) : Int) +
                  ((M2 (edgeList edges2) m : Nat) : Int)) ∧
            (∃ i, i < n ∧
              elem r i =
                ((max (A1 (edgeList edges1) n) (B1 (edgeList edges1) n) : Nat) : Int) +
                  ((M2 (edgeList edges2) m : Nat) : Int)) ∧
              (∀ i, i < n →
                ((min (A1 (edgeList edges1) n) (B1 (edgeList edges1) n) : Nat) : Int) +
                    ((M2 (edgeList edges2) m : Nat) : Int) ≤ elem r i) ∧
                (∃ i, i < n ∧
                  elem r i =
                    ((min (A1 (edgeList edges1) n) (B1 (edgeList edges1) n) : Nat) : Int) +
                      ((M2 (edgeList edges2) m : Nat) : Int))) := by
    sorry

  /-- Let d1(u,v) be the distance in the first tree given by edges1, and d2(u,v) the distance in the second tree given by edges2. Whenever the function returns a result r, for every i with 0 <= i < n, there exist x with 0 <= x < n and y with 0 <= y < m such that (number of u with 0 <= u < n and d1(i,u) even) + (number of v with 0 <= v < m and d1(i,x) + 1 + d2(y,v) even) = r[i].
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_8 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
        ∀ i, i < n →
          ∃ x, x < n ∧ ∃ y, y < m ∧
            (((countEvenDist (edgeList edges1) n i +
                countOffsetEven (edgeList edges2) m (dist (edgeList edges1) i x + 1) y : Nat)) : Int) =
              elem r i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
          ∀ i, i < n →
            ∃ x, x < n ∧ ∃ y, y < m ∧
              (((countEvenDist (edgeList edges1) n i +
                  countOffsetEven (edgeList edges2) m (dist (edgeList edges1) i x + 1) y : Nat)) : Int) =
                elem r i) := by
    sorry

  /-- Let d1(u,v) be the distance in the first tree given by edges1, and d2(u,v) the distance in the second tree given by edges2. Whenever the function returns a result r, for every i with 0 <= i < n, every x with 0 <= x < n, and every y with 0 <= y < m, (number of u with 0 <= u < n and d1(i,u) even) + (number of v with 0 <= v < m and d1(i,x) + 1 + d2(y,v) even) <= r[i].
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_9 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
        ∀ i x y, i < n → x < n → y < m →
          (((countEvenDist (edgeList edges1) n i +
              countOffsetEven (edgeList edges2) m (dist (edgeList edges1) i x + 1) y : Nat)) : Int) ≤
            elem r i := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
          ∀ i x y, i < n → x < n → y < m →
            (((countEvenDist (edgeList edges1) n i +
                countOffsetEven (edgeList edges2) m (dist (edgeList edges1) i x + 1) y : Nat)) : Int) ≤
              elem r i) := by
    sorry

  /-- The function returns Ok r (it does not fail) for every input satisfying the preconditions.
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m <= 10^5; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_10 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m) (hnmax : n ≤ 10 ^ 5) (hmmax : m ≤ 10 ^ 5)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∃ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m) (hnmax : n ≤ 10 ^ 5) (hmmax : m ≤ 10 ^ 5)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∃ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r) := by
    sorry

  /-- With the notation of spec_1: whenever the function returns a result r, if n = 2 then r[0] = r[1] = 1 + M2.
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_11 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r → n = 2 →
        elem r 0 = ((1 + M2 (edgeList edges2) m : Nat) : Int) ∧
          elem r 1 = ((1 + M2 (edgeList edges2) m : Nat) : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r → n = 2 →
          elem r 0 = ((1 + M2 (edgeList edges2) m : Nat) : Int) ∧
            elem r 1 = ((1 + M2 (edgeList edges2) m : Nat) : Int)) := by
    sorry

  /-- With the notation of spec_1: whenever the function returns a result r, if m = 2 then for every i with 0 <= i < n, r[i] = s1(i) + 1.
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_12 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r → m = 2 →
        ∀ i, i < n →
          elem r i = ((s1 (edgeList edges1) n i + 1 : Nat) : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r → m = 2 →
          ∀ i, i < n →
            elem r i = ((s1 (edgeList edges1) n i + 1 : Nat) : Int)) := by
    sorry

  /-- With the notation of spec_1: whenever the function returns a result r, if A1 = B1 then for every i with 0 <= i < n, r[i] = A1 + M2.
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_13 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
        A1 (edgeList edges1) n = B1 (edgeList edges1) n →
          ∀ i, i < n →
            elem r i = ((A1 (edgeList edges1) n + M2 (edgeList edges2) m : Nat) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
          A1 (edgeList edges1) n = B1 (edgeList edges1) n →
            ∀ i, i < n →
              elem r i = ((A1 (edgeList edges1) n + M2 (edgeList edges2) m : Nat) : Int)) := by
    sorry

  /-- With the notation of spec_1: whenever the function returns a result r, for every integer t, the number of indices i with 0 <= i < n and r[i] = t is: A1 if t = A1 + M2 and A1 + M2 != B1 + M2; B1 if t = B1 + M2 and A1 + M2 != B1 + M2; n if t = A1 + M2 and A1 + M2 = B1 + M2; and 0 otherwise.
    Preconditions: n = len(edges1)+1, m = len(edges2)+1; 2 <= n,m; each element of edges1 and edges2 has length 2; every edge of edges1 has both endpoints in [0,n) and every edge of edges2 has both endpoints in [0,m); edges1 describes a tree on nodes 0..n-1; edges2 describes a tree on nodes 0..m-1. -/
  theorem spec_14 (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
      (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
      (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
      (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m) :
      ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
        ∀ t : Int,
          countVal r n t =
            (if t = ((valueZero edges1 edges2 n m : Nat) : Int) ∧
                ((valueZero edges1 edges2 n m : Nat) : Int) ≠
                  ((valueOne edges1 edges2 n m : Nat) : Int) then
              A1 (edgeList edges1) n
            else if t = ((valueOne edges1 edges2 n m : Nat) : Int) ∧
                ((valueZero edges1 edges2 n m : Nat) : Int) ≠
                  ((valueOne edges1 edges2 n m : Nat) : Int) then
              B1 (edgeList edges1) n
            else if t = ((valueZero edges1 edges2 n m : Nat) : Int) ∧
                ((valueZero edges1 edges2 n m : Nat) : Int) =
                  ((valueOne edges1 edges2 n m : Nat) : Int) then
              n
            else 0) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
        (hn : n = edges1.val.length + 1) (hm : m = edges2.val.length + 1)
        (hn2 : 2 ≤ n) (hm2 : 2 ≤ m)
        (h1 : EdgesOk edges1 n) (h2 : EdgesOk edges2 m), ∀ r : alloc.vec.Vec Std.I64, max_target_nodes edges1 edges2 = ok r →
          ∀ t : Int,
            countVal r n t =
              (if t = ((valueZero edges1 edges2 n m : Nat) : Int) ∧
                  ((valueZero edges1 edges2 n m : Nat) : Int) ≠
                    ((valueOne edges1 edges2 n m : Nat) : Int) then
                A1 (edgeList edges1) n
              else if t = ((valueOne edges1 edges2 n m : Nat) : Int) ∧
                  ((valueZero edges1 edges2 n m : Nat) : Int) ≠
                    ((valueOne edges1 edges2 n m : Nat) : Int) then
                B1 (edgeList edges1) n
              else if t = ((valueZero edges1 edges2 n m : Nat) : Int) ∧
                  ((valueZero edges1 edges2 n m : Nat) : Int) =
                    ((valueOne edges1 edges2 n m : Nat) : Int) then
                n
              else 0)) := by
    sorry

  end AegisSpec.MaxTargetNodes
