import Aegis.ReachableNodes.Code.Funs

/-!
# Specifications of `Aegis.ReachableNodes.reachable_nodes`

LeetCode problem `reachable-nodes-in-subdivided-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ReachableNodes

  abbrev EdgeVec : Type := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

  abbrev EdgeList : Type := Aeneas.Std.Slice EdgeVec

  noncomputable def toBool (p : Prop) : Bool := @decide p (Classical.propDecidable p)

  theorem toBool_eq_true_iff (p : Prop) : toBool p = true ↔ p := by
    classical
    unfold toBool
    exact decide_eq_true_iff

  theorem toBool_eq_false_iff (p : Prop) : toBool p = false ↔ ¬ p := by
    classical
    unfold toBool
    exact decide_eq_false_iff_not

  def entryField (e : EdgeVec) (k : Nat) : Int := (e.val.getD k 0#i64).val

  def edgeU (e : EdgeVec) : Int := entryField e 0

  def edgeV (e : EdgeVec) : Int := entryField e 1

  def edgeC (e : EdgeVec) : Int := entryField e 2

  def triples (edges : EdgeList) : List (Int × Int × Int) :=
    edges.val.map fun e => (edgeU e, edgeV e, edgeC e)

  def edgeAt (edges : EdgeList) (i : Nat) : Option (Int × Int × Int) :=
    (edges.val[i]?).map fun e => (edgeU e, edgeV e, edgeC e)

  def EntriesAreTriples (edges : EdgeList) : Prop :=
    ∀ e ∈ edges.val, e.val.length = 3

  def totalNew (edges : EdgeList) : Int :=
    ((triples edges).map fun t => t.2.2).sum

  def PairsDistinct (edges : EdgeList) : Prop :=
    (triples edges).Pairwise fun a b => ¬ (a.1 = b.1 ∧ a.2.1 = b.2.1)

  def SatConstraints (edges : EdgeList) (maxMoves n : Std.I64) : Prop :=
    1 ≤ n.val ∧ n.val ≤ 3000 ∧
    0 ≤ maxMoves.val ∧ maxMoves.val ≤ 1000000000 ∧
    EntriesAreTriples edges ∧
    (∀ e ∈ edges.val,
      0 ≤ edgeU e ∧ edgeU e < edgeV e ∧ edgeV e < n.val ∧
        0 ≤ edgeC e ∧ edgeC e ≤ 10000) ∧
    PairsDistinct edges ∧
    (edges.val.length : Int) ≤ min (n.val * (n.val - 1) / 2) 10000

  inductive GV where
    | orig (v : Nat)
    | new (i k : Nat)
    deriving DecidableEq

  def EdgeStep (i : Nat) (e : EdgeVec) (x y : GV) : Prop :=
    (1 ≤ (edgeC e).toNat ∧
        ((x = GV.orig (edgeU e).toNat ∧ y = GV.new i 1) ∨
         (y = GV.orig (edgeU e).toNat ∧ x = GV.new i 1) ∨
         (x = GV.orig (edgeV e).toNat ∧ y = GV.new i (edgeC e).toNat) ∨
         (y = GV.orig (edgeV e).toNat ∧ x = GV.new i (edgeC e).toNat) ∨
         (∃ k : Nat, 1 ≤ k ∧ k + 1 ≤ (edgeC e).toNat ∧
           ((x = GV.new i k ∧ y = GV.new i (k + 1)) ∨
            (y = GV.new i k ∧ x = GV.new i (k + 1)))))) ∨
      (edgeC e = 0 ∧
        ((x = GV.orig (edgeU e).toNat ∧ y = GV.orig (edgeV e).toNat) ∨
         (y = GV.orig (edgeU e).toNat ∧ x = GV.orig (edgeV e).toNat)))

  def GStep (edges : EdgeList) (x y : GV) : Prop :=
    ∃ (i : Nat) (e : EdgeVec), edges.val[i]? = some e ∧ EdgeStep i e x y

  inductive GReach (edges : EdgeList) : GV → GV → Nat → Prop where
    | refl (a : GV) : GReach edges a a 0
    | step {a b c : GV} {k : Nat} :
        GReach edges a b k → GStep edges b c → GReach edges a c (k + 1)

  def GDistLe (edges : EdgeList) (y : GV) (M : Int) : Prop :=
    ∃ k : Nat, (k : Int) ≤ M ∧ GReach edges (GV.orig 0) y k

  def GVerts (edges : EdgeList) (n : Int) : List GV :=
    (List.range n.toNat).map GV.orig ++
      (edges.val.zipIdx.flatMap fun (e, i) =>
        (List.range (edgeC e).toNat).map fun k => GV.new i (k + 1))

  noncomputable def countReach (edges : EdgeList) (n M : Int) : Nat :=
    ((GVerts edges n).filter fun y => toBool (GDistLe edges y M)).length

  def OStep (edges : EdgeList) (a b : Nat) : Prop :=
    ∃ (i : Nat) (e : EdgeVec), edges.val[i]? = some e ∧
      ((a = (edgeU e).toNat ∧ b = (edgeV e).toNat) ∨
       (b = (edgeU e).toNat ∧ a = (edgeV e).toNat))

  inductive OReach (edges : EdgeList) : Nat → Nat → Prop where
    | refl (a : Nat) : OReach edges a a
    | step {a b c : Nat} : OReach edges a b → OStep edges b c → OReach edges a c

  def inC (edges : EdgeList) (n : Int) (v : Int) : Prop :=
    0 ≤ v ∧ v < n ∧ OReach edges 0 v.toNat

  noncomputable def compSize (edges : EdgeList) (n : Int) : Nat :=
    ((List.range n.toNat).filter fun v => toBool (OReach edges 0 v)).length

  noncomputable def crossSum (edges : EdgeList) (n : Int) : Int :=
    (((triples edges).filter
        (fun t => toBool (inC edges n t.1 ∨ inC edges n t.2.1))).map
      fun t => t.2.2).sum

  noncomputable def S7Size (edges : EdgeList) (n : Int) : Int :=
    (compSize edges n : Int) + crossSum edges n

  def WStep (edges : EdgeList) (a b : Nat) (w : Nat) : Prop :=
    ∃ (i : Nat) (e : EdgeVec), edges.val[i]? = some e ∧ w = (edgeC e).toNat + 1 ∧
      ((a = (edgeU e).toNat ∧ b = (edgeV e).toNat) ∨
       (b = (edgeU e).toNat ∧ a = (edgeV e).toNat))

  inductive WReach (edges : EdgeList) : Nat → Nat → Nat → Prop where
    | refl (a : Nat) : WReach edges a a 0
    | step {a b c : Nat} {w1 w2 : Nat} :
        WReach edges a b w1 → WStep edges b c w2 → WReach edges a c (w1 + w2)

  def WDistLe (edges : EdgeList) (v : Nat) (M : Int) : Prop :=
    ∃ w : Nat, (w : Int) ≤ M ∧ WReach edges 0 v w

  def WDistLeAdd (edges : EdgeList) (v : Nat) (t : Int) (M : Int) : Prop :=
    ∃ w : Nat, (w : Int) + t ≤ M ∧ WReach edges 0 v w

  /-- Construct the subdivided graph G' from n and edges as follows. Its vertices are the original vertices 0,...,n-1 together with, for each edge e_i = [u_i,v_i,c_i], c_i distinct new vertices x_{i,1},...,x_{i,c_i}. Its edges are, for each i, the unit-length path u_i - x_{i,1} - x_{i,2} - ... - x_{i,c_i} - v_i (when c_i=0 this is the single edge u_i-v_i). For a vertex y of G', let dist(y) be the minimum number of edges on a path from 0 to y in G', or infinity if no such path exists. Whenever reachable_nodes returns a result r, r equals the number of vertices y of G' with dist(y) <= maxMoves.
    Preconditions: All inputs satisfy the problem Constraints: 1 <= n <= 3000; 0 <= maxMoves <= 10^9; edges is a list of triples [u_i,v_i,c_i] with 0 <= u_i < v_i < n, 0 <= c_i <= 10^4, no unordered pair {u_i,v_i} occurs twice, and len(edges) <= min(n*(n-1)/2, 10^4). -/
  theorem spec_1 (edges : EdgeList) (maxMoves n : Std.I64)
      (h : SatConstraints edges maxMoves n) :
      ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
        r.val = (countReach edges n.val maxMoves.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (edges : EdgeList) (maxMoves n : Std.I64)
        (h : SatConstraints edges maxMoves n), ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
          r.val = (countReach edges n.val maxMoves.val : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, reachable_nodes returns an ok result of type i64 and does not fail by overflow, panic, out-of-bounds access, or any other runtime error.
    Preconditions: All inputs satisfy the problem Constraints: 1 <= n <= 3000; 0 <= maxMoves <= 10^9; edges is a list of triples [u_i,v_i,c_i] with 0 <= u_i < v_i < n, 0 <= c_i <= 10^4, no unordered pair {u_i,v_i} occurs twice, and len(edges) <= min(n*(n-1)/2, 10^4). -/
  theorem spec_2 (edges : EdgeList) (maxMoves n : Std.I64)
      (h : SatConstraints edges maxMoves n) :
      ∃ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (edges : EdgeList) (maxMoves n : Std.I64)
        (h : SatConstraints edges maxMoves n), ∃ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r) := by
    sorry

  /-- Whenever reachable_nodes returns r, 1 <= r <= n + sum_{i=0}^{len(edges)-1} edges[i][2].
    Preconditions: All inputs satisfy the problem Constraints: 1 <= n <= 3000; 0 <= maxMoves <= 10^9; edges is a list of triples [u_i,v_i,c_i] with 0 <= u_i < v_i < n, 0 <= c_i <= 10^4, no unordered pair {u_i,v_i} occurs twice, and len(edges) <= min(n*(n-1)/2, 10^4). -/
  theorem spec_3 (edges : EdgeList) (maxMoves n : Std.I64)
      (h : SatConstraints edges maxMoves n) :
      ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
        1 ≤ r.val ∧ r.val ≤ n.val + totalNew edges := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (edges : EdgeList) (maxMoves n : Std.I64)
        (h : SatConstraints edges maxMoves n), ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
          1 ≤ r.val ∧ r.val ≤ n.val + totalNew edges) := by
    sorry

  /-- Let C be the set of original vertices v with 0 <= v < n that are connected to 0 in the undirected graph on vertices 0,...,n-1 having an edge {u_i,v_i} for each i. Let S = |C| + sum_{i: u_i in C or v_i in C} edges[i][2]. If maxMoves >= S - 1, then whenever reachable_nodes returns r, r = S.
    Preconditions: All inputs satisfy the problem Constraints: 1 <= n <= 3000; 0 <= maxMoves <= 10^9; edges is a list of triples [u_i,v_i,c_i] with 0 <= u_i < v_i < n, 0 <= c_i <= 10^4, no unordered pair {u_i,v_i} occurs twice, and len(edges) <= min(n*(n-1)/2, 10^4). -/
  theorem spec_4 (edges : EdgeList) (maxMoves n : Std.I64)
      (h : SatConstraints edges maxMoves n)
      (hM : S7Size edges n.val - 1 ≤ maxMoves.val) :
      ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
        r.val = S7Size edges n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (edges : EdgeList) (maxMoves n : Std.I64)
        (h : SatConstraints edges maxMoves n)
        (hM : S7Size edges n.val - 1 ≤ maxMoves.val), ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
          r.val = S7Size edges n.val) := by
    sorry

  /-- Let r1 be the result of reachable_nodes(edges, m1, n) and r2 be the result of reachable_nodes(edges, m2, n). Whenever both calls return results, r1 <= r2.
    Preconditions: All inputs satisfy the problem Constraints: 1 <= n <= 3000; 0 <= maxMoves <= 10^9; edges is a list of triples [u_i,v_i,c_i] with 0 <= u_i < v_i < n, 0 <= c_i <= 10^4, no unordered pair {u_i,v_i} occurs twice, and len(edges) <= min(n*(n-1)/2, 10^4). Also 0 <= m1 <= m2 <= 10^9. -/
  theorem spec_5 (edges : EdgeList) (n m1 m2 : Std.I64)
      (h1 : SatConstraints edges m1 n) (h2 : SatConstraints edges m2 n)
      (hm : m1.val ≤ m2.val) :
      ∀ r1 r2, Aegis.ReachableNodes.reachable_nodes edges m1 n = ok r1 →
        Aegis.ReachableNodes.reachable_nodes edges m2 n = ok r2 →
        r1.val ≤ r2.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (edges : EdgeList) (n m1 m2 : Std.I64)
        (h1 : SatConstraints edges m1 n) (h2 : SatConstraints edges m2 n)
        (hm : m1.val ≤ m2.val), ∀ r1 r2, Aegis.ReachableNodes.reachable_nodes edges m1 n = ok r1 →
          Aegis.ReachableNodes.reachable_nodes edges m2 n = ok r2 →
          r1.val ≤ r2.val) := by
    sorry

  /-- Whenever reachable_nodes(edges, maxMoves, n) returns r and reachable_nodes(edges', maxMoves, n) returns r', we have r = r'.
    Preconditions: All inputs satisfy the problem Constraints: 1 <= n <= 3000; 0 <= maxMoves <= 10^9; edges is a list of triples [u_i,v_i,c_i] with 0 <= u_i < v_i < n, 0 <= c_i <= 10^4, no unordered pair {u_i,v_i} occurs twice, and len(edges) <= min(n*(n-1)/2, 10^4). Also edges' is any permutation of the list edges. -/
  theorem spec_6 (edges edges' : EdgeList) (maxMoves n : Std.I64)
      (h : SatConstraints edges maxMoves n) (hp : edges'.val.Perm edges.val) :
      ∀ r r', Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
        Aegis.ReachableNodes.reachable_nodes edges' maxMoves n = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (edges edges' : EdgeList) (maxMoves n : Std.I64)
        (h : SatConstraints edges maxMoves n) (hp : edges'.val.Perm edges.val), ∀ r r', Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
          Aegis.ReachableNodes.reachable_nodes edges' maxMoves n = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Let edges' be edges with entry i removed. Whenever reachable_nodes(edges, maxMoves, n) returns r and reachable_nodes(edges', maxMoves, n) returns r', we have r = r'.
    Preconditions: All inputs satisfy the problem Constraints: 1 <= n <= 3000; 0 <= maxMoves <= 10^9; edges is a list of triples [u_i,v_i,c_i] with 0 <= u_i < v_i < n, 0 <= c_i <= 10^4, no unordered pair {u_i,v_i} occurs twice, and len(edges) <= min(n*(n-1)/2, 10^4). Also i is an index with 0 <= i < len(edges); C is the set of original vertices connected to 0 in the original graph using all edges and ignoring cnt; neither u_i nor v_i belongs to C. -/
  theorem spec_7 (edges edges' : EdgeList) (maxMoves n : Std.I64) (i : Nat)
      (h : SatConstraints edges maxMoves n)
      (hi : i < edges.val.length)
      (hC : ∀ u v c, edgeAt edges i = some (u, v, c) →
        ¬ inC edges n.val u ∧ ¬ inC edges n.val v)
      (he' : edges'.val = edges.val.eraseIdx i) :
      ∀ r r', Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
        Aegis.ReachableNodes.reachable_nodes edges' maxMoves n = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (edges edges' : EdgeList) (maxMoves n : Std.I64) (i : Nat)
        (h : SatConstraints edges maxMoves n)
        (hi : i < edges.val.length)
        (hC : ∀ u v c, edgeAt edges i = some (u, v, c) →
          ¬ inC edges n.val u ∧ ¬ inC edges n.val v)
        (he' : edges'.val = edges.val.eraseIdx i), ∀ r r', Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
          Aegis.ReachableNodes.reachable_nodes edges' maxMoves n = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Let n' = n + 1. Whenever reachable_nodes(edges, maxMoves, n) returns r and reachable_nodes(edges, maxMoves, n') returns r', we have r = r'.
    Preconditions: All inputs satisfy the problem Constraints: 1 <= n <= 3000; 0 <= maxMoves <= 10^9; edges is a list of triples [u_i,v_i,c_i] with 0 <= u_i < v_i < n, 0 <= c_i <= 10^4, no unordered pair {u_i,v_i} occurs twice, and len(edges) <= min(n*(n-1)/2, 10^4). Also n < 3000. -/
  theorem spec_8 (edges : EdgeList) (maxMoves n n' : Std.I64)
      (h : SatConstraints edges maxMoves n) (hn : n.val < 3000)
      (hn' : n'.val = n.val + 1) :
      ∀ r r', Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
        Aegis.ReachableNodes.reachable_nodes edges maxMoves n' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (edges : EdgeList) (maxMoves n n' : Std.I64)
        (h : SatConstraints edges maxMoves n) (hn : n.val < 3000)
        (hn' : n'.val = n.val + 1), ∀ r r', Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
          Aegis.ReachableNodes.reachable_nodes edges maxMoves n' = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Define an undirected weighted graph W on vertices 0,...,n-1 by giving each edge i = [u_i,v_i,c_i] weight c_i+1. For a vertex v, let D(v) be the minimum total weight of a path from 0 to v in W, or infinity if no such path exists. Whenever reachable_nodes returns r, let R be the set of vertices of the subdivided graph G' (as in spec_1) with dist <= maxMoves, so |R| = r. For every original vertex v with 0 <= v < n, v is in R if and only if D(v) <= maxMoves.
    Preconditions: All inputs satisfy the problem Constraints: 1 <= n <= 3000; 0 <= maxMoves <= 10^9; edges is a list of triples [u_i,v_i,c_i] with 0 <= u_i < v_i < n, 0 <= c_i <= 10^4, no unordered pair {u_i,v_i} occurs twice, and len(edges) <= min(n*(n-1)/2, 10^4). -/
  theorem spec_9 (edges : EdgeList) (maxMoves n : Std.I64)
      (h : SatConstraints edges maxMoves n) :
      ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
        r.val = (countReach edges n.val maxMoves.val : Int) ∧
          ∀ v : Nat, v < n.val.toNat →
            (GDistLe edges (GV.orig v) maxMoves.val ↔ WDistLe edges v maxMoves.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (edges : EdgeList) (maxMoves n : Std.I64)
        (h : SatConstraints edges maxMoves n), ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
          r.val = (countReach edges n.val maxMoves.val : Int) ∧
            ∀ v : Nat, v < n.val.toNat →
              (GDistLe edges (GV.orig v) maxMoves.val ↔ WDistLe edges v maxMoves.val)) := by
    sorry

  /-- Let G' be the subdivided graph, and for each edge i let x_{i,k} be the k-th new vertex on the path from u_i to v_i. Define an undirected weighted graph W on vertices 0,...,n-1 by giving edge i weight c_i+1, and let D(v) be the minimum total weight of a path from 0 to v in W, or infinity if no such path exists; take infinity + t = infinity for every integer t and treat infinity as larger than all integers in min. Whenever reachable_nodes returns r, let R be the set of vertices of G' with dist <= maxMoves, so |R| = r. For every edge i and every k with 1 <= k <= edges[i][2], x_{i,k} is in R if and only if min(D(u_i) + k, D(v_i) + edges[i][2] + 1 - k) <= maxMoves.
    Preconditions: All inputs satisfy the problem Constraints: 1 <= n <= 3000; 0 <= maxMoves <= 10^9; edges is a list of triples [u_i,v_i,c_i] with 0 <= u_i < v_i < n, 0 <= c_i <= 10^4, no unordered pair {u_i,v_i} occurs twice, and len(edges) <= min(n*(n-1)/2, 10^4). -/
  theorem spec_10 (edges : EdgeList) (maxMoves n : Std.I64)
      (h : SatConstraints edges maxMoves n) :
      ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
        r.val = (countReach edges n.val maxMoves.val : Int) ∧
          ∀ (i k : Nat) (e : EdgeVec), edges.val[i]? = some e →
            1 ≤ k → k ≤ (edgeC e).toNat →
              (GDistLe edges (GV.new i k) maxMoves.val ↔
                (WDistLeAdd edges (edgeU e).toNat (k : Int) maxMoves.val ∨
                  WDistLeAdd edges (edgeV e).toNat
                    (edgeC e + 1 - (k : Int)) maxMoves.val)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (edges : EdgeList) (maxMoves n : Std.I64)
        (h : SatConstraints edges maxMoves n), ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r →
          r.val = (countReach edges n.val maxMoves.val : Int) ∧
            ∀ (i k : Nat) (e : EdgeVec), edges.val[i]? = some e →
              1 ≤ k → k ≤ (edgeC e).toNat →
                (GDistLe edges (GV.new i k) maxMoves.val ↔
                  (WDistLeAdd edges (edgeU e).toNat (k : Int) maxMoves.val ∨
                    WDistLeAdd edges (edgeV e).toNat
                      (edgeC e + 1 - (k : Int)) maxMoves.val))) := by
    sorry

  /-- Whenever reachable_nodes returns r, r >= 2.
    Preconditions: All inputs satisfy the problem Constraints: 1 <= n <= 3000; 0 <= maxMoves <= 10^9; edges is a list of triples [u_i,v_i,c_i] with 0 <= u_i < v_i < n, 0 <= c_i <= 10^4, no unordered pair {u_i,v_i} occurs twice, and len(edges) <= min(n*(n-1)/2, 10^4). Also maxMoves >= 1 and there exists an index i with 0 <= i < len(edges) and (edges[i][0] = 0 or edges[i][1] = 0). -/
  theorem spec_11 (edges : EdgeList) (maxMoves n : Std.I64)
      (h : SatConstraints edges maxMoves n) (hM : 1 ≤ maxMoves.val)
      (h0 : ∃ (i : Nat) (u v c : Int), edgeAt edges i = some (u, v, c) ∧ (u = 0 ∨ v = 0)) :
      ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r → 2 ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (edges : EdgeList) (maxMoves n : Std.I64)
        (h : SatConstraints edges maxMoves n) (hM : 1 ≤ maxMoves.val)
        (h0 : ∃ (i : Nat) (u v c : Int), edgeAt edges i = some (u, v, c) ∧ (u = 0 ∨ v = 0)), ∀ r, Aegis.ReachableNodes.reachable_nodes edges maxMoves n = ok r → 2 ≤ r.val) := by
    sorry

  end AegisSpec.ReachableNodes
