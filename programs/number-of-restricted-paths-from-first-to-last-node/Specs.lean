import Aegis.CountRestrictedPaths.Code.Funs

/-!
# Specifications of `Aegis.CountRestrictedPaths.count_restricted_paths`

LeetCode problem `number-of-restricted-paths-from-first-to-last-node`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  namespace AegisSpec.CountRestrictedPaths

  abbrev Row : Type := alloc.vec.Vec Std.I64

  abbrev EdgeArr : Type := Slice Row

  def modulus : Int := 1000000007

  def modulusNat : Nat := 1000000007

  def rowTriple (edges : EdgeArr) (i : Nat) : Option (Int × Int × Int) :=
    match edges.val[i]? with
    | some r =>
      match r.val with
      | [u, v, w] => some (u.val, v.val, w.val)
      | _ => none
    | none => none

  def RowsWellFormed (n : Int) (edges : EdgeArr) : Prop :=
    ∀ i : Nat, i < edges.val.length →
      ∃ u v w : Int, rowTriple edges i = some (u, v, w) ∧
        1 ≤ u ∧ u ≤ n ∧ 1 ≤ v ∧ v ≤ n ∧ u ≠ v ∧ 1 ≤ w ∧ w ≤ 100000

  def EndpointsDistinct (edges : EdgeArr) : Prop :=
    ∀ (i j : Nat), i < edges.val.length → j < edges.val.length → i ≠ j →
      ∀ u v w u' v' w' : Int,
        rowTriple edges i = some (u, v, w) → rowTriple edges j = some (u', v', w') →
          ¬ ((u = u' ∧ v = v') ∨ (u = v' ∧ v = u'))

  def IsEdge (edges : EdgeArr) (a b : Int) (w : Int) : Prop :=
    ∃ i : Nat, ∃ u v : Int,
      rowTriple edges i = some (u, v, w) ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))

  inductive Walk (edges : EdgeArr) : List Int → Int → Prop

    | single (x : Int) : Walk edges [x] 0

    | cons {x y s w : Int} {rest : List Int} :
        IsEdge edges x y w → Walk edges (y :: rest) s → Walk edges (x :: y :: rest) (w + s)

  def Connected (n : Int) (edges : EdgeArr) : Prop :=
    ∀ a b : Int, 1 ≤ a → a ≤ n → 1 ≤ b → b ≤ n →
      ∃ p : List Int, ∃ s : Int, p.head? = some a ∧ p.getLast? = some b ∧ Walk edges p s

  def ValidInput (n : Std.I64) (edges : EdgeArr) : Prop :=
    1 ≤ n.val ∧ n.val ≤ 20000 ∧
      n.val - 1 ≤ (edges.val.length : Int) ∧ (edges.val.length : Int) ≤ 40000 ∧
        RowsWellFormed n.val edges ∧ EndpointsDistinct edges ∧ Connected n.val edges

  def IsShortestDist (edges : EdgeArr) (n : Int) (d : Int → Int) : Prop :=
    d n = 0 ∧
      (∀ x : Int, 1 ≤ x → x ≤ n →
        ∃ p : List Int, ∃ s : Int,
          p.head? = some x ∧ p.getLast? = some n ∧ Walk edges p s ∧ d x = s) ∧
        (∀ (x : Int) (p : List Int) (s : Int),
          p.head? = some x → p.getLast? = some n → Walk edges p s → d x ≤ s)

  def StrictlyDecreasing (d : Int → Int) : List Int → Prop
    | [] => True
    | [_] => True
    | x :: y :: rest => d x > d y ∧ StrictlyDecreasing d (y :: rest)

  def RestrictedPath (edges : EdgeArr) (n : Int) (d : Int → Int) (p : List Int) : Prop :=
    p.head? = some 1 ∧ p.getLast? = some n ∧ (∃ s : Int, Walk edges p s) ∧
      StrictlyDecreasing d p

  def NumRestrictedPaths (edges : EdgeArr) (n : Int) (d : Int → Int) (C : Nat) : Prop :=
    ∃ l : List (List Int), l.length = C ∧ l.Nodup ∧
      (∀ p : List Int, p ∈ l → RestrictedPath edges n d p) ∧
        (∀ p : List Int, RestrictedPath edges n d p → p ∈ l)

  /-- Let d(x) be the minimum, over all paths from node x to node n, of the sum of the weights of the edges on the path (so d(n)=0). A path from 1 to n is a sequence z0,...,zk with k >= 0, z0=1, zk=n, and each consecutive pair {z_i,z_{i+1}} an edge of the graph. It is restricted if d(z_i) > d(z_{i+1}) for every i with 0 <= i < k. Let C be the number of restricted paths from 1 to n. Then the function returns a result r such that 0 <= r < 1000000007 and C = q*1000000007 + r for some integer q >= 0.
    Preconditions: 1 <= n <= 20000; len(edges) is between n-1 and 40000 inclusive; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 100000; for any two distinct indices i,j, the unordered pairs {edges[i][0],edges[i][1]} and {edges[j][0],edges[j][1]} are different; the undirected graph on nodes 1,...,n with these edges is connected (for every a,b in {1,...,n} there is a path between a and b). -/
  theorem spec_1 (n : Std.I64) (edges : EdgeArr) (h : ValidInput n edges) :
      ∃ d : Int → Int, IsShortestDist edges n.val d ∧
        ∃ r : Std.I64,
          Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r ∧
            0 ≤ r.val ∧ r.val < modulus ∧
              ∃ C : Nat, NumRestrictedPaths edges n.val d C ∧
                ∃ q : Int, 0 ≤ q ∧ (C : Int) = q * modulus + r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edges : EdgeArr) (h : ValidInput n edges), ∃ d : Int → Int, IsShortestDist edges n.val d ∧
          ∃ r : Std.I64,
            Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r ∧
              0 ≤ r.val ∧ r.val < modulus ∧
                ∃ C : Nat, NumRestrictedPaths edges n.val d C ∧
                  ∃ q : Int, 0 ≤ q ∧ (C : Int) = q * modulus + r.val) := by
    sorry

  /-- The function returns a result r; equivalently, evaluation does not panic, overflow, or otherwise fail.
    Preconditions: 1 <= n <= 20000; len(edges) is between n-1 and 40000 inclusive; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 100000; for any two distinct indices i,j, the unordered pairs {edges[i][0],edges[i][1]} and {edges[j][0],edges[j][1]} are different; the undirected graph on nodes 1,...,n with these edges is connected (for every a,b in {1,...,n} there is a path between a and b). -/
  theorem spec_2 (n : Std.I64) (edges : EdgeArr) (h : ValidInput n edges) :
      ∃ r : Std.I64, Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edges : EdgeArr) (h : ValidInput n edges), ∃ r : Std.I64, Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: 1 <= n <= 20000; len(edges) is between n-1 and 40000 inclusive; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 100000; for any two distinct indices i,j, the unordered pairs {edges[i][0],edges[i][1]} and {edges[j][0],edges[j][1]} are different; the undirected graph on nodes 1,...,n with these edges is connected (for every a,b in {1,...,n} there is a path between a and b); n >= 3 and len(edges) = n-1. -/
  theorem spec_3 (n : Std.I64) (edges : EdgeArr) (h : ValidInput n edges)
      (hn : 3 ≤ n.val) (hlen : (edges.val.length : Int) = n.val - 1) :
      ∃ r : Std.I64,
        Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edges : EdgeArr) (h : ValidInput n edges)
        (hn : 3 ≤ n.val) (hlen : (edges.val.length : Int) = n.val - 1), ∃ r : Std.I64,
          Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r on (n,edges) and a result r' on (n,edges'), and r = r'.
    Preconditions: 1 <= n <= 20000; len(edges) is between n-1 and 40000 inclusive; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 100000; for any two distinct indices i,j, the unordered pairs {edges[i][0],edges[i][1]} and {edges[j][0],edges[j][1]} are different; the undirected graph on nodes 1,...,n with these edges is connected (for every a,b in {1,...,n} there is a path between a and b). Also edges' is an array of triples with the same length as edges, there is a bijection pi from {0,...,len(edges)-1} to itself such that edges'[i] = edges[pi(i)] for every i, and (n,edges') satisfies the same problem constraints. -/
  theorem spec_4 (n : Std.I64) (edges edges' : EdgeArr) (h : ValidInput n edges)
      (h' : ValidInput n edges') (hlen : edges'.val.length = edges.val.length)
      (hperm : ∃ π : Fin edges.val.length → Fin edges.val.length,
        Function.Bijective π ∧
          ∀ i : Fin edges.val.length, edges'.val[i.val]? = edges.val[(π i).val]?) :
      ∃ r r' : Std.I64,
        Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r ∧
          Aegis.CountRestrictedPaths.count_restricted_paths n edges' = ok r' ∧ r = r' := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edges edges' : EdgeArr) (h : ValidInput n edges)
        (h' : ValidInput n edges') (hlen : edges'.val.length = edges.val.length)
        (hperm : ∃ π : Fin edges.val.length → Fin edges.val.length,
          Function.Bijective π ∧
            ∀ i : Fin edges.val.length, edges'.val[i.val]? = edges.val[(π i).val]?), ∃ r r' : Std.I64,
          Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r ∧
            Aegis.CountRestrictedPaths.count_restricted_paths n edges' = ok r' ∧ r = r') := by
    sorry

  /-- The function returns r on (n,edges) and r' on (n,edges'), and r = r'.
    Preconditions: 1 <= n <= 20000; len(edges) is between n-1 and 40000 inclusive; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 100000; for any two distinct indices i,j, the unordered pairs {edges[i][0],edges[i][1]} and {edges[j][0],edges[j][1]} are different; the undirected graph on nodes 1,...,n with these edges is connected (for every a,b in {1,...,n} there is a path between a and b). Also edges' is an array of triples with the same length as edges, for every i, edges'[i][2] = edges[i][2] and {edges'[i][0],edges'[i][1]} = {edges[i][0],edges[i][1]}, and (n,edges') satisfies the same problem constraints. -/
  theorem spec_5 (n : Std.I64) (edges edges' : EdgeArr) (h : ValidInput n edges)
      (h' : ValidInput n edges') (hlen : edges'.val.length = edges.val.length)
      (hsame : ∀ i : Nat, i < edges.val.length →
        ∃ u v w u' v' w' : Int,
          rowTriple edges i = some (u, v, w) ∧ rowTriple edges' i = some (u', v', w') ∧
            w' = w ∧ ((u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u))) :
      ∃ r r' : Std.I64,
        Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r ∧
          Aegis.CountRestrictedPaths.count_restricted_paths n edges' = ok r' ∧ r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (edges edges' : EdgeArr) (h : ValidInput n edges)
        (h' : ValidInput n edges') (hlen : edges'.val.length = edges.val.length)
        (hsame : ∀ i : Nat, i < edges.val.length →
          ∃ u v w u' v' w' : Int,
            rowTriple edges i = some (u, v, w) ∧ rowTriple edges' i = some (u', v', w') ∧
              w' = w ∧ ((u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u))), ∃ r r' : Std.I64,
          Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r ∧
            Aegis.CountRestrictedPaths.count_restricted_paths n edges' = ok r' ∧ r = r') := by
    sorry

  /-- If the function returns a result r with r = 0, then the number C of restricted paths from 1 to n is a positive multiple of 1000000007.
    Preconditions: 1 <= n <= 20000; len(edges) is between n-1 and 40000 inclusive; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 100000; for any two distinct indices i,j, the unordered pairs {edges[i][0],edges[i][1]} and {edges[j][0],edges[j][1]} are different; the undirected graph on nodes 1,...,n with these edges is connected (for every a,b in {1,...,n} there is a path between a and b). -/
  theorem spec_6 (n : Std.I64) (edges : EdgeArr) (h : ValidInput n edges) :
      ∀ r : Std.I64,
        Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r → r.val = 0 →
          ∃ d : Int → Int, IsShortestDist edges n.val d ∧
            ∃ C : Nat, NumRestrictedPaths edges n.val d C ∧ 1 ≤ C ∧
              ∃ q : Nat, 1 ≤ q ∧ C = q * modulusNat := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (edges : EdgeArr) (h : ValidInput n edges), ∀ r : Std.I64,
          Aegis.CountRestrictedPaths.count_restricted_paths n edges = ok r → r.val = 0 →
            ∃ d : Int → Int, IsShortestDist edges n.val d ∧
              ∃ C : Nat, NumRestrictedPaths edges n.val d C ∧ 1 ≤ C ∧
                ∃ q : Nat, 1 ≤ q ∧ C = q * modulusNat) := by
    sorry

  end AegisSpec.CountRestrictedPaths
