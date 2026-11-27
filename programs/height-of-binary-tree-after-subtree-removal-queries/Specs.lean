import Aegis.TreeQueries.Code.Funs

/-!
# Specifications of `Aegis.TreeQueries.tree_queries`

LeetCode problem `height-of-binary-tree-after-subtree-removal-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.TreeQueries

namespace AegisSpec.TreeQueries

namespace Spec

def nodeCount : Tree → Nat
  | .Null => 0
  | .Node _ l r => nodeCount l + nodeCount r + 1

def values : Tree → List Int
  | .Null => []
  | .Node v l r => v.val :: values l ++ values r

def rootValue : Tree → Int
  | .Null => 0
  | .Node v _ _ => v.val

def heightAux : Tree → Nat
  | .Null => 0
  | .Node _ l r => max (heightAux l) (heightAux r) + 1

def height (t : Tree) : Nat := heightAux t - 1

def removeSubtree : Tree → Int → Tree
  | .Null, _ => .Null
  | .Node v l r, q =>
      if v.val = q then .Null else .Node v (removeSubtree l q) (removeSubtree r q)

def subtreeAt? : Tree → Int → Option Tree
  | .Null, _ => none
  | .Node v l r, q =>
      if v.val = q then some (.Node v l r)
      else
        match subtreeAt? l q with
        | some s => some s
        | none => subtreeAt? r q

def depthOf : Tree → Int → Option Nat
  | .Null, _ => none
  | .Node v l r, q =>
      if v.val = q then some 0
      else
        match depthOf l q with
        | some d => some (d + 1)
        | none => (depthOf r q).map (fun d => d + 1)

def memValue (t : Tree) (y : Int) : Prop := y ∈ values t

def inSubtreeAt (root : Tree) (q y : Int) : Prop :=
  match subtreeAt? root q with
  | some s => memValue s y
  | none => False

def isProperAncestor (root : Tree) (q y : Int) : Prop :=
  q ≠ y ∧ inSubtreeAt root q y

def nthVal (l : List I64) (i : Nat) : Option Int :=
  (l[i]?).map (fun x => x.val)

def ValidTree (t : Tree) : Prop :=
  2 ≤ nodeCount t ∧
    (∀ v, v ∈ values t → 1 ≤ v ∧ v ≤ (nodeCount t : Int)) ∧
    (values t).Nodup

def ValidQueries (root : Tree) (queries : Slice I64) : Prop :=
  1 ≤ queries.val.length ∧
    queries.val.length ≤ min (nodeCount root) 10000 ∧
    (∀ i, i < queries.val.length →
      ∃ q : Int,
        nthVal queries.val i = some q ∧
          1 ≤ q ∧ q ≤ (nodeCount root : Int) ∧ q ≠ rootValue root)

def ValidInput (root : Tree) (queries : Slice I64) : Prop :=
  ValidTree root ∧ ValidQueries root queries

end Spec

/-- Whenever tree_queries(root, queries) returns a result r, len(r) = m and for every i with 0 <= i < m, r[i] = height(R_i), where height(S) is the number of edges in a longest simple path from the root of S to any node of S, so a one-node tree has height 0. Each R_i is formed from the original root independently; no query uses a tree modified by another query.
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; every node value is an integer in {1,...,n}; all node values are distinct, hence the set of values is exactly {1,...,n}. queries is a 0-indexed slice of m 64-bit integers with 1 <= m <= min(n,10^4). For every i with 0 <= i < m, queries[i] is in {1,...,n} and queries[i] is not the value at the root. For each i, let R_i be the tree obtained from the original root by deleting the node whose value is queries[i] and all descendants of that node, keeping all other nodes and all original parent-child edges among them; R_i is nonempty. -/
theorem spec_1 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries)
    (hR : ∀ (i : Nat) (hi : i < queries.val.length) (q : Int),
      Spec.nthVal queries.val i = some q → Spec.removeSubtree root q ≠ .Null) :
    ∃ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r ∧
        r.val.length = queries.val.length ∧
        (∀ (i : Nat), i < queries.val.length →
          ∃ q : Int,
            Spec.nthVal queries.val i = some q ∧
              Spec.nthVal r.val i = some ((Spec.height (Spec.removeSubtree root q)) : Int)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries)
    (hR : ∀ (i : Nat) (hi : i < queries.val.length) (q : Int),
      Spec.nthVal queries.val i = some q → Spec.removeSubtree root q ≠ .Null), ∃ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r ∧
        r.val.length = queries.val.length ∧
        (∀ (i : Nat), i < queries.val.length →
          ∃ q : Int,
            Spec.nthVal queries.val i = some q ∧
              Spec.nthVal r.val i = some ((Spec.height (Spec.removeSubtree root q)) : Int))) := by
  sorry

/-- For every root and queries satisfying the preconditions, tree_queries(root, queries) returns a result (it does not fail, panic, or overflow).
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_2 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∃ r : alloc.vec.Vec I64, tree_queries root queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∃ r : alloc.vec.Vec I64, tree_queries root queries = ok r) := by
  sorry

/-- Whenever tree_queries(root, queries) returns a result r, len(r) = len(queries) = m.
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_3 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r → r.val.length = queries.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r → r.val.length = queries.val.length) := by
  sorry

/-- Whenever tree_queries(root, queries) returns a result r, for every i with 0 <= i < m, r[i] >= 0.
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_4 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q : Int, Spec.nthVal r.val i = some q ∧ 0 ≤ q := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q : Int, Spec.nthVal r.val i = some q ∧ 0 ≤ q) := by
  sorry

/-- Whenever tree_queries(root, queries) returns a result r, for every i with 0 <= i < m, r[i] <= height(root), where height(root) is the number of edges in a longest simple path from the root of the original tree to any node of the original tree.
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_5 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q : Int, Spec.nthVal r.val i = some q ∧ q ≤ ((Spec.height root) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q : Int, Spec.nthVal r.val i = some q ∧ q ≤ ((Spec.height root) : Int)) := by
  sorry

/-- Whenever tree_queries(root, queries) returns a result r, for every i with 0 <= i < m, r[i] <= n - 2.
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_6 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q : Int, Spec.nthVal r.val i = some q ∧ q ≤ ((Spec.nodeCount root) : Int) - 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q : Int, Spec.nthVal r.val i = some q ∧ q ≤ ((Spec.nodeCount root) : Int) - 2) := by
  sorry

/-- Whenever tree_queries(root, queries) returns a result r, for every i with 0 <= i < m, there exists a node y of the original root such that y is not in the subtree rooted at the node whose value is queries[i] (the subtree includes that node and all its descendants), and the number of edges on the original path from the root to y is exactly r[i].
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_7 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q : Int,
              Spec.nthVal queries.val i = some q ∧
                (∃ y : Int,
                  Spec.memValue root y ∧ ¬ Spec.inSubtreeAt root q y ∧
                    (∃ d : Nat,
                      Spec.depthOf root y = some d ∧
                        Spec.nthVal r.val i = some (d : Int))) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q : Int,
              Spec.nthVal queries.val i = some q ∧
                (∃ y : Int,
                  Spec.memValue root y ∧ ¬ Spec.inSubtreeAt root q y ∧
                    (∃ d : Nat,
                      Spec.depthOf root y = some d ∧
                        Spec.nthVal r.val i = some (d : Int)))) := by
  sorry

/-- Whenever tree_queries(root, queries) returns a result r, for every i with 0 <= i < m and every node y of the original root that is not in the subtree rooted at the node whose value is queries[i] (the subtree is that node together with all its descendants), the number of edges on the original path from the root to y is at most r[i].
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_8 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q qr : Int,
              Spec.nthVal queries.val i = some q ∧
                Spec.nthVal r.val i = some qr ∧
                  (∀ y : Int,
                    Spec.memValue root y → ¬ Spec.inSubtreeAt root q y →
                      ∃ d : Nat, Spec.depthOf root y = some d ∧ (d : Int) ≤ qr) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q qr : Int,
              Spec.nthVal queries.val i = some q ∧
                Spec.nthVal r.val i = some qr ∧
                  (∀ y : Int,
                    Spec.memValue root y → ¬ Spec.inSubtreeAt root q y →
                      ∃ d : Nat, Spec.depthOf root y = some d ∧ (d : Int) ≤ qr)) := by
  sorry

/-- Whenever tree_queries(root, queries) returns a result r, for all i and j with 0 <= i < m and 0 <= j < m, if queries[i] = queries[j], then r[i] = r[j].
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_9 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ (i j : Nat) (qi qj ri rj : Int),
          i < queries.val.length →
            j < queries.val.length →
              Spec.nthVal queries.val i = some qi →
                Spec.nthVal queries.val j = some qj →
                  qi = qj →
                    Spec.nthVal r.val i = some ri →
                      Spec.nthVal r.val j = some rj → ri = rj := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ (i j : Nat) (qi qj ri rj : Int),
          i < queries.val.length →
            j < queries.val.length →
              Spec.nthVal queries.val i = some qi →
                Spec.nthVal queries.val j = some qj →
                  qi = qj →
                    Spec.nthVal r.val i = some ri →
                      Spec.nthVal r.val j = some rj → ri = rj) := by
  sorry

/-- Whenever tree_queries(root, queries) returns r and tree_queries(root, queries') returns r', for every i with 0 <= i < m, if queries'[i] = queries[i], then r'[i] = r[i].
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries and queries' are two 0-indexed slices of length m with 1 <= m <= min(n,10^4); every entry of queries and every entry of queries' is in {1,...,n} and differs from the root value. -/
theorem spec_10 (root : Tree) (queries queries' : Slice I64)
    (hvalid : Spec.ValidInput root queries)
    (hvalid' : Spec.ValidInput root queries')
    (hlen : queries.val.length = queries'.val.length) :
    ∀ (r r' : alloc.vec.Vec I64),
      tree_queries root queries = ok r →
        tree_queries root queries' = ok r' →
          ∀ (i : Nat) (q q' : Int),
            i < queries.val.length →
              Spec.nthVal queries.val i = some q →
                Spec.nthVal queries'.val i = some q' →
                  q' = q →
                    ∀ ri ri' : Int,
                      Spec.nthVal r.val i = some ri →
                        Spec.nthVal r'.val i = some ri' → ri' = ri := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (queries queries' : Slice I64)
    (hvalid : Spec.ValidInput root queries)
    (hvalid' : Spec.ValidInput root queries')
    (hlen : queries.val.length = queries'.val.length), ∀ (r r' : alloc.vec.Vec I64),
      tree_queries root queries = ok r →
        tree_queries root queries' = ok r' →
          ∀ (i : Nat) (q q' : Int),
            i < queries.val.length →
              Spec.nthVal queries.val i = some q →
                Spec.nthVal queries'.val i = some q' →
                  q' = q →
                    ∀ ri ri' : Int,
                      Spec.nthVal r.val i = some ri →
                        Spec.nthVal r'.val i = some ri' → ri' = ri) := by
  sorry

/-- Whenever tree_queries(root, queries) returns a result r, for every i with 0 <= i < m, if there exists a node y of the original root whose depth equals height(root) and y is not in the subtree rooted at the node whose value is queries[i] (the subtree is that node together with all its descendants), then r[i] = height(root), where depth is the number of edges from the original root and height(root) is the maximum depth in the original tree.
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_11 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q qr : Int,
              Spec.nthVal queries.val i = some q ∧
                Spec.nthVal r.val i = some qr ∧
                  ((∃ y : Int,
                      Spec.memValue root y ∧
                        Spec.depthOf root y = some (Spec.height root) ∧
                          ¬ Spec.inSubtreeAt root q y) →
                    qr = ((Spec.height root) : Int)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q qr : Int,
              Spec.nthVal queries.val i = some q ∧
                Spec.nthVal r.val i = some qr ∧
                  ((∃ y : Int,
                      Spec.memValue root y ∧
                        Spec.depthOf root y = some (Spec.height root) ∧
                          ¬ Spec.inSubtreeAt root q y) →
                    qr = ((Spec.height root) : Int))) := by
  sorry

/-- Whenever tree_queries(root, queries) returns a result r, for every i with 0 <= i < m, if every node y of the original root whose depth equals height(root) lies in the subtree rooted at the node whose value is queries[i] (the subtree is that node together with all its descendants), then r[i] < height(root), where depth and height(root) are measured in edges from the original root.
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_12 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q qr : Int,
              Spec.nthVal queries.val i = some q ∧
                Spec.nthVal r.val i = some qr ∧
                  ((∀ y : Int,
                      Spec.memValue root y →
                        Spec.depthOf root y = some (Spec.height root) →
                          Spec.inSubtreeAt root q y) →
                    qr < ((Spec.height root) : Int)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q qr : Int,
              Spec.nthVal queries.val i = some q ∧
                Spec.nthVal r.val i = some qr ∧
                  ((∀ y : Int,
                      Spec.memValue root y →
                        Spec.depthOf root y = some (Spec.height root) →
                          Spec.inSubtreeAt root q y) →
                    qr < ((Spec.height root) : Int))) := by
  sorry

/-- Whenever tree_queries(root, queries) returns a result r, for every i with 0 <= i < m, r[i] = 0 if and only if every node of the original root other than the root lies in the subtree rooted at the node whose value is queries[i].
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_13 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q qr : Int,
              Spec.nthVal queries.val i = some q ∧
                Spec.nthVal r.val i = some qr ∧
                  (qr = 0 ↔
                    ∀ y : Int,
                      Spec.memValue root y → y ≠ Spec.rootValue root →
                        Spec.inSubtreeAt root q y) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ i : Nat,
          i < queries.val.length →
            ∃ q qr : Int,
              Spec.nthVal queries.val i = some q ∧
                Spec.nthVal r.val i = some qr ∧
                  (qr = 0 ↔
                    ∀ y : Int,
                      Spec.memValue root y → y ≠ Spec.rootValue root →
                        Spec.inSubtreeAt root q y)) := by
  sorry

/-- Whenever tree_queries(root, queries) returns a result r, for all i and j with 0 <= i < m and 0 <= j < m, if the node whose value is queries[i] is a proper ancestor of the node whose value is queries[j] in the original tree (that is, it lies on the original path from the root to that node and is not that node), then r[i] <= r[j].
  Preconditions: The input satisfies the problem constraints: root is a finite binary tree with n >= 2 nodes; node values are distinct and exactly {1,...,n}; queries has length m with 1 <= m <= min(n,10^4); each queries[i] is in {1,...,n} and differs from the root value. -/
theorem spec_14 (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries) :
    ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ (i j : Nat) (qi qj ri rj : Int),
          i < queries.val.length →
            j < queries.val.length →
              Spec.nthVal queries.val i = some qi →
                Spec.nthVal queries.val j = some qj →
                  Spec.nthVal r.val i = some ri →
                    Spec.nthVal r.val j = some rj →
                      Spec.isProperAncestor root qi qj → ri ≤ rj := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (root : Tree) (queries : Slice I64)
    (hvalid : Spec.ValidInput root queries), ∀ r : alloc.vec.Vec I64,
      tree_queries root queries = ok r →
        ∀ (i j : Nat) (qi qj ri rj : Int),
          i < queries.val.length →
            j < queries.val.length →
              Spec.nthVal queries.val i = some qi →
                Spec.nthVal queries.val j = some qj →
                  Spec.nthVal r.val i = some ri →
                    Spec.nthVal r.val j = some rj →
                      Spec.isProperAncestor root qi qj → ri ≤ rj) := by
  sorry

end AegisSpec.TreeQueries
