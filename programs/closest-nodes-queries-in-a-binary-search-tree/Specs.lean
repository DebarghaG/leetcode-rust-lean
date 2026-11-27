import Aegis.ClosestNodes.Code.Funs

/-!
# Specifications of `Aegis.ClosestNodes.closest_nodes`

LeetCode problem `closest-nodes-queries-in-a-binary-search-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ClosestNodes

  namespace AegisSpec.ClosestNodes

  def inorderVals : Tree → List ℤ
    | Tree.Null => []
    | Tree.Node v l r => inorderVals l ++ [v.val] ++ inorderVals r

  def nodeCount : Tree → ℕ
    | Tree.Null => 0
    | Tree.Node _ l r => nodeCount l + 1 + nodeCount r

  def IsBST (t : Tree) : Prop := (inorderVals t).Pairwise (fun x y => x ≤ y)

  def Occurs (t : Tree) (x : ℤ) : Prop := x ∈ inorderVals t

  def rowCount (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : ℕ := r.val.length

  def row? (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (List ℤ) :=
    (r.val[i]?).map (fun row => row.val)

  def entry? (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : ℕ) (j : ℕ) : Option ℤ :=
    ((r.val[i]?).bind (fun row => row.val[j]?)).map (fun v => v.val)

  def queryVal? (queries : Slice Std.I64) (i : ℕ) : Option ℤ :=
    (queries.val[i]?).map (fun q => q.val)

  /-- Let V(root) be the set of all values that occur at some node of root. The function returns a result r and, for every i with 0 <= i < len(queries), letting q = queries[i]: len(r) = len(queries); len(r[i]) = 2; if the set {x in V(root) | x <= q} is nonempty then r[i][0] is its maximum, otherwise r[i][0] = -1; and if the set {x in V(root) | x >= q} is nonempty then r[i][1] is its minimum, otherwise r[i][1] = -1.
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_1 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        rowCount r = queries.length ∧
        ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
          ∃ a b : ℤ, row? r i = some [a, b] ∧
            ((a = -1 ∧ ∀ x ∈ inorderVals root, q < x) ∨
             (a ≤ q ∧ Occurs root a ∧ ∀ x ∈ inorderVals root, x ≤ q → x ≤ a)) ∧
            ((b = -1 ∧ ∀ x ∈ inorderVals root, x < q) ∨
             (q ≤ b ∧ Occurs root b ∧ ∀ x ∈ inorderVals root, q ≤ x → b ≤ x)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          rowCount r = queries.length ∧
          ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
            ∃ a b : ℤ, row? r i = some [a, b] ∧
              ((a = -1 ∧ ∀ x ∈ inorderVals root, q < x) ∨
               (a ≤ q ∧ Occurs root a ∧ ∀ x ∈ inorderVals root, x ≤ q → x ≤ a)) ∧
              ((b = -1 ∧ ∀ x ∈ inorderVals root, x < q) ∨
               (q ≤ b ∧ Occurs root b ∧ ∀ x ∈ inorderVals root, q ≤ x → b ≤ x))) := by
    sorry

  /-- The function returns some result r; it does not fail, panic, overflow, or index out of bounds.
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_2 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r) := by
    sorry

  /-- The function returns a result r and len(r) = len(queries).
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_3 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧ rowCount r = queries.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧ rowCount r = queries.length) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), r has an entry at index i and the vector r[i] has length 2.
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_4 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length →
          ∃ row, r.val[i]? = some row ∧ row.val.length = 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length →
            ∃ row, r.val[i]? = some row ∧ row.val.length = 2) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), either r[i][0] = -1 or r[i][0] is a value occurring at some node of root.
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_5 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length →
          ∃ a : ℤ, entry? r i 0 = some a ∧ (a = -1 ∨ Occurs root a) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length →
            ∃ a : ℤ, entry? r i 0 = some a ∧ (a = -1 ∨ Occurs root a)) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), either r[i][1] = -1 or r[i][1] is a value occurring at some node of root.
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_6 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length →
          ∃ b : ℤ, entry? r i 1 = some b ∧ (b = -1 ∨ Occurs root b) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length →
            ∃ b : ℤ, entry? r i 1 = some b ∧ (b = -1 ∨ Occurs root b)) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), if r[i][0] != -1 then r[i][0] <= queries[i] and every tree value x satisfying x <= queries[i] also satisfies x <= r[i][0].
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_7 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
          ∀ a : ℤ, entry? r i 0 = some a → a ≠ -1 →
            a ≤ q ∧ ∀ x ∈ inorderVals root, x ≤ q → x ≤ a := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
            ∀ a : ℤ, entry? r i 0 = some a → a ≠ -1 →
              a ≤ q ∧ ∀ x ∈ inorderVals root, x ≤ q → x ≤ a) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), r[i][0] = -1 if and only if every tree value x satisfies queries[i] < x.
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_8 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
          ∀ a : ℤ, entry? r i 0 = some a →
            (a = -1 ↔ ∀ x ∈ inorderVals root, q < x) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
            ∀ a : ℤ, entry? r i 0 = some a →
              (a = -1 ↔ ∀ x ∈ inorderVals root, q < x)) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), if r[i][1] != -1 then queries[i] <= r[i][1] and every tree value x satisfying queries[i] <= x also satisfies r[i][1] <= x.
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_9 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
          ∀ b : ℤ, entry? r i 1 = some b → b ≠ -1 →
            q ≤ b ∧ ∀ x ∈ inorderVals root, q ≤ x → b ≤ x := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
            ∀ b : ℤ, entry? r i 1 = some b → b ≠ -1 →
              q ≤ b ∧ ∀ x ∈ inorderVals root, q ≤ x → b ≤ x) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), r[i][1] = -1 if and only if every tree value x satisfies x < queries[i].
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_10 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
          ∀ b : ℤ, entry? r i 1 = some b →
            (b = -1 ↔ ∀ x ∈ inorderVals root, x < q) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
            ∀ b : ℤ, entry? r i 1 = some b →
              (b = -1 ↔ ∀ x ∈ inorderVals root, x < q)) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), if queries[i] occurs as a node value in root, then r[i][0] = queries[i] and r[i][1] = queries[i].
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_11 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
          Occurs root q →
            ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
              a = q ∧ b = q := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
            Occurs root q →
              ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
                a = q ∧ b = q) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), if queries[i] is strictly less than every value occurring in root, then r[i][0] = -1 and r[i][1] is the minimum value occurring in root.
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_12 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
          (∀ x ∈ inorderVals root, q < x) →
            ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
              a = -1 ∧ Occurs root b ∧ ∀ x ∈ inorderVals root, b ≤ x := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
            (∀ x ∈ inorderVals root, q < x) →
              ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
                a = -1 ∧ Occurs root b ∧ ∀ x ∈ inorderVals root, b ≤ x) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), if queries[i] is strictly greater than every value occurring in root, then r[i][0] is the maximum value occurring in root and r[i][1] = -1.
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_13 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
          (∀ x ∈ inorderVals root, x < q) →
            ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
              b = -1 ∧ Occurs root a ∧ ∀ x ∈ inorderVals root, x ≤ a := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
            (∀ x ∈ inorderVals root, x < q) →
              ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
                b = -1 ∧ Occurs root a ∧ ∀ x ∈ inorderVals root, x ≤ a) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), each of r[i][0] and r[i][1] is either -1 or lies in the interval [1, 1000000].
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_14 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length →
          ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
            (a = -1 ∨ (1 ≤ a ∧ a ≤ 1000000)) ∧
            (b = -1 ∨ (1 ≤ b ∧ b ≤ 1000000)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length →
            ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
              (a = -1 ∨ (1 ≤ a ∧ a ≤ 1000000)) ∧
              (b = -1 ∨ (1 ≤ b ∧ b ≤ 1000000))) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), if r[i][0] != -1 then r[i][0] <= queries[i], and if r[i][1] != -1 then queries[i] <= r[i][1].
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_15 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
          ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
            (a ≠ -1 → a ≤ q) ∧ (b ≠ -1 → q ≤ b) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length → ∀ q : ℤ, queryVal? queries i = some q →
            ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
              (a ≠ -1 → a ≤ q) ∧ (b ≠ -1 → q ≤ b)) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < len(queries), if r[i][0] != -1 and r[i][1] != -1 then r[i][0] <= r[i][1].
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_16 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i, i < queries.length →
          ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
            a ≠ -1 → b ≠ -1 → a ≤ b := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i, i < queries.length →
            ∀ a b : ℤ, entry? r i 0 = some a → entry? r i 1 = some b →
              a ≠ -1 → b ≠ -1 → a ≤ b) := by
    sorry

  /-- The function returns a result r and, for every i and j with 0 <= i < len(queries), 0 <= j < len(queries), and queries[i] = queries[j], the pairs r[i] and r[j] are equal.
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_17 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i j, i < queries.length → j < queries.length →
          ∀ qi qj : ℤ, queryVal? queries i = some qi → queryVal? queries j = some qj →
            qi = qj → row? r i = row? r j := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i j, i < queries.length → j < queries.length →
            ∀ qi qj : ℤ, queryVal? queries i = some qi → queryVal? queries j = some qj →
              qi = qj → row? r i = row? r j) := by
    sorry

  /-- The function returns a result r and, for every i and j with 0 <= i < len(queries), 0 <= j < len(queries), and queries[i] <= queries[j], if r[i][0] != -1 and r[j][0] != -1 then r[i][0] <= r[j][0].
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_18 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i j, i < queries.length → j < queries.length →
          ∀ qi qj : ℤ, queryVal? queries i = some qi → queryVal? queries j = some qj →
            qi ≤ qj →
              ∀ a b : ℤ, entry? r i 0 = some a → entry? r j 0 = some b →
                a ≠ -1 → b ≠ -1 → a ≤ b := by
    sorry

  theorem spec_18_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i j, i < queries.length → j < queries.length →
            ∀ qi qj : ℤ, queryVal? queries i = some qi → queryVal? queries j = some qj →
              qi ≤ qj →
                ∀ a b : ℤ, entry? r i 0 = some a → entry? r j 0 = some b →
                  a ≠ -1 → b ≠ -1 → a ≤ b) := by
    sorry

  /-- The function returns a result r and, for every i and j with 0 <= i < len(queries), 0 <= j < len(queries), and queries[i] <= queries[j], if r[i][1] != -1 and r[j][1] != -1 then r[i][1] <= r[j][1].
    Preconditions: root is a binary search tree (its in-order traversal of node values is nondecreasing), root has between 2 and 100000 nodes inclusive, every node value is in [1, 1000000], queries is a slice with 1 <= len(queries) <= 100000, and every entry queries[i] satisfies 1 <= queries[i] <= 1000000 for all 0 <= i < len(queries). -/
  theorem spec_19 (root : Tree) (queries : Slice Std.I64)
      (hbst : IsBST root)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
      (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
      (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r, closest_nodes root queries = ok r ∧
        ∀ i j, i < queries.length → j < queries.length →
          ∀ qi qj : ℤ, queryVal? queries i = some qi → queryVal? queries j = some qj →
            qi ≤ qj →
              ∀ a b : ℤ, entry? r i 1 = some a → entry? r j 1 = some b →
                a ≠ -1 → b ≠ -1 → a ≤ b := by
    sorry

  theorem spec_19_neg :
      ¬ (∀ (root : Tree) (queries : Slice Std.I64)
        (hbst : IsBST root)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hvals : ∀ x ∈ inorderVals root, 1 ≤ x ∧ x ≤ 1000000)
        (hlen : 1 ≤ queries.length ∧ queries.length ≤ 100000)
        (hq : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r, closest_nodes root queries = ok r ∧
          ∀ i j, i < queries.length → j < queries.length →
            ∀ qi qj : ℤ, queryVal? queries i = some qi → queryVal? queries j = some qj →
              qi ≤ qj →
                ∀ a b : ℤ, entry? r i 1 = some a → entry? r j 1 = some b →
                  a ≠ -1 → b ≠ -1 → a ≤ b) := by
    sorry

  end AegisSpec.ClosestNodes
