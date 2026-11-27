import Aegis.GetLonelyNodes.Code.Funs

/-!
# Specifications of `Aegis.GetLonelyNodes.get_lonely_nodes`

LeetCode problem `find-all-the-lonely-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.GetLonelyNodes

  namespace AegisSpec.GetLonelyNodes

  def nodeCount : Tree → Nat
    | .Null => 0
    | .Node _ l r => 1 + nodeCount l + nodeCount r

  def values : Tree → List I64
    | .Null => []
    | .Node v l r => v :: (values l ++ values r)

  def valuesBounded (t : Tree) : Prop :=
    ∀ v ∈ values t, 1 ≤ v.val ∧ v.val ≤ 1000000

  def collectVals : Tree → Bool → List I64
    | .Null, _ => []
    | .Node v l r, isLonely =>
        (if isLonely then [v] else []) ++
          match l with
          | .Null =>
              match r with
              | .Null => []
              | .Node _ _ _ => collectVals r true
          | .Node _ _ _ =>
              match r with
              | .Null => collectVals l true
              | .Node _ _ _ => collectVals l false ++ collectVals r false

  def lonelyValues (t : Tree) : List I64 := collectVals t false

  lemma collectVals_true_eq_node (v : I64) (l r : Tree) :
      collectVals (Tree.Node v l r) true = v :: collectVals (Tree.Node v l r) false := by
    rw [collectVals.eq_def]
    rfl

  def mirror : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node v (mirror r) (mirror l)

  def countOf (l : List I64) (x : ℤ) : Nat :=
    (l.map (fun v => v.val)).countP (fun y => decide (y = x))

  def multisetEq (l₁ l₂ : List I64) : Prop := ∀ x : ℤ, countOf l₁ x = countOf l₂ x

  /-- The function returns Result.ok r, and the multiset of entries of r is exactly the multiset of values of all lonely node occurrences in root. Here a node occurrence is identified by its path from the root (the empty path is the root); an occurrence is lonely iff its path is nonempty and its parent has exactly one non-null child, namely this occurrence. Equivalently, for every integer x, the number of indices i with 0 <= i < len(r) and r[i] = x equals the number of lonely node occurrences in root whose stored value is x. Multiplicity counts duplicate values.
    Preconditions: root is a non-null finite binary tree with between 1 and 1000 nodes, and every node value is an integer v with 1 <= v <= 10^6. -/
  theorem spec_1 (root : Tree) (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
      (hval : valuesBounded root) :
      ∃ r : alloc.vec.Vec I64,
        get_lonely_nodes root = .ok r ∧ multisetEq r.val (lonelyValues root) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
        (hval : valuesBounded root), ∃ r : alloc.vec.Vec I64,
          get_lonely_nodes root = Result.ok r ∧ multisetEq r.val (lonelyValues root)) := by
    sorry

  /-- The function returns Result.ok r for some vector r; it does not panic, overflow, or return an error.
    Preconditions: root is any finite Tree (possibly Null) with at most 1000 nodes; its stored values may be arbitrary 64-bit integers. -/
  theorem spec_2 (root : Tree) (hsize : nodeCount root ≤ 1000) :
      ∃ r : alloc.vec.Vec I64, get_lonely_nodes root = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hsize : nodeCount root ≤ 1000), ∃ r : alloc.vec.Vec I64, get_lonely_nodes root = Result.ok r) := by
    sorry

  /-- Whenever get_lonely_nodes root returns Result.ok r, len(r) equals the number of lonely node occurrences in root, where a node occurrence is lonely exactly when it is a non-root node whose parent has exactly one non-null child.
    Preconditions: root is a non-null finite binary tree with between 1 and 1000 nodes, and every node value is an integer v with 1 <= v <= 10^6. -/
  theorem spec_3 (root : Tree) (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
      (hval : valuesBounded root) :
      ∀ r : alloc.vec.Vec I64, get_lonely_nodes root = .ok r →
        r.val.length = (lonelyValues root).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
        (hval : valuesBounded root), ∀ r : alloc.vec.Vec I64, get_lonely_nodes root = Result.ok r →
          r.val.length = (lonelyValues root).length) := by
    sorry

  /-- Whenever get_lonely_nodes root returns Result.ok r, for every index i with 0 <= i < len(r), the entry r[i] is an integer satisfying 1 <= r[i] <= 10^6.
    Preconditions: root is a non-null finite binary tree with between 1 and 1000 nodes, and every node value is an integer v with 1 <= v <= 10^6. -/
  theorem spec_4 (root : Tree) (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
      (hval : valuesBounded root) :
      ∀ (r : alloc.vec.Vec I64), get_lonely_nodes root = .ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          1 ≤ (r.val[i]'hi).val ∧ (r.val[i]'hi).val ≤ 1000000 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
        (hval : valuesBounded root), ∀ (r : alloc.vec.Vec I64), get_lonely_nodes root = Result.ok r →
          ∀ (i : Nat) (hi : i < r.val.length),
            1 ≤ (r.val[i]'hi).val ∧ (r.val[i]'hi).val ≤ 1000000) := by
    sorry

  /-- Whenever get_lonely_nodes root returns Result.ok r, for every index i with 0 <= i < len(r) there exists a lonely node occurrence in root whose stored value is r[i], where a node occurrence is lonely exactly when it is a non-root node whose parent has exactly one non-null child.
    Preconditions: root is a non-null finite binary tree with between 1 and 1000 nodes, and every node value is an integer v with 1 <= v <= 10^6. -/
  theorem spec_5 (root : Tree) (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
      (hval : valuesBounded root) :
      ∀ (r : alloc.vec.Vec I64), get_lonely_nodes root = .ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          ∃ v : I64, v ∈ lonelyValues root ∧ r.val[i]'hi = v := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
        (hval : valuesBounded root), ∀ (r : alloc.vec.Vec I64), get_lonely_nodes root = Result.ok r →
          ∀ (i : Nat) (hi : i < r.val.length),
            ∃ v : I64, v ∈ lonelyValues root ∧ r.val[i]'hi = v) := by
    sorry

  /-- Whenever get_lonely_nodes root returns Result.ok r, for every lonely node occurrence p in root there exists an index i with 0 <= i < len(r) such that r[i] equals the value stored at p. Here lonely means non-root and the only non-null child of its parent.
    Preconditions: root is a non-null finite binary tree with between 1 and 1000 nodes, and every node value is an integer v with 1 <= v <= 10^6. -/
  theorem spec_6 (root : Tree) (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
      (hval : valuesBounded root) :
      ∀ (r : alloc.vec.Vec I64), get_lonely_nodes root = .ok r →
        ∀ v : I64, v ∈ lonelyValues root →
          ∃ (i : Nat) (hi : i < r.val.length), r.val[i]'hi = v := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
        (hval : valuesBounded root), ∀ (r : alloc.vec.Vec I64), get_lonely_nodes root = Result.ok r →
          ∀ v : I64, v ∈ lonelyValues root →
            ∃ (i : Nat) (hi : i < r.val.length), r.val[i]'hi = v) := by
    sorry

  /-- Whenever get_lonely_nodes Null returns Result.ok r, len(r) = 0.
    Preconditions: root = Null, which is outside the problem's stated nonempty-tree constraints but is a value of the Lean Tree type. -/
  theorem spec_7 (root : Tree) (hroot : root = Tree.Null) :
      ∀ r : alloc.vec.Vec I64, get_lonely_nodes root = .ok r → r.val.length = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (hroot : root = Tree.Null), ∀ r : alloc.vec.Vec I64, get_lonely_nodes root = Result.ok r → r.val.length = 0) := by
    sorry

  /-- Whenever get_lonely_nodes root returns Result.ok r, len(r) <= N - 1, where N is the number of nodes in root.
    Preconditions: root is a non-null finite binary tree with between 1 and 1000 nodes, and every node value is an integer v with 1 <= v <= 10^6. -/
  theorem spec_8 (root : Tree) (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
      (hval : valuesBounded root) :
      ∀ r : alloc.vec.Vec I64, get_lonely_nodes root = .ok r →
        r.val.length ≤ nodeCount root - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
        (hval : valuesBounded root), ∀ r : alloc.vec.Vec I64, get_lonely_nodes root = Result.ok r →
          r.val.length ≤ nodeCount root - 1) := by
    sorry

  /-- Let mirror(root) be the tree obtained recursively by mirror(Null)=Null and mirror(Node(v,L,R))=Node(v,mirror(R),mirror(L)). Whenever get_lonely_nodes root returns Result.ok r and get_lonely_nodes (mirror(root)) returns Result.ok r', the multiset of entries of r equals the multiset of entries of r'.
    Preconditions: root is a non-null finite binary tree with between 1 and 1000 nodes, and every node value is an integer v with 1 <= v <= 10^6. -/
  theorem spec_9 (root : Tree) (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
      (hval : valuesBounded root) :
      ∀ (r r' : alloc.vec.Vec I64),
        get_lonely_nodes root = .ok r →
        get_lonely_nodes (mirror root) = .ok r' → multisetEq r.val r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
        (hval : valuesBounded root), ∀ (r r' : alloc.vec.Vec I64),
          get_lonely_nodes root = Result.ok r →
          get_lonely_nodes (mirror root) = Result.ok r' → multisetEq r.val r'.val) := by
    sorry

  /-- Whenever get_lonely_nodes root returns Result.ok r, the multiset of entries of r is the multiset union, with multiplicity, of the multiset of values of all lonely node occurrences in L, where L is regarded as a tree with its own root not lonely, and the corresponding multiset for R.
    Preconditions: root is a non-null finite binary tree with between 1 and 1000 nodes, every node value is an integer v with 1 <= v <= 10^6, and root = Node(v,L,R) with L and R both non-null. -/
  theorem spec_10 (root : Tree) (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
      (hval : valuesBounded root) (v : I64) (L R : Tree)
      (hroot : root = Tree.Node v L R) (hL : L ≠ Tree.Null) (hR : R ≠ Tree.Null) :
      ∀ r : alloc.vec.Vec I64, get_lonely_nodes root = .ok r →
        multisetEq r.val (lonelyValues L ++ lonelyValues R) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
        (hval : valuesBounded root) (v : I64) (L R : Tree)
        (hroot : root = Tree.Node v L R) (hL : L ≠ Tree.Null) (hR : R ≠ Tree.Null), ∀ r : alloc.vec.Vec I64, get_lonely_nodes root = Result.ok r →
          multisetEq r.val (lonelyValues L ++ lonelyValues R)) := by
    sorry

  /-- Whenever get_lonely_nodes root returns Result.ok r, the multiset of entries of r is obtained from the multiset of values of all lonely node occurrences in C, where C is regarded as a tree with its own root not lonely, by adding one additional occurrence of w.
    Preconditions: root is a non-null finite binary tree with between 1 and 1000 nodes, every node value is an integer v with 1 <= v <= 10^6, and either root = Node(v,L,Null) with L = Node(w,LL,LR), or root = Node(v,Null,R) with R = Node(w,RL,RR). Let C be the unique non-null child and let w be its root value. -/
  theorem spec_11 (root : Tree) (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
      (hval : valuesBounded root) (v w : I64) (LL LR : Tree)
      (hroot : root = Tree.Node v (Tree.Node w LL LR) Tree.Null ∨
               root = Tree.Node v Tree.Null (Tree.Node w LL LR)) :
      ∀ r : alloc.vec.Vec I64, get_lonely_nodes root = .ok r →
        multisetEq r.val (w :: lonelyValues (Tree.Node w LL LR)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 1000)
        (hval : valuesBounded root) (v w : I64) (LL LR : Tree)
        (hroot : root = Tree.Node v (Tree.Node w LL LR) Tree.Null ∨
                 root = Tree.Node v Tree.Null (Tree.Node w LL LR)), ∀ r : alloc.vec.Vec I64, get_lonely_nodes root = Result.ok r →
          multisetEq r.val (w :: lonelyValues (Tree.Node w LL LR))) := by
    sorry

  end AegisSpec.GetLonelyNodes
