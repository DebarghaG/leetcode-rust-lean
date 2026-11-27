import Aegis.CountGreatEnoughNodes.Code.Funs

/-!
# Specifications of `Aegis.CountGreatEnoughNodes.count_great_enough_nodes`

LeetCode problem `count-nodes-that-are-great-enough`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountGreatEnoughNodes

  open Aegis.CountGreatEnoughNodes

  inductive ValTree where

    | null : ValTree

    | node : Int → ValTree → ValTree → ValTree
    deriving DecidableEq, Repr

  namespace ValTree

  def size : ValTree → Nat
    | .null => 0
    | .node _ l r => ValTree.size l + ValTree.size r + 1

  end ValTree

  def nodeSize (l r : ValTree) : Nat := ValTree.size l + ValTree.size r + 1

  def lessCount (v : Int) : ValTree → Nat
    | .null => 0
    | .node w l r => lessCount v l + lessCount v r + (if w < v then 1 else 0)

  def nodeLessCount (v : Int) (l r : ValTree) : Nat := lessCount v l + lessCount v r

  def greatEnough (k : Int) : ValTree → Nat
    | .null => 0
    | .node v l r =>
      greatEnough k l + greatEnough k r +
        (if k ≤ ((nodeSize l r : Nat) : Int) ∧ k ≤ ((nodeLessCount v l r : Nat) : Int) then 1 else 0)

  def existsGreatEnough (k : Int) : ValTree → Prop
    | .null => False
    | .node v l r =>
      existsGreatEnough k l ∨ existsGreatEnough k r ∨
        (k ≤ ((nodeSize l r : Nat) : Int) ∧ k ≤ ((nodeLessCount v l r : Nat) : Int))

  def countSizeAtLeast (k : Int) : ValTree → Nat
    | .null => 0
    | .node _ l r =>
      countSizeAtLeast k l + countSizeAtLeast k r +
        (if k ≤ ((nodeSize l r : Nat) : Int) then 1 else 0)

  def countWithSmallerBelow : ValTree → Nat
    | .null => 0
    | .node v l r =>
      countWithSmallerBelow l + countWithSmallerBelow r +
        (if 0 < nodeLessCount v l r then 1 else 0)

  def valuesBetween (lo hi : Int) : ValTree → Prop
    | .null => True
    | .node v l r => lo ≤ v ∧ v ≤ hi ∧ valuesBetween lo hi l ∧ valuesBetween lo hi r

  def mapValues (f : Int → Int) : ValTree → ValTree
    | .null => .null
    | .node v l r => .node (f v) (mapValues f l) (mapValues f r)

  def shift (c : Int) (t : ValTree) : ValTree := mapValues (fun v => v + c) t

  def mirror : ValTree → ValTree
    | .null => .null
    | .node v l r => .node v (mirror r) (mirror l)

  def IsUnder (u : ValTree) : ValTree → Prop
    | .null => False
    | .node v l r => u = .node v l r ∨ IsUnder u l ∨ IsUnder u r

  def ofTree : Tree → ValTree
    | .Null => .null
    | .Node v l r => .node v.val (ofTree l) (ofTree r)

  /-- Whenever the function returns a result r, r equals the number of node occurrences u of root that are great enough for k, i.e. r = #{u : sz(u) >= k and less(u) >= k}.
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k is an i64 with 1 <= k <= 10. For a node occurrence u of root, let sub(u) be the set of node occurrences in the subtree rooted at u, including u; let sz(u)=|sub(u)|; let less(u)=#{w in sub(u) : val(w) < val(u)}. A node occurrence u is great enough for k iff sz(u) >= k and less(u) >= k. -/
  theorem spec_1 (root : Tree) (k : I64) (r : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
      (hres : count_great_enough_nodes root k = ok r) :
      r.val = (greatEnough k.val (ofTree root) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (k : I64) (r : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
        (hres : count_great_enough_nodes root k = ok r), r.val = (greatEnough k.val (ofTree root) : Int)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail: there is no panic, no out-of-bounds access, and no 64-bit integer overflow during the computation.
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k is an i64 with 1 <= k <= 10. -/
  theorem spec_2 (root : Tree) (k : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10) :
      ∃ r : I64, count_great_enough_nodes root k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (k : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10), ∃ r : I64, count_great_enough_nodes root k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= N(root).
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k is an i64 with 1 <= k <= 10. Let N(root) be the number of node occurrences in root. -/
  theorem spec_3 (root : Tree) (k : I64) (r : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
      (hres : count_great_enough_nodes root k = ok r) :
      0 ≤ r.val ∧ r.val ≤ ((ofTree root).size : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (k : I64) (r : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
        (hres : count_great_enough_nodes root k = ok r), 0 ≤ r.val ∧ r.val ≤ ((ofTree root).size : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= #{u : u is a node occurrence of root and sz(u) >= k}.
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k is an i64 with 1 <= k <= 10. For a node occurrence u, let sz(u) be the number of node occurrences in the subtree rooted at u, including u. -/
  theorem spec_4 (root : Tree) (k : I64) (r : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
      (hres : count_great_enough_nodes root k = ok r) :
      r.val ≤ (countSizeAtLeast k.val (ofTree root) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (k : I64) (r : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
        (hres : count_great_enough_nodes root k = ok r), r.val ≤ (countSizeAtLeast k.val (ofTree root) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k is an i64 with 1 <= k <= 10. Let N(root) be the number of node occurrences in root, and assume k >= N(root). -/
  theorem spec_5 (root : Tree) (k : I64) (r : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
      (hkN : ((ofTree root).size : Int) ≤ k.val)
      (hres : count_great_enough_nodes root k = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (k : I64) (r : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
        (hkN : ((ofTree root).size : Int) ≤ k.val)
        (hres : count_great_enough_nodes root k = ok r), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r equals the number of node occurrences u of root for which there exists a node occurrence w in the subtree rooted at u (including u) with val(w) < val(u).
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k = 1. -/
  theorem spec_6 (root : Tree) (k : I64) (r : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
      (hk : k.val = 1)
      (hres : count_great_enough_nodes root k = ok r) :
      r.val = (countWithSmallerBelow (ofTree root) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (k : I64) (r : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
        (hk : k.val = 1)
        (hres : count_great_enough_nodes root k = ok r), r.val = (countWithSmallerBelow (ofTree root) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = A(L,k) + A(R,k) + (1 if szRoot >= k and lessRoot >= k else 0).
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k is an i64 with 1 <= k <= 10; root = Node(v,L,R). For any Tree T, let A(T,k) be the mathematical number of node occurrences u of T with sz_T(u) >= k and less_T(u) >= k, using the same subtree definitions, and let A(Null,k)=0. Let szRoot = 1 + N(L) + N(R), where N(L) and N(R) are the numbers of node occurrences in L and R; let lessRoot be the number of node occurrences w in L or R with val(w) < v. -/
  theorem spec_7 (root : Tree) (k : I64) (r : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
      (v : I64) (L R : Tree) (hroot : root = Tree.Node v L R)
      (hres : count_great_enough_nodes root k = ok r) :
      r.val = ((greatEnough k.val (ofTree L) + greatEnough k.val (ofTree R) +
          (if k.val ≤ (nodeSize (ofTree L) (ofTree R) : Int) ∧
              k.val ≤ (nodeLessCount v.val (ofTree L) (ofTree R) : Int)
           then 1 else 0) : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (k : I64) (r : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
        (v : I64) (L R : Tree) (hroot : root = Tree.Node v L R)
        (hres : count_great_enough_nodes root k = ok r), r.val = ((greatEnough k.val (ofTree L) + greatEnough k.val (ofTree R) +
            (if k.val ≤ (nodeSize (ofTree L) (ofTree R) : Int) ∧
                k.val ≤ (nodeLessCount v.val (ofTree L) (ofTree R) : Int)
             then 1 else 0) : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r on root, r equals the number of great-enough node occurrences of shift(root,c) for the same k; equivalently A(root,k)=A(shift(root,c),k).
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k is an i64 with 1 <= k <= 10. Let c be any integer such that 1 <= val(u)+c <= 10000 for every node occurrence u of root. Let shift(root,c) be the tree with the same shape as root and with each node value val(u) replaced by val(u)+c. -/
  theorem spec_8 (root : Tree) (k : I64) (r : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
      (c : Int) (hshift : valuesBetween 1 10000 (shift c (ofTree root)))
      (hres : count_great_enough_nodes root k = ok r) :
      r.val = (greatEnough k.val (shift c (ofTree root)) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (k : I64) (r : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
        (c : Int) (hshift : valuesBetween 1 10000 (shift c (ofTree root)))
        (hres : count_great_enough_nodes root k = ok r), r.val = (greatEnough k.val (shift c (ofTree root)) : Int)) := by
    sorry

  /-- Whenever the function returns a result r on root, r equals the number of great-enough node occurrences of mirror(root) for the same k; equivalently A(root,k)=A(mirror(root),k).
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k is an i64 with 1 <= k <= 10. Define mirror(T) recursively by mirror(Null)=Null and mirror(Node(v,L,R))=Node(v,mirror(R),mirror(L)). For any Tree T, let A(T,k) be the mathematical number of great-enough node occurrences of T for k, using the same subtree definitions. -/
  theorem spec_9 (root : Tree) (k : I64) (r : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
      (hres : count_great_enough_nodes root k = ok r) :
      r.val = (greatEnough k.val (mirror (ofTree root)) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (k : I64) (r : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
        (hres : count_great_enough_nodes root k = ok r), r.val = (greatEnough k.val (mirror (ofTree root)) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there is no node occurrence u of root with sz(u) >= k and less(u) >= k.
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k is an i64 with 1 <= k <= 10. For a node occurrence u, let sz(u) be the number of node occurrences in the subtree rooted at u, including u; let less(u) be the number of w in that subtree with val(w) < val(u). -/
  theorem spec_10 (root : Tree) (k : I64) (r : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
      (hres : count_great_enough_nodes root k = ok r) :
      (r.val = 0 ↔ ¬ existsGreatEnough k.val (ofTree root)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (k : I64) (r : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
        (hres : count_great_enough_nodes root k = ok r), (r.val = 0 ↔ ¬ existsGreatEnough k.val (ofTree root))) := by
    sorry

  /-- Whenever the function returns results r1 for k1 and r2 for k2 on the same root, r2 <= r1. Equivalently A(root,k2) <= A(root,k1), where A(T,k) is the number of great-enough node occurrences of T for k.
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k1 and k2 are i64 with 1 <= k1 <= k2 <= 10. -/
  theorem spec_11 (root : Tree) (k1 k2 : I64) (r1 r2 : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1lo : 1 ≤ k1.val) (hk1hi : k1.val ≤ 10)
      (hk2lo : 1 ≤ k2.val) (hk2hi : k2.val ≤ 10)
      (hkm : k1.val ≤ k2.val)
      (hres1 : count_great_enough_nodes root k1 = ok r1)
      (hres2 : count_great_enough_nodes root k2 = ok r2) :
      r2.val ≤ r1.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (k1 k2 : I64) (r1 r2 : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1lo : 1 ≤ k1.val) (hk1hi : k1.val ≤ 10)
        (hk2lo : 1 ≤ k2.val) (hk2hi : k2.val ≤ 10)
        (hkm : k1.val ≤ k2.val)
        (hres1 : count_great_enough_nodes root k1 = ok r1)
        (hres2 : count_great_enough_nodes root k2 = ok r2), r2.val ≤ r1.val) := by
    sorry

  /-- Whenever the function returns a result r on root, r equals the number of great-enough node occurrences of map(root,f) for the same k; equivalently A(root,k)=A(map(root,f),k).
    Preconditions: root is a non-null Tree with between 1 and 10000 node occurrences; every node value is an integer in [1,10000]; k is an i64 with 1 <= k <= 10; f is a strictly increasing function on integers such that 1 <= f(val(u)) <= 10000 for every node occurrence u of root. Let map(root,f) be the tree with the same shape and each node value val(u) replaced by f(val(u)). -/
  theorem spec_12 (root : Tree) (k : I64) (r : I64)
      (hne : root ≠ Tree.Null)
      (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
      (hval : valuesBetween 1 10000 (ofTree root))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
      (f : Int → Int) (hf : ∀ a b : Int, a < b → f a < f b)
      (hmap : valuesBetween 1 10000 (mapValues f (ofTree root)))
      (hres : count_great_enough_nodes root k = ok r) :
      r.val = (greatEnough k.val (mapValues f (ofTree root)) : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (k : I64) (r : I64)
        (hne : root ≠ Tree.Null)
        (hpos : 1 ≤ (ofTree root).size) (hsize : (ofTree root).size ≤ 10000)
        (hval : valuesBetween 1 10000 (ofTree root))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10)
        (f : Int → Int) (hf : ∀ a b : Int, a < b → f a < f b)
        (hmap : valuesBetween 1 10000 (mapValues f (ofTree root)))
        (hres : count_great_enough_nodes root k = ok r), r.val = (greatEnough k.val (mapValues f (ofTree root)) : Int)) := by
    sorry

  end AegisSpec.CountGreatEnoughNodes
