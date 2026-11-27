import Aegis.GoodNodes.Code.Funs

/-!
# Specifications of `Aegis.GoodNodes.good_nodes`

LeetCode problem `count-good-nodes-in-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.GoodNodes (good_nodes)

open Aeneas.Std.Result

namespace AegisSpec.GoodNodes

abbrev Tree := Aegis.GoodNodes.Tree

abbrev I64 := Aeneas.Std.I64

def size : Tree → Nat
  | .Null => 0
  | .Node _ l r => 1 + size l + size r

def nodeVals : Tree → List ℤ
  | .Null => []
  | .Node v l r => v.val :: (nodeVals l ++ nodeVals r)

def ValuesIn (t : Tree) (lo hi : ℤ) : Prop := ∀ x ∈ nodeVals t, lo ≤ x ∧ x ≤ hi

def Constraints (t : Tree) : Prop :=
  1 ≤ size t ∧ size t ≤ 100000 ∧ ValuesIn t (-10000) 10000

def rootVal? : Tree → Option ℤ
  | .Null => none
  | .Node v _ _ => some v.val

def childVals : Tree → List ℤ
  | .Null => []
  | .Node _ l r =>
      (match l with
       | .Null => []
       | .Node w _ _ => [w.val]) ++
      (match r with
       | .Null => []
       | .Node w _ _ => [w.val])

def IsChain : Tree → Prop
  | .Null => True
  | .Node _ l r => (l = .Null ∨ r = .Null) ∧ IsChain l ∧ IsChain r

def StrictlyDecreasing : Tree → Prop
  | .Null => True
  | .Node v l r =>
      (∀ w ∈ childVals (.Node v l r), w < v.val) ∧ StrictlyDecreasing l ∧ StrictlyDecreasing r

def SameExceptRoot : Tree → Tree → Prop
  | .Null, .Null => True
  | .Node _ l1 r1, .Node _ l2 r2 => l1 = l2 ∧ r1 = r2
  | _, _ => False

def mapValues (f : I64 → I64) : Tree → Tree
  | .Null => .Null
  | .Node v l r => .Node (f v) (mapValues f l) (mapValues f r)

def StrictMono64 (f : I64 → I64) : Prop :=
  ∀ a b : I64, a.val < b.val → (f a).val < (f b).val

def countGoodFrom : Tree → ℤ → Nat
  | .Null, _ => 0
  | .Node v l r, m =>
      (if m ≤ v.val then 1 else 0) + countGoodFrom l (max m v.val) +
        countGoodFrom r (max m v.val)

def numGood : Tree → Nat
  | .Null => 0
  | .Node v l r => 1 + countGoodFrom l v.val + countGoodFrom r v.val

/-- The function returns a result r (it does not fail). For each node X in root, let maxPath(X) be the maximum value among all nodes on the path from the root to X (including X itself). Then r equals the number of nodes X such that value(X) = maxPath(X). Equivalently, X is counted iff for every ancestor Y of X (where an ancestor is any node on the path from the root to X, including X), value(Y) <= value(X).
  Preconditions: The tree root is not Null. The number of nodes in root is between 1 and 10^5. Every node's value is between -10^4 and 10^4. -/
theorem spec_1 (root : Tree) (hne : root ≠ .Null) (hcons : Constraints root) :
    ∃ r : I64, good_nodes root = ok r ∧ r.val = (numGood root : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ .Null) (hcons : Constraints root), ∃ r : I64, good_nodes root = ok r ∧ r.val = (numGood root : ℤ)) := by
  sorry

/-- The function returns a result r and r >= 1.
  Preconditions: The tree root is not Null. The number of nodes in root is between 1 and 10^5. Every node's value is between -10^4 and 10^4. -/
theorem spec_2 (root : Tree) (hne : root ≠ .Null) (hcons : Constraints root) :
    ∃ r : I64, good_nodes root = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ .Null) (hcons : Constraints root), ∃ r : I64, good_nodes root = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= size, where size is the number of nodes in root.
  Preconditions: The tree root is not Null. The number of nodes in root is between 1 and 10^5. Every node's value is between -10^4 and 10^4. -/
theorem spec_3 (root : Tree) (hne : root ≠ .Null) (hcons : Constraints root) :
    ∃ r : I64, good_nodes root = ok r ∧ r.val ≤ (size root : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ .Null) (hcons : Constraints root), ∃ r : I64, good_nodes root = ok r ∧ r.val ≤ (size root : ℤ)) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: The tree root is Null. -/
theorem spec_4 : ∃ r : I64, good_nodes .Null = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∃ r : I64, good_nodes .Null = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = size, where size is the number of nodes in root.
  Preconditions: The tree root is not Null. The number of nodes in root is between 1 and 10^5. Every node's value is between -10^4 and 10^4. There exists an integer c such that every node in root has value c. -/
theorem spec_5 (root : Tree) (hne : root ≠ .Null) (hcons : Constraints root)
    (hconst : ∃ c : ℤ, ∀ x ∈ nodeVals root, x = c) :
    ∃ r : I64, good_nodes root = ok r ∧ r.val = (size root : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ .Null) (hcons : Constraints root)
    (hconst : ∃ c : ℤ, ∀ x ∈ nodeVals root, x = c), ∃ r : I64, good_nodes root = ok r ∧ r.val = (size root : ℤ)) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: The tree root satisfies the problem constraints: the number of nodes is between 1 and 10^5, and every node's value is between -10^4 and 10^4. The tree is a chain (every node has at most one child). For every node X with a child Y, value(X) > value(Y). -/
theorem spec_6 (root : Tree) (hcons : Constraints root) (hchain : IsChain root)
    (hdec : StrictlyDecreasing root) :
    ∃ r : I64, good_nodes root = ok r ∧ r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (hcons : Constraints root) (hchain : IsChain root)
    (hdec : StrictlyDecreasing root), ∃ r : I64, good_nodes root = ok r ∧ r.val = 1) := by
  sorry

/-- Let r1 be the result of good_nodes(T1) and r2 be the result of good_nodes(T2). If both calls return results, then r1 >= r2.
  Preconditions: Consider two trees T1 and T2 that have the same shape and the same values at every node except possibly at the root. Let v1 be the root value of T1 and v2 be the root value of T2, with v1 <= v2. Both trees satisfy the problem constraints: number of nodes between 1 and 10^5, all values between -10^4 and 10^4. -/
theorem spec_7 (T1 T2 : Tree) (v1 v2 : ℤ)
    (hcons1 : Constraints T1) (hcons2 : Constraints T2)
    (hsame : SameExceptRoot T1 T2)
    (hroot1 : rootVal? T1 = some v1) (hroot2 : rootVal? T2 = some v2) (hv : v1 ≤ v2) :
    ∀ r1 r2 : I64, good_nodes T1 = ok r1 → good_nodes T2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (T1 T2 : Tree) (v1 v2 : ℤ)
    (hcons1 : Constraints T1) (hcons2 : Constraints T2)
    (hsame : SameExceptRoot T1 T2)
    (hroot1 : rootVal? T1 = some v1) (hroot2 : rootVal? T2 = some v2) (hv : v1 ≤ v2), ∀ r1 r2 : I64, good_nodes T1 = ok r1 → good_nodes T2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- If good_nodes(T) returns r and good_nodes(T') returns r', then r = r'.
  Preconditions: T is a tree satisfying the problem constraints: 1 <= size(T) <= 10^5 and every node value lies in [-10^4, 10^4]. Let f be a strictly increasing function from 64-bit integers to 64-bit integers. Let T' be obtained from T by replacing every node value v with f(v), and assume T' also satisfies the problem constraints (equivalently, all f(v) lie in [-10^4, 10^4]; the shape and size are unchanged). -/
theorem spec_8 (T : Tree) (f : I64 → I64)
    (hcons : Constraints T) (hmono : StrictMono64 f)
    (hcons' : Constraints (mapValues f T)) :
    ∀ r r' : I64, good_nodes T = ok r → good_nodes (mapValues f T) = ok r' → r'.val = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (T : Tree) (f : I64 → I64)
    (hcons : Constraints T) (hmono : StrictMono64 f)
    (hcons' : Constraints (mapValues f T)), ∀ r r' : I64, good_nodes T = ok r → good_nodes (mapValues f T) = ok r' → r'.val = r.val) := by
  sorry

/-- The function returns a result r and r = 4.
  Preconditions: The tree root is Node(3, Node(1, Node(3, Null, Null), Null), Node(4, Node(1, Null, Null), Node(5, Null, Null))). -/
theorem spec_9 :
    ∃ r : I64,
      good_nodes
        (.Node (3#i64)
          (.Node (1#i64) (.Node (3#i64) .Null .Null) .Null)
          (.Node (4#i64) (.Node (1#i64) .Null .Null) (.Node (5#i64) .Null .Null)))
        = ok r ∧
      r.val = 4 := by
  sorry

theorem spec_9_neg :
    ¬ (∃ r : I64,
      good_nodes
        (.Node (3#i64)
          (.Node (1#i64) (.Node (3#i64) .Null .Null) .Null)
          (.Node (4#i64) (.Node (1#i64) .Null .Null) (.Node (5#i64) .Null .Null)))
        = ok r ∧
      r.val = 4) := by
  sorry

/-- The function returns a result r and r = 3.
  Preconditions: The tree root is Node(3, Node(3, Node(4, Null, Null), Node(2, Null, Null)), Null). -/
theorem spec_10 :
    ∃ r : I64,
      good_nodes
        (.Node (3#i64)
          (.Node (3#i64) (.Node (4#i64) .Null .Null) (.Node (2#i64) .Null .Null))
          .Null)
        = ok r ∧
      r.val = 3 := by
  sorry

theorem spec_10_neg :
    ¬ (∃ r : I64,
      good_nodes
        (.Node (3#i64)
          (.Node (3#i64) (.Node (4#i64) .Null .Null) (.Node (2#i64) .Null .Null))
          .Null)
        = ok r ∧
      r.val = 3) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, panic, or overflow).
  Preconditions: The tree root satisfies the problem constraints: the number of nodes is between 1 and 10^5, and every node's value is between -10^4 and 10^4. -/
theorem spec_11 (root : Tree) (hcons : Constraints root) :
    ∃ r : I64, good_nodes root = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (hcons : Constraints root), ∃ r : I64, good_nodes root = ok r) := by
  sorry

/-- If good_nodes(T) returns r and good_nodes(T') returns r', then r' = r + 1.
  Preconditions: Let T be a tree satisfying the problem constraints: number of nodes between 1 and 10^5, every node value between -10^4 and 10^4. Let v be an integer such that v <= value(X) for every node X in T. Let T' be the tree obtained by making T the left child (or right child) of a new root with value v, and the other child Null. (T' also satisfies the problem constraints.) -/
theorem spec_12 (T : Tree) (V : I64)
    (hcons : Constraints T) (hv : ∀ x ∈ nodeVals T, V.val ≤ x)
    (hVlo : -10000 ≤ V.val) (hVhi : V.val ≤ 10000) (hsize : size T + 1 ≤ 100000) :
    (∀ r r' : I64,
        good_nodes T = ok r → good_nodes (.Node V T .Null) = ok r' → r'.val = r.val + 1) ∧
      ∀ r r' : I64,
        good_nodes T = ok r → good_nodes (.Node V .Null T) = ok r' → r'.val = r.val + 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (T : Tree) (V : I64)
    (hcons : Constraints T) (hv : ∀ x ∈ nodeVals T, V.val ≤ x)
    (hVlo : -10000 ≤ V.val) (hVhi : V.val ≤ 10000) (hsize : size T + 1 ≤ 100000), (∀ r r' : I64,
        good_nodes T = ok r → good_nodes (.Node V T .Null) = ok r' → r'.val = r.val + 1) ∧
      ∀ r r' : I64,
        good_nodes T = ok r → good_nodes (.Node V .Null T) = ok r' → r'.val = r.val + 1) := by
  sorry

/-- The function returns a result r for T' and r = 1.
  Preconditions: T satisfies the problem constraints: 1 <= size(T) <= 10^5 and every node value lies in [-10^4, 10^4]. Let v be a 64-bit integer such that v > value(X) for every node X in T. Let T' be obtained by making T the left or right child of a new root with value v, with the other child Null. Assume T' also satisfies the problem constraints (so size(T) <= 10^5 - 1 and v lies in [-10^4, 10^4]). -/
theorem spec_13 (T : Tree) (V : I64)
    (hcons : Constraints T) (hv : ∀ x ∈ nodeVals T, x < V.val)
    (hVlo : -10000 ≤ V.val) (hVhi : V.val ≤ 10000) (hsize : size T + 1 ≤ 100000) :
    (∃ r : I64, good_nodes (.Node V T .Null) = ok r ∧ r.val = 1) ∧
      ∃ r : I64, good_nodes (.Node V .Null T) = ok r ∧ r.val = 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (T : Tree) (V : I64)
    (hcons : Constraints T) (hv : ∀ x ∈ nodeVals T, x < V.val)
    (hVlo : -10000 ≤ V.val) (hVhi : V.val ≤ 10000) (hsize : size T + 1 ≤ 100000), (∃ r : I64, good_nodes (.Node V T .Null) = ok r ∧ r.val = 1) ∧
      ∃ r : I64, good_nodes (.Node V .Null T) = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result res and res = 1 + (if l >= v then 1 else 0) + (if r >= v then 1 else 0).
  Preconditions: Let v, l, r be 64-bit integers with -10^4 <= v, l, r <= 10^4. The tree root is Node(v, Node(l, Null, Null), Node(r, Null, Null)). -/
theorem spec_14 (V L R : I64)
    (hV : -10000 ≤ V.val ∧ V.val ≤ 10000)
    (hL : -10000 ≤ L.val ∧ L.val ≤ 10000)
    (hR : -10000 ≤ R.val ∧ R.val ≤ 10000) :
    ∃ res : I64,
      good_nodes (.Node V (.Node L .Null .Null) (.Node R .Null .Null)) = ok res ∧
        res.val = (1 : ℤ) + (if V.val ≤ L.val then 1 else 0) +
          (if V.val ≤ R.val then 1 else 0) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (V L R : I64)
    (hV : -10000 ≤ V.val ∧ V.val ≤ 10000)
    (hL : -10000 ≤ L.val ∧ L.val ≤ 10000)
    (hR : -10000 ≤ R.val ∧ R.val ≤ 10000), ∃ res : I64,
      good_nodes (.Node V (.Node L .Null .Null) (.Node R .Null .Null)) = ok res ∧
        res.val = (1 : ℤ) + (if V.val ≤ L.val then 1 else 0) +
          (if V.val ≤ R.val then 1 else 0)) := by
  sorry

end AegisSpec.GoodNodes
