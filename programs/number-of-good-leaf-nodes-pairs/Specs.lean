import Aegis.CountPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPairs.count_pairs`

LeetCode problem `number-of-good-leaf-nodes-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountPairs

  open Aegis.CountPairs

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

  def NodeValuesIn (lo hi : Int) : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
      lo ≤ v.val ∧ v.val ≤ hi ∧ NodeValuesIn lo hi l ∧ NodeValuesIn lo hi r

  def SameShape : Tree → Tree → Prop
    | Tree.Null, Tree.Null => True
    | Tree.Node _ l₁ r₁, Tree.Node _ l₂ r₂ => SameShape l₁ l₂ ∧ SameShape r₁ r₂
    | _, _ => False

  def subtree? : Tree → List Bool → Option Tree
    | t, [] => some t
    | Tree.Node _ l _, false :: ds => subtree? l ds
    | Tree.Node _ _ r, true :: ds => subtree? r ds
    | Tree.Null, _ :: _ => none

  def IsLeafAt (t : Tree) (p : List Bool) : Prop :=
    ∃ v, subtree? t p = some (Tree.Node v Tree.Null Tree.Null)

  def isLeafAt (t : Tree) (p : List Bool) : Bool :=
    match subtree? t p with
    | some (Tree.Node _ Tree.Null Tree.Null) => true
    | _ => false

  theorem isLeafAt_iff (t : Tree) (p : List Bool) : isLeafAt t p = true ↔ IsLeafAt t p := by
    unfold isLeafAt IsLeafAt
    cases h : subtree? t p with
    | none => simp
    | some s =>
      cases s with
      | Null => simp
      | Node v l r =>
        cases l with
        | Null =>
          cases r with
          | Null => simp
          | Node v' l' r' => simp
        | Node v' l' r' => simp

  def positions : Tree → Finset (List Bool)
    | Tree.Null => ∅
    | Tree.Node _ l r =>
      insert [] ((positions l).image (fun p => false :: p) ∪ (positions r).image (fun p => true :: p))

  def leafPositions (t : Tree) : Finset (List Bool) :=
    (positions t).filter (fun p => isLeafAt t p)

  def commonPrefixLen : List Bool → List Bool → Nat
    | a :: pa, b :: pb => if a = b then 1 + commonPrefixLen pa pb else 0
    | _, _ => 0

  def pathDist (p q : List Bool) : Nat :=
    p.length + q.length - 2 * commonPrefixLen p q

  def pairCount (t : Tree) (d : Int) : Nat :=
    (((leafPositions t).product (leafPositions t)).filter
        (fun pq => pq.1 < pq.2 ∧ (pathDist pq.1 pq.2 : Int) ≤ d)).card

  /-- Whenever count_pairs root distance returns Ok r, r equals the number of unordered pairs {u,v} of two distinct leaf positions u and v of root such that the length, counted in edges, of the unique simple path between u and v in root is at most distance. A leaf position is a node occurrence of the form Node(val, Null, Null); distinct leaf positions may have equal stored values.
    Preconditions: root is a finite binary tree with at least 1 and at most 1024 nodes; every Node value in root lies in [1,100]; distance is an i64 satisfying 1 <= distance <= 10. -/
  theorem spec_1
      (root : Tree) (distance : Std.I64) (r : Std.I64)
      (h_nodes_nonempty : 1 ≤ nodeCount root)
      (h_nodes_bound : nodeCount root ≤ 1024)
      (h_values : NodeValuesIn 1 100 root)
      (h_distance_lower : 1 ≤ distance.val)
      (h_distance_upper : distance.val ≤ 10)
      (h_returns : count_pairs root distance = ok r) :
      r.val = (pairCount root distance.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (distance : Std.I64) (r : Std.I64)
        (h_nodes_nonempty : 1 ≤ nodeCount root)
        (h_nodes_bound : nodeCount root ≤ 1024)
        (h_values : NodeValuesIn 1 100 root)
        (h_distance_lower : 1 ≤ distance.val)
        (h_distance_upper : distance.val ≤ 10)
        (h_returns : count_pairs root distance = ok r), r.val = (pairCount root distance.val : Int)) := by
    sorry

  /-- count_pairs root distance returns Ok r for some i64 r; in particular it does not return Err, overflow, go out of bounds, or panic.
    Preconditions: root is a finite binary tree with at least 1 and at most 1024 nodes; every Node value in root lies in [1,100]; distance is an i64 satisfying 1 <= distance <= 10. -/
  theorem spec_2
      (root : Tree) (distance : Std.I64)
      (h_nodes_nonempty : 1 ≤ nodeCount root)
      (h_nodes_bound : nodeCount root ≤ 1024)
      (h_values : NodeValuesIn 1 100 root)
      (h_distance_lower : 1 ≤ distance.val)
      (h_distance_upper : distance.val ≤ 10) :
      ∃ r : Std.I64, count_pairs root distance = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (distance : Std.I64)
        (h_nodes_nonempty : 1 ≤ nodeCount root)
        (h_nodes_bound : nodeCount root ≤ 1024)
        (h_values : NodeValuesIn 1 100 root)
        (h_distance_lower : 1 ≤ distance.val)
        (h_distance_upper : distance.val ≤ 10), ∃ r : Std.I64, count_pairs root distance = ok r) := by
    sorry

  /-- Whenever count_pairs root d1 returns Ok r1 and count_pairs root d2 returns Ok r2, r1 <= r2.
    Preconditions: root is a finite binary tree with at least 1 and at most 1024 nodes; every Node value in root lies in [1,100]; d1 and d2 are i64 with 1 <= d1 <= d2 <= 10. -/
  theorem spec_3
      (root : Tree) (d1 d2 : Std.I64) (r1 r2 : Std.I64)
      (h_nodes_nonempty : 1 ≤ nodeCount root)
      (h_nodes_bound : nodeCount root ≤ 1024)
      (h_values : NodeValuesIn 1 100 root)
      (h_d1_lower : 1 ≤ d1.val)
      (h_d1_le_d2 : d1.val ≤ d2.val)
      (h_d2_upper : d2.val ≤ 10)
      (h_returns1 : count_pairs root d1 = ok r1)
      (h_returns2 : count_pairs root d2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (d1 d2 : Std.I64) (r1 r2 : Std.I64)
        (h_nodes_nonempty : 1 ≤ nodeCount root)
        (h_nodes_bound : nodeCount root ≤ 1024)
        (h_values : NodeValuesIn 1 100 root)
        (h_d1_lower : 1 ≤ d1.val)
        (h_d1_le_d2 : d1.val ≤ d2.val)
        (h_d2_upper : d2.val ≤ 10)
        (h_returns1 : count_pairs root d1 = ok r1)
        (h_returns2 : count_pairs root d2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Whenever count_pairs root1 distance returns Ok r1 and count_pairs root2 distance returns Ok r2, r1 = r2.
    Preconditions: root1 and root2 are finite binary trees with at least 1 and at most 1024 nodes each; every Node value in both trees lies in [1,100]; root1 and root2 have the same underlying shape, meaning root2 is obtained from root1 by replacing each stored node value while keeping every Null/Node constructor and every parent-child position unchanged; distance is an i64 satisfying 1 <= distance <= 10. -/
  theorem spec_4
      (root1 root2 : Tree) (distance : Std.I64) (r1 r2 : Std.I64)
      (h_nodes_nonempty1 : 1 ≤ nodeCount root1)
      (h_nodes_bound1 : nodeCount root1 ≤ 1024)
      (h_nodes_nonempty2 : 1 ≤ nodeCount root2)
      (h_nodes_bound2 : nodeCount root2 ≤ 1024)
      (h_values1 : NodeValuesIn 1 100 root1)
      (h_values2 : NodeValuesIn 1 100 root2)
      (h_same_shape : SameShape root1 root2)
      (h_distance_lower : 1 ≤ distance.val)
      (h_distance_upper : distance.val ≤ 10)
      (h_returns1 : count_pairs root1 distance = ok r1)
      (h_returns2 : count_pairs root2 distance = ok r2) :
      r1.val = r2.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root1 root2 : Tree) (distance : Std.I64) (r1 r2 : Std.I64)
        (h_nodes_nonempty1 : 1 ≤ nodeCount root1)
        (h_nodes_bound1 : nodeCount root1 ≤ 1024)
        (h_nodes_nonempty2 : 1 ≤ nodeCount root2)
        (h_nodes_bound2 : nodeCount root2 ≤ 1024)
        (h_values1 : NodeValuesIn 1 100 root1)
        (h_values2 : NodeValuesIn 1 100 root2)
        (h_same_shape : SameShape root1 root2)
        (h_distance_lower : 1 ≤ distance.val)
        (h_distance_upper : distance.val ≤ 10)
        (h_returns1 : count_pairs root1 distance = ok r1)
        (h_returns2 : count_pairs root2 distance = ok r2), r1.val = r2.val) := by
    sorry

  end AegisSpec.CountPairs
