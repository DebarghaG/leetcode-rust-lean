import Aegis.MinCameraCover.Code.Funs

/-!
# Specifications of `Aegis.MinCameraCover.min_camera_cover`

LeetCode problem `binary-tree-cameras`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinCameraCover

  open Aegis.MinCameraCover

  inductive PathDir where
    | left : PathDir
    | right : PathDir
    deriving DecidableEq, Repr

  def nodePaths : Tree → List (List PathDir)
    | .Null => []
    | .Node _ l r =>
      [] :: (nodePaths l).map (fun p => p ++ [PathDir.left]) ++
        (nodePaths r).map (fun p => p ++ [PathDir.right])

  def Nodes (t : Tree) : Finset (List PathDir) := (nodePaths t).toFinset

  def numNodes : Tree → ℕ
    | .Null => 0
    | .Node _ l r => 1 + numNodes l + numNodes r

  def allValuesZero : Tree → Prop
    | .Null => True
    | .Node v l r => v.val = 0 ∧ allValuesZero l ∧ allValuesZero r

  def parentOf (p : List PathDir) : Option (List PathDir) :=
    match p with
    | [] => none
    | _ => some p.dropLast

  def Monitored (S : Finset (List PathDir)) (v : List PathDir) : Prop :=
    v ∈ S ∨ (∃ w : List PathDir, parentOf v = some w ∧ w ∈ S) ∨
      v ++ [PathDir.left] ∈ S ∨ v ++ [PathDir.right] ∈ S

  def IsCover (t : Tree) (S : Finset (List PathDir)) : Prop :=
    (∀ p ∈ S, p ∈ Nodes t) ∧ ∀ v ∈ Nodes t, Monitored S v

  def IsMinCoverCard (t : Tree) (r : ℤ) : Prop :=
    ∃ S : Finset (List PathDir),
      IsCover t S ∧ (S.card : ℤ) = r ∧
        ∀ S' : Finset (List PathDir), IsCover t S' → r ≤ (S'.card : ℤ)

  def mirror : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node v (mirror r) (mirror l)

  def IsPath : Tree → Prop
    | .Null => True
    | .Node _ l r => (l = Tree.Null ∨ r = Tree.Null) ∧ IsPath l ∧ IsPath r

  def numInternal : Tree → ℕ
    | .Null => 0
    | .Node _ l r =>
      numInternal l + numInternal r + (match l, r with | .Null, .Null => 0 | _, _ => 1)

  def IsCeilThird (N : ℕ) (k : ℤ) : Prop :=
    3 * k ≥ (N : ℤ) ∧ ∀ j : ℤ, 3 * j ≥ (N : ℤ) → k ≤ j

  /-- The function returns a result r and r equals the minimum cardinality of a set S of nodes of the tree such that every node is monitored by S. A node v is monitored by S iff v is in S, or the parent of v (if v is not the root) is in S, or at least one immediate child of v (if v has such a child) is in S. Formally, let Nodes(root) be the set of nodes reachable from root by left and right child links. Then r = min { |S| : S is a subset of Nodes(root) and for every v in Nodes(root), v is in S or parent(v) is in S or leftChild(v) is in S or rightChild(v) is in S }, ignoring nonexistent parents and Null children.
    Preconditions: root is not Null; the number of nodes in the tree rooted at root is between 1 and 1000; every Node in the tree has value 0. -/
  theorem spec_1 (root : Tree)
      (hroot : root ≠ Tree.Null)
      (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
      (hzero : allValuesZero root) :
      ∃ r : I64, min_camera_cover root = .ok r ∧ IsMinCoverCard root r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hroot : root ≠ Tree.Null)
        (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
        (hzero : allValuesZero root), ∃ r : I64, min_camera_cover root = Result.ok r ∧ IsMinCoverCard root r.val) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, go out of bounds, or overflow during execution.
    Preconditions: root is not Null; the number of nodes in the tree rooted at root is between 1 and 1000; every Node in the tree has value 0. -/
  theorem spec_2 (root : Tree)
      (hroot : root ≠ Tree.Null)
      (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
      (hzero : allValuesZero root) :
      ∃ r : I64, min_camera_cover root = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hroot : root ≠ Tree.Null)
        (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
        (hzero : allValuesZero root), ∃ r : I64, min_camera_cover root = Result.ok r) := by
    sorry

  /-- Let N be the number of nodes in the tree rooted at root. The function returns a result r and 1 <= r <= N.
    Preconditions: root is not Null; the number of nodes in the tree rooted at root is between 1 and 1000; every Node in the tree has value 0. -/
  theorem spec_3 (root : Tree)
      (hroot : root ≠ Tree.Null)
      (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
      (hzero : allValuesZero root) :
      ∃ r : I64, min_camera_cover root = .ok r ∧ 1 ≤ r.val ∧ r.val ≤ (numNodes root : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hroot : root ≠ Tree.Null)
        (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
        (hzero : allValuesZero root), ∃ r : I64, min_camera_cover root = Result.ok r ∧ 1 ≤ r.val ∧ r.val ≤ (numNodes root : ℤ)) := by
    sorry

  /-- The function returns a result r and there exists a set S of nodes of the tree such that |S| = r and every node of the tree is monitored by S, where a camera at a node monitors that node, its parent if any, and its immediate children if any.
    Preconditions: root is not Null; the number of nodes in the tree rooted at root is between 1 and 1000; every Node in the tree has value 0. -/
  theorem spec_4 (root : Tree)
      (hroot : root ≠ Tree.Null)
      (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
      (hzero : allValuesZero root) :
      ∃ r : I64, min_camera_cover root = .ok r ∧
        ∃ S : Finset (List PathDir), IsCover root S ∧ (S.card : ℤ) = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hroot : root ≠ Tree.Null)
        (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
        (hzero : allValuesZero root), ∃ r : I64, min_camera_cover root = Result.ok r ∧
          ∃ S : Finset (List PathDir), IsCover root S ∧ (S.card : ℤ) = r.val) := by
    sorry

  /-- The function returns a result r and for every set S of nodes of the tree, if every node of the tree is monitored by S (with the same monitoring definition: a camera at a node monitors that node, its parent if any, and its immediate children if any), then |S| >= r.
    Preconditions: root is not Null; the number of nodes in the tree rooted at root is between 1 and 1000; every Node in the tree has value 0. -/
  theorem spec_5 (root : Tree)
      (hroot : root ≠ Tree.Null)
      (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
      (hzero : allValuesZero root) :
      ∃ r : I64, min_camera_cover root = .ok r ∧
        ∀ S : Finset (List PathDir), IsCover root S → r.val ≤ (S.card : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hroot : root ≠ Tree.Null)
        (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
        (hzero : allValuesZero root), ∃ r : I64, min_camera_cover root = Result.ok r ∧
          ∀ S : Finset (List PathDir), IsCover root S → r.val ≤ (S.card : ℤ)) := by
    sorry

  /-- The function returns a result r and r = ceil(N/3), where ceil(N/3) is the least integer k such that 3*k >= N.
    Preconditions: The tree rooted at root is a path with N >= 4 nodes: every node has at most one child, and every node has value 0. Let N be the number of nodes. -/
  theorem spec_6 (root : Tree)
      (hpath : IsPath root)
      (hnum : 4 ≤ numNodes root)
      (hzero : allValuesZero root) :
      ∃ r : I64, min_camera_cover root = .ok r ∧ IsCeilThird (numNodes root) r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree)
        (hpath : IsPath root)
        (hnum : 4 ≤ numNodes root)
        (hzero : allValuesZero root), ∃ r : I64, min_camera_cover root = Result.ok r ∧ IsCeilThird (numNodes root) r.val) := by
    sorry

  /-- The function returns a result r when called on root and a result r_mirror when called on mirrorRoot, and r = r_mirror.
    Preconditions: root is not Null; the tree rooted at root has between 1 and 1000 nodes; every node has value 0; and mirrorRoot is the tree obtained from root by recursively swapping the left and right children at every node, keeping the same node values. -/
  theorem spec_7 (root mirrorRoot : Tree)
      (hroot : root ≠ Tree.Null)
      (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
      (hzero : allValuesZero root)
      (hmirror : mirrorRoot = mirror root) :
      ∃ r rm : I64,
        min_camera_cover root = .ok r ∧ min_camera_cover mirrorRoot = .ok rm ∧ r = rm := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root mirrorRoot : Tree)
        (hroot : root ≠ Tree.Null)
        (hnum_lo : 1 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
        (hzero : allValuesZero root)
        (hmirror : mirrorRoot = mirror root), ∃ r rm : I64,
          min_camera_cover root = Result.ok r ∧ min_camera_cover mirrorRoot = Result.ok rm ∧ r = rm) := by
    sorry

  /-- Let I be the number of nodes in the tree rooted at root that have at least one child. The function returns a result r and r <= I.
    Preconditions: root is not Null; the tree rooted at root has between 2 and 1000 nodes; every node has value 0. -/
  theorem spec_8 (root : Tree)
      (hroot : root ≠ Tree.Null)
      (hnum_lo : 2 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
      (hzero : allValuesZero root) :
      ∃ r : I64, min_camera_cover root = .ok r ∧ r.val ≤ (numInternal root : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree)
        (hroot : root ≠ Tree.Null)
        (hnum_lo : 2 ≤ numNodes root) (hnum_hi : numNodes root ≤ 1000)
        (hzero : allValuesZero root), ∃ r : I64, min_camera_cover root = Result.ok r ∧ r.val ≤ (numInternal root : ℤ)) := by
    sorry

  end AegisSpec.MinCameraCover
