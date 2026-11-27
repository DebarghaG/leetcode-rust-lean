import Aegis.BinaryTreePaths.Code.Funs

/-!
# Specifications of `Aegis.BinaryTreePaths.binary_tree_paths`

LeetCode problem `binary-tree-paths`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.BinaryTreePaths

open Aegis.BinaryTreePaths

abbrev Tree : Type := Aegis.BinaryTreePaths.Tree

def numNodes : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + numNodes l + numNodes r

def isLeaf : Tree → Bool
  | Tree.Null => false
  | Tree.Node _ l r =>
    match l, r with
    | Tree.Null, Tree.Null => true
    | _, _ => false

def numLeaves : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r =>
    match l, r with
    | Tree.Null, Tree.Null => 1
    | _, _ => numLeaves l + numLeaves r

def paths : Tree → List (List Int)
  | Tree.Null => []
  | Tree.Node v l r =>
    match l, r with
    | Tree.Null, Tree.Null => [[v.val]]
    | _, _ => (paths l).map (fun p => v.val :: p) ++ (paths r).map (fun p => v.val :: p)

def valuesWithin (lo hi : Int) : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r =>
    lo ≤ v.val ∧ v.val ≤ hi ∧ valuesWithin lo hi l ∧ valuesWithin lo hi r

def bytesOf (v : alloc.vec.Vec Std.U8) : List Nat := v.val.map (fun b => b.val)

def decNat (n : Nat) : List Nat :=
  if n < 10 then [48 + n] else decNat (n / 10) ++ [48 + n % 10]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def dec (z : Int) : List Nat :=
  if z < 0 then 45 :: decNat z.natAbs else decNat z.natAbs

def arrow : List Nat := [45, 62]

def enc : List Int → List Nat
  | [] => []
  | [v] => dec v
  | v :: w :: ws => dec v ++ arrow ++ enc (w :: ws)

def IsPathEncoding (s : List Nat) : Prop :=
  ∃ (vs : List Int), vs ≠ [] ∧ (∀ a ∈ vs, -100 ≤ a ∧ a ≤ 100) ∧ enc vs = s

def HasUniqueDecoding (s : List Nat) : Prop :=
  ∃ (vs : List Int),
    vs ≠ [] ∧ (∀ a ∈ vs, -100 ≤ a ∧ a ≤ 100) ∧ enc vs = s ∧
      ∀ vs' : List Int, vs' ≠ [] → (∀ a ∈ vs', -100 ≤ a ∧ a ≤ 100) → enc vs' = s → vs' = vs

def splitArrowAux : List Nat → List Nat → List (List Nat)
  | cur, [] => [cur.reverse]
  | cur, [a] => (a :: cur).reverse :: []
  | cur, a :: b :: rest =>
    if a = 45 ∧ b = 62 then cur.reverse :: splitArrowAux [] rest
    else splitArrowAux (a :: cur) (b :: rest)

def splitArrow (s : List Nat) : List (List Nat) := splitArrowAux [] s

def segments (s : List Nat) : List (List Nat) :=
  (splitArrow s).filter (fun seg => !seg.isEmpty)

def digitsNumber : List Nat → Nat
  | [] => 0
  | b :: rest => (b - 48) * 10 ^ rest.length + digitsNumber rest

def parseInt (s : List Nat) : Option Int :=
  match s with
  | [] => none
  | 45 :: rest =>
    if rest.isEmpty then none
    else if rest.all (fun b => decide (48 ≤ b ∧ b ≤ 57)) then
      some (-(Int.ofNat (digitsNumber rest)))
    else none
  | _ =>
    if s.all (fun b => decide (48 ≤ b ∧ b ≤ 57)) then some (Int.ofNat (digitsNumber s))
    else none

def isEncodingByte (b : Nat) : Prop := b = 45 ∨ b = 62 ∨ (48 ≤ b ∧ b ≤ 57)

def BytesOK : List Nat → Prop
  | [] => True
  | b :: rest => isEncodingByte b ∧ BytesOK rest

def ArrowsWellFormed : List Nat → Prop
  | [] => True
  | [b] => b ≠ 62
  | a :: b :: rest =>
    (b = 62 → a = 45 ∧
      (match rest with
       | [] => False
       | c :: _ => c = 45 ∨ (48 ≤ c ∧ c ≤ 57))) ∧
      ArrowsWellFormed (b :: rest)

/-- Whenever binary_tree_paths(root) returns Ok r, r is a vector of byte vectors that is a permutation, with multiplicity, of the list of encodings enc(P) over all root-to-leaf paths P of root. Equivalently, there is a bijection from the index set {0,...,len(r)-1} to the leaves of root (or to root-to-leaf paths) such that for every index i, r[i] = enc(P_i), where P_i is the path from the root to the associated leaf. The order of entries in r is arbitrary; if two distinct leaves give the same encoding, that byte string must occur once for each such leaf. Definitions: a leaf is a Node with both children Null; a root-to-leaf path is the sequence of node values v0,...,vk obtained by starting at the root and repeatedly moving to a child, ending at a leaf; dec(z) for an integer z in [-100,100] is the ASCII byte vector of the usual decimal representation of z, with a leading '-' (byte 45) if and only if z < 0, no leading zeros, and a single '0' byte for zero; arrow is the two-byte vector [45,62] representing '->'; and enc(v0,...,vk) = dec(v0) ++ arrow ++ dec(v1) ++ ... ++ arrow ++ dec(vk), where ++ is byte-vector concatenation.
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_1 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      List.Perm (r.val.map bytesOf) ((paths root).map enc) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      List.Perm (r.val.map bytesOf) ((paths root).map enc)) := by
  sorry

/-- For every root satisfying the preconditions, binary_tree_paths(root) returns Ok r for some r; in particular it does not overflow, access out of bounds, or panic.
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_2 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), binary_tree_paths root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), binary_tree_paths root = ok r) := by
  sorry

/-- Whenever binary_tree_paths(root) returns a result r, len(r) is exactly the number of leaves of root, where a leaf is a node whose left and right children are both Null. Distinct leaves are counted separately even if they have the same value or the same encoded path.
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_3 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r → r.val.length = numLeaves root := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r → r.val.length = numLeaves root) := by
  sorry

/-- Whenever binary_tree_paths(root) returns a result r, for every i with 0 <= i < len(r), the byte vector r[i] can be written uniquely as dec(a0) ++ arrow ++ dec(a1) ++ ... ++ arrow ++ dec(ak) for some k >= 0 and integers a0,...,ak in [-100,100], where arrow is the two-byte vector [45,62] and dec(z) is the ASCII decimal representation of z with no leading zeros (except the single byte [48] for 0). In particular, r[i] has no leading or trailing arrow, no empty integer component, and every occurrence of the two-byte sequence [45,62] is a separator between consecutive integer components.
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_4 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length), HasUniqueDecoding (bytesOf (r.val[i]'hi)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length), HasUniqueDecoding (bytesOf (r.val[i]'hi))) := by
  sorry

/-- Whenever binary_tree_paths(root) returns a result r, for every i with 0 <= i < len(r), r[i] begins with dec(root.val), where root = Node(root.val, _, _) and dec(z) is the ASCII decimal representation of z with no leading zeros (except [48] for 0).
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_5 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (v : Std.I64) (l rr : Tree), root = Tree.Node v l rr →
        ∀ (i : Nat) (hi : i < r.val.length),
          List.IsPrefix (dec v.val) (bytesOf (r.val[i]'hi)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (v : Std.I64) (l rr : Tree), root = Tree.Node v l rr →
        ∀ (i : Nat) (hi : i < r.val.length),
          List.IsPrefix (dec v.val) (bytesOf (r.val[i]'hi))) := by
  sorry

/-- Whenever binary_tree_paths(root) returns a result r, for every i with 0 <= i < len(r), there exists a root-to-leaf path P of root such that r[i] = enc(P). Here a root-to-leaf path is a sequence of node values v0,...,vk from the root to a leaf (a node with both children Null); enc(v0,...,vk) is dec(v0) ++ arrow ++ ... ++ arrow ++ dec(vk), with arrow = [45,62] and dec(z) the ASCII decimal representation of z with no leading zeros (except [48] for 0).
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_6 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        ∃ P ∈ paths root, bytesOf (r.val[i]'hi) = enc P := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        ∃ P ∈ paths root, bytesOf (r.val[i]'hi) = enc P) := by
  sorry

/-- Whenever binary_tree_paths(root) returns a result r, for every leaf L of root, there exists an index i with 0 <= i < len(r) such that r[i] = enc(P_L), where P_L is the sequence of node values on the path from the root to L, and enc is defined by dec(z) (ASCII decimal, no leading zeros, [48] for 0) and arrow = [45,62].
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_7 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ P ∈ paths root,
        ∃ (i : Nat) (hi : i < r.val.length), bytesOf (r.val[i]'hi) = enc P := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ P ∈ paths root,
        ∃ (i : Nat) (hi : i < r.val.length), bytesOf (r.val[i]'hi) = enc P) := by
  sorry

/-- Whenever binary_tree_paths(root) returns a result r, for every byte string s that is the encoding of at least one root-to-leaf path of root, the number of indices i with 0 <= i < len(r) and r[i] = s is exactly the number of leaves L whose root-to-leaf path encodes to s. Encodings are defined as dec(v0) ++ arrow ++ ... ++ arrow ++ dec(vk), with arrow = [45,62] and dec(z) the ASCII decimal representation of z with no leading zeros (except [48] for 0).
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_8 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ s : List Nat, (∃ P ∈ paths root, enc P = s) →
        (r.val.filter (fun v => decide (bytesOf v = s))).length
          = ((paths root).filter (fun P => decide (enc P = s))).length := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ s : List Nat, (∃ P ∈ paths root, enc P = s) →
        (r.val.filter (fun v => decide (bytesOf v = s))).length
          = ((paths root).filter (fun P => decide (enc P = s))).length) := by
  sorry

/-- Whenever binary_tree_paths(root) returns a result r, every byte b in every r[i] is one of: an ASCII decimal digit (48 <= b <= 57), a hyphen-minus '-' (b = 45), or a greater-than sign '>' (b = 62). Moreover every '>' byte (62) is immediately preceded by a '-' byte (45) and is immediately followed by either a decimal digit (48..57) or a '-' byte (45); no '>' occurs at the last byte of r[i].
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_9 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        BytesOK (bytesOf (r.val[i]'hi)) ∧ ArrowsWellFormed (bytesOf (r.val[i]'hi)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        BytesOK (bytesOf (r.val[i]'hi)) ∧ ArrowsWellFormed (bytesOf (r.val[i]'hi))) := by
  sorry

/-- Whenever binary_tree_paths(root) returns a result r, for every i with 0 <= i < len(r), split r[i] at every occurrence of the two-byte separator [45,62]; each resulting non-empty byte segment, interpreted as a decimal integer, lies in the interval [-100,100].
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_10 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        ∀ seg ∈ segments (bytesOf (r.val[i]'hi)),
          ∃ z : Int, parseInt seg = some z ∧ -100 ≤ z ∧ z ≤ 100 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        ∀ seg ∈ segments (bytesOf (r.val[i]'hi)),
          ∃ z : Int, parseInt seg = some z ∧ -100 ≤ z ∧ z ≤ 100) := by
  sorry

/-- Whenever binary_tree_paths(root) returns a result r, for every i with 0 <= i < len(r), len(r[i]) <= 4*N + 2*(N-1), where N is the number of nodes of root. (Every integer component has at most 4 ASCII bytes because values are in [-100,100], and a path of at most N nodes contains at most N-1 separators.)
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_11 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        (bytesOf (r.val[i]'hi)).length ≤ 4 * N + 2 * (N - 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        (bytesOf (r.val[i]'hi)).length ≤ 4 * N + 2 * (N - 1)) := by
  sorry

/-- Whenever binary_tree_paths(root) returns a result r, for every i with 0 <= i < len(r) and every integer component of r[i] obtained by splitting on the separator [45,62], if the component represents the integer 0 then it is exactly the single byte [48]; otherwise its first byte is not '0' (48).
  Preconditions: root is a finite binary tree (Tree) with N nodes, where 1 <= N <= 100, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_12 (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        ∀ seg ∈ segments (bytesOf (r.val[i]'hi)),
          ∀ z : Int, parseInt seg = some z →
            (z = 0 → seg = [48]) ∧ (z ≠ 0 → ∀ b : Nat, seg.head? = some b → b ≠ 48) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree) (N : Nat) (hN : numNodes root = N) (hN1 : 1 ≤ N)
    (hN100 : N ≤ 100) (hval : valuesWithin (-100) 100 root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      binary_tree_paths root = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        ∀ seg ∈ segments (bytesOf (r.val[i]'hi)),
          ∀ z : Int, parseInt seg = some z →
            (z = 0 → seg = [48]) ∧ (z ≠ 0 → ∀ b : Nat, seg.head? = some b → b ≠ 48)) := by
  sorry

end AegisSpec.BinaryTreePaths
