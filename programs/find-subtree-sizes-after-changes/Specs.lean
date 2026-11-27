import Aegis.FindSubtreeSizes.Code.Funs

/-!
# Specifications of `Aegis.FindSubtreeSizes.find_subtree_sizes`

LeetCode problem `find-subtree-sizes-after-changes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindSubtreeSizes

  open Classical

  attribute [local instance] Classical.propDecidable

  def numNodes (parent : Slice Std.I64) : ℕ := parent.val.length

  def parList (parent : Slice Std.I64) : List ℤ := parent.val.map (fun x => x.val)

  def letters (s : Slice Std.U8) : List ℕ := s.val.map (fun c => c.val)

  def resList (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun x => x.val)

  def par (p : List ℤ) (i : ℕ) : ℕ := (p.getD i 0).toNat

  def iter (p : List ℤ) : ℕ → ℕ → ℕ
    | 0, i => i
    | (k + 1), i => iter p k (par p i)

  noncomputable def depth (p : List ℤ) (i : ℕ) : ℕ :=
    if h : ∃ k, iter p k i = 0 then Nat.find h else 0

  def StrictAncestor (p : List ℤ) (y x : ℕ) : Prop :=
    ∃ k, y = iter p (k + 1) x

  def OrigAncestorOrSelf (p : List ℤ) (y u : ℕ) : Prop :=
    y = u ∨ (u ≠ 0 ∧ StrictAncestor p y u)

  def InA (sl : List ℕ) (p : List ℤ) (x y : ℕ) : Prop :=
    StrictAncestor p y x ∧ sl.getD y 0 = sl.getD x 0

  def NewParent (sl : List ℕ) (p : List ℤ) (x y : ℕ) : Prop :=
    (InA sl p x y ∧ ∀ z, InA sl p x z → depth p z ≤ depth p y) ∨
      (¬∃ z, InA sl p x z) ∧ y = par p x

  inductive FinalAncestor (sl : List ℕ) (p : List ℤ) : ℕ → ℕ → Prop where
    | refl (u : ℕ) : FinalAncestor sl p u u
    | step {u w v : ℕ} (hne : u ≠ 0) (hp : NewParent sl p u w)
        (h : FinalAncestor sl p v w) : FinalAncestor sl p v u

  noncomputable def Size (sl : List ℕ) (p : List ℤ) (v : ℕ) : ℕ :=
    ((Finset.range p.length).filter (fun u => FinalAncestor sl p v u)).card

  noncomputable def OrigSize (p : List ℤ) (v : ℕ) : ℕ :=
    ((Finset.range p.length).filter (fun u => OrigAncestorOrSelf p v u)).card

  noncomputable def sumOverChildren (sl : List ℕ) (p : List ℤ) (r : List ℤ) (v : ℕ) : ℤ :=
    ∑ u ∈ (Finset.range p.length).filter (fun u => 1 ≤ u ∧ NewParent sl p u v), r.getD u 0

  structure ValidInput (parent : Slice Std.I64) (s : Slice Std.U8) : Prop where

    len_s : s.val.length = parent.val.length

    n_ge_one : 1 ≤ numNodes parent

    n_le : numNodes parent ≤ 100000

    root : (parList parent).getD 0 0 = -1

    parent_range : ∀ i, 1 ≤ i → i < numNodes parent →
      0 ≤ (parList parent).getD i 0 ∧ (parList parent).getD i 0 < (numNodes parent : ℤ)

    reaches_root : ∀ i, 1 ≤ i → i < numNodes parent →
      ∃ k, iter (parList parent) k i = 0

    letters_range : ∀ i, i < numNodes parent →
      97 ≤ (letters s).getD i 0 ∧ (letters s).getD i 0 ≤ 122

  def NoLetterOnChain (parent : Slice Std.I64) (s : Slice Std.U8) : Prop :=
    ∀ x y, 1 ≤ x → x < numNodes parent → StrictAncestor (parList parent) y x →
      (letters s).getD y 0 ≠ (letters s).getD x 0

  /-- Whenever the function returns a result r, r is a vector of length n, and for every v with 0 <= v < n, r[v] = size(v), where size is defined as follows: define depth(0)=0 and for i>=1, depth(i)=depth(parent[i])+1; for nodes x,y, y is a strict ancestor of x iff y is on the parent chain from parent[x] to 0 (i.e., either parent[x]=y, or parent[x]!=-1 and y is a strict ancestor of parent[x]); for each x with 1<=x<n, let A(x) = { y : 0<=y<n, y is a strict ancestor of x, and s[y]=s[x] }; define newpar(x) as the unique y in A(x) with maximal depth if A(x) is nonempty, and as parent[x] if A(x) is empty; the final tree has nodes {0,...,n-1}, root 0, and for each x>=1 the parent of x is newpar(x); for nodes u,v, v is an ancestor of u in the final tree (including u=v) iff v=u, or (u!=0 and v is an ancestor of newpar(u) in the final tree); finally, size(v) is the number of u with 0<=u<n such that v is an ancestor of u in the final tree.
    Preconditions: Let n = len(parent). The inputs satisfy: len(s) = n; 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; for every i with 1 <= i < n, repeatedly applying parent (i, parent[i], parent[parent[i]], ...) reaches 0 after finitely many steps (equivalently, parent describes a valid rooted tree at 0); and s consists only of lowercase English letters, i.e., 97 <= s[i] <= 122 for every i with 0 <= i < n. -/
  theorem spec_1 (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
        r.val.length = numNodes parent ∧
          ∀ v : ℕ, v < numNodes parent →
            (resList r).getD v 0 =
              (Size (letters s) (parList parent) v : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
          r.val.length = numNodes parent ∧
            ∀ v : ℕ, v < numNodes parent →
              (resList r).getD v 0 =
                (Size (letters s) (parList parent) v : ℤ)) := by
    sorry

  /-- The function returns a result r (it does not fail, overflow, or panic) for every input satisfying the preconditions.
    Preconditions: Let n = len(parent). The inputs satisfy: len(s) = n; 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; for every i with 1 <= i < n, repeatedly applying parent (i, parent[i], parent[parent[i]], ...) reaches 0 after finitely many steps (equivalently, parent describes a valid rooted tree at 0); and s consists only of lowercase English letters, i.e., 97 <= s[i] <= 122 for every i with 0 <= i < n. -/
  theorem spec_2 (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every v with 0 <= v < n, 1 <= r[v] <= n.
    Preconditions: Let n = len(parent). The inputs satisfy: len(s) = n; 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; for every i with 1 <= i < n, repeatedly applying parent (i, parent[i], parent[parent[i]], ...) reaches 0 after finitely many steps (equivalently, parent describes a valid rooted tree at 0); and s consists only of lowercase English letters, i.e., 97 <= s[i] <= 122 for every i with 0 <= i < n. -/
  theorem spec_3 (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
        ∀ v : ℕ, v < numNodes parent →
          1 ≤ (resList r).getD v 0 ∧ (resList r).getD v 0 ≤ (numNodes parent : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
          ∀ v : ℕ, v < numNodes parent →
            1 ≤ (resList r).getD v 0 ∧ (resList r).getD v 0 ≤ (numNodes parent : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r[0] = n.
    Preconditions: Let n = len(parent). The inputs satisfy: len(s) = n; 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; for every i with 1 <= i < n, repeatedly applying parent (i, parent[i], parent[parent[i]], ...) reaches 0 after finitely many steps (equivalently, parent describes a valid rooted tree at 0); and s consists only of lowercase English letters, i.e., 97 <= s[i] <= 122 for every i with 0 <= i < n. -/
  theorem spec_4 (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
        (resList r).getD 0 0 = (numNodes parent : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
          (resList r).getD 0 0 = (numNodes parent : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every v with 0 <= v < n, r[v] = 1 + sum_{u : 1 <= u < n and newpar(u) = v} r[u], where newpar is defined as in the main specification: newpar(u) is the unique strict ancestor y of u with s[y]=s[u] and maximal depth if such a y exists, and newpar(u)=parent[u] otherwise.
    Preconditions: Let n = len(parent). The inputs satisfy: len(s) = n; 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; for every i with 1 <= i < n, repeatedly applying parent (i, parent[i], parent[parent[i]], ...) reaches 0 after finitely many steps (equivalently, parent describes a valid rooted tree at 0); and s consists only of lowercase English letters, i.e., 97 <= s[i] <= 122 for every i with 0 <= i < n. -/
  theorem spec_5 (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
        ∀ v : ℕ, v < numNodes parent →
          (resList r).getD v 0 =
            1 + sumOverChildren (letters s) (parList parent) (resList r) v := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
          ∀ v : ℕ, v < numNodes parent →
            (resList r).getD v 0 =
              1 + sumOverChildren (letters s) (parList parent) (resList r) v) := by
    sorry

  /-- Whenever the function returns a result r, for every v with 0 <= v < n, r[v] equals the number of u with 0 <= u < n such that either u=v, or (u!=0 and v appears in the sequence parent[u], parent[parent[u]], ..., 0).
    Preconditions: Let n = len(parent). The inputs satisfy: len(s) = n; 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; for every i with 1 <= i < n, repeatedly applying parent (i, parent[i], parent[parent[i]], ...) reaches 0 after finitely many steps (equivalently, parent describes a valid rooted tree at 0); and s consists only of lowercase English letters, i.e., 97 <= s[i] <= 122 for every i with 0 <= i < n. Additionally, for every x with 1 <= x < n and every y that appears in the sequence parent[x], parent[parent[x]], ..., 0, we have s[y] != s[x]. -/
  theorem spec_6 (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s)
      (hno : NoLetterOnChain parent s) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
        ∀ v : ℕ, v < numNodes parent →
          (resList r).getD v 0 = (OrigSize (parList parent) v : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s)
        (hno : NoLetterOnChain parent s), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
          ∀ v : ℕ, v < numNodes parent →
            (resList r).getD v 0 = (OrigSize (parList parent) v : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every v with 0 <= v < n, r[v] <= the number of u with 0 <= u < n such that either u=v, or (u!=0 and v appears in the sequence parent[u], parent[parent[u]], ..., 0).
    Preconditions: Let n = len(parent). The inputs satisfy: len(s) = n; 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; for every i with 1 <= i < n, repeatedly applying parent (i, parent[i], parent[parent[i]], ...) reaches 0 after finitely many steps (equivalently, parent describes a valid rooted tree at 0); and s consists only of lowercase English letters, i.e., 97 <= s[i] <= 122 for every i with 0 <= i < n. -/
  theorem spec_7 (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
        ∀ v : ℕ, v < numNodes parent →
          (resList r).getD v 0 ≤ (OrigSize (parList parent) v : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
          ∀ v : ℕ, v < numNodes parent →
            (resList r).getD v 0 ≤ (OrigSize (parList parent) v : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every v with 0 <= v < n, if there is no u with 1 <= u < n and newpar(u) = v (where newpar is as defined in the main specification), then r[v] = 1.
    Preconditions: Let n = len(parent). The inputs satisfy: len(s) = n; 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; for every i with 1 <= i < n, repeatedly applying parent (i, parent[i], parent[parent[i]], ...) reaches 0 after finitely many steps (equivalently, parent describes a valid rooted tree at 0); and s consists only of lowercase English letters, i.e., 97 <= s[i] <= 122 for every i with 0 <= i < n. -/
  theorem spec_8 (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
        ∀ v : ℕ, v < numNodes parent →
          (¬∃ u, 1 ≤ u ∧ u < numNodes parent ∧
              NewParent (letters s) (parList parent) u v) →
            (resList r).getD v 0 = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
          ∀ v : ℕ, v < numNodes parent →
            (¬∃ u, 1 ≤ u ∧ u < numNodes parent ∧
                NewParent (letters s) (parList parent) u v) →
              (resList r).getD v 0 = 1) := by
    sorry

  /-- Whenever the function returns a result r, for every v with 1 <= v < n, 1 <= r[v] < n.
    Preconditions: Let n = len(parent). The inputs satisfy: len(s) = n; 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; for every i with 1 <= i < n, repeatedly applying parent (i, parent[i], parent[parent[i]], ...) reaches 0 after finitely many steps (equivalently, parent describes a valid rooted tree at 0); and s consists only of lowercase English letters, i.e., 97 <= s[i] <= 122 for every i with 0 <= i < n. -/
  theorem spec_9 (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
        ∀ v : ℕ, 1 ≤ v → v < numNodes parent →
          1 ≤ (resList r).getD v 0 ∧ (resList r).getD v 0 < (numNodes parent : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (h : ValidInput parent s), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindSubtreeSizes.find_subtree_sizes parent s = ok r →
          ∀ v : ℕ, 1 ≤ v → v < numNodes parent →
            1 ≤ (resList r).getD v 0 ∧ (resList r).getD v 0 < (numNodes parent : ℤ)) := by
    sorry

  end AegisSpec.FindSubtreeSizes
