import Aegis.FindFrequentTreeSum.Code.Funs

/-!
# Specifications of `Aegis.FindFrequentTreeSum.find_frequent_tree_sum`

LeetCode problem `most-frequent-subtree-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindFrequentTreeSum

  open Aegis.FindFrequentTreeSum (Tree find_frequent_tree_sum)

  def size : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => size l + size r + 1

  def subtreeSum : Tree → Int
    | Tree.Null => 0
    | Tree.Node v l r => v.val + subtreeSum l + subtreeSum r

  def subtreeSums : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => (v.val + subtreeSum l + subtreeSum r) :: (subtreeSums l ++ subtreeSums r)

  def allValuesInRange : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
      -100000 ≤ v.val ∧ v.val ≤ 100000 ∧ allValuesInRange l ∧ allValuesInRange r

  def ValidInput (t : Tree) : Prop :=
    t ≠ Tree.Null ∧ 1 ≤ size t ∧ size t ≤ 10000 ∧ allValuesInRange t

  def countOcc (l : List Int) (s : Int) : Nat := (l.filter (fun x => x = s)).length

  def freqRoot (t : Tree) (s : Int) : Nat := countOcc (subtreeSums t) s

  def maxFreq (t : Tree) : Nat :=
    (subtreeSums t).foldr (fun s acc => max (freqRoot t s) acc) 0

  def maxFreqCount (t : Tree) : Nat :=
    ((subtreeSums t).dedup.filter (fun s => freqRoot t s = maxFreq t)).length

  def countInResult (r : alloc.vec.Vec I64) (s : Int) : Nat :=
    countOcc (r.val.map (fun x => x.val)) s

  def mirror : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

  /-- The function returns a result r (it does not fail). For every integer s, let freq_root(s) be the number of node occurrences u in root whose subtree sum equals s, where the subtree sum at u is the sum of the values of u and all descendants of u, and let maxfreq(root) be the maximum of freq_root(s) over all integers s. Then the number of indices i with 0 <= i < len(r) and r[i] = s is 1 if freq_root(s) = maxfreq(root), and 0 otherwise. Thus, in any order and with no duplicates, r contains exactly the subtree-sum values that occur with maximum frequency.
    Preconditions: root is not Tree.Null. Let n be the number of Node occurrences in root; 1 <= n <= 10000. For every node occurrence u in root with value v, -100000 <= v <= 100000. -/
  theorem spec_1 (root : Tree) (h : ValidInput root) :
      ∃ r : alloc.vec.Vec I64,
        find_frequent_tree_sum root = ok r ∧
          ∀ s : Int, countInResult r s = if freqRoot root s = maxFreq root then 1 else 0 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (h : ValidInput root), ∃ r : alloc.vec.Vec I64,
          find_frequent_tree_sum root = ok r ∧
            ∀ s : Int, countInResult r s = if freqRoot root s = maxFreq root then 1 else 0) := by
    sorry

  /-- The function returns a result r; it does not fail on any input satisfying the preconditions. In particular, for every node occurrence u in root, the mathematical subtree sum at u has absolute value at most 100000*n <= 1,000,000,000, so no i64 overflow occurs, and the non-empty root guarantees that a maximum frequency is defined.
    Preconditions: root is not Tree.Null. Let n be the number of Node occurrences in root; 1 <= n <= 10000. For every node occurrence u in root with value v, -100000 <= v <= 100000. -/
  theorem spec_2 (root : Tree) (h : ValidInput root) :
      ∃ r : alloc.vec.Vec I64,
        find_frequent_tree_sum root = ok r ∧
          (∀ s ∈ subtreeSums root,
            -((100000 : Int) * (size root : Int)) ≤ s ∧
              s ≤ (100000 : Int) * (size root : Int)) ∧
            (100000 : Int) * (size root : Int) ≤ 1000000000 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (h : ValidInput root), ∃ r : alloc.vec.Vec I64,
          find_frequent_tree_sum root = ok r ∧
            (∀ s ∈ subtreeSums root,
              -((100000 : Int) * (size root : Int)) ≤ s ∧
                s ≤ (100000 : Int) * (size root : Int)) ∧
              (100000 : Int) * (size root : Int) ≤ 1000000000) := by
    sorry

  /-- The function returns a result r, and for every index i with 0 <= i < len(r), -100000*n <= r[i] <= 100000*n. Equivalently, |r[i]| <= 1,000,000,000 because n <= 10000.
    Preconditions: root is not Tree.Null. Let n be the number of Node occurrences in root; 1 <= n <= 10000. For every node occurrence u in root with value v, -100000 <= v <= 100000. -/
  theorem spec_3 (root : Tree) (h : ValidInput root) :
      ∃ r : alloc.vec.Vec I64,
        find_frequent_tree_sum root = ok r ∧
          ∀ i (hi : i < r.val.length),
            -((100000 : Int) * (size root : Int)) ≤ (r.val[i]'hi).val ∧
              (r.val[i]'hi).val ≤ (100000 : Int) * (size root : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (h : ValidInput root), ∃ r : alloc.vec.Vec I64,
          find_frequent_tree_sum root = ok r ∧
            ∀ i (hi : i < r.val.length),
              -((100000 : Int) * (size root : Int)) ≤ (r.val[i]'hi).val ∧
                (r.val[i]'hi).val ≤ (100000 : Int) * (size root : Int)) := by
    sorry

  /-- The function returns a result r, and 1 <= len(r) <= n.
    Preconditions: root is not Tree.Null. Let n be the number of Node occurrences in root; 1 <= n <= 10000. For every node occurrence u in root with value v, -100000 <= v <= 100000. -/
  theorem spec_4 (root : Tree) (h : ValidInput root) :
      ∃ r : alloc.vec.Vec I64,
        find_frequent_tree_sum root = ok r ∧ 1 ≤ r.val.length ∧ r.val.length ≤ size root := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (h : ValidInput root), ∃ r : alloc.vec.Vec I64,
          find_frequent_tree_sum root = ok r ∧ 1 ≤ r.val.length ∧ r.val.length ≤ size root) := by
    sorry

  /-- The function returns a result r, and for every index i with 0 <= i < len(r), there exists a node occurrence u in root such that the subtree sum at u equals r[i].
    Preconditions: root is not Tree.Null. Let n be the number of Node occurrences in root; 1 <= n <= 10000. For every node occurrence u in root with value v, -100000 <= v <= 100000. -/
  theorem spec_5 (root : Tree) (h : ValidInput root) :
      ∃ r : alloc.vec.Vec I64,
        find_frequent_tree_sum root = ok r ∧
          ∀ i (hi : i < r.val.length), (r.val[i]'hi).val ∈ subtreeSums root := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (h : ValidInput root), ∃ r : alloc.vec.Vec I64,
          find_frequent_tree_sum root = ok r ∧
            ∀ i (hi : i < r.val.length), (r.val[i]'hi).val ∈ subtreeSums root) := by
    sorry

  /-- The function returns a result r, and for every index i with 0 <= i < len(r), freq_root(r[i]) = maxfreq(root), where freq_root(s) counts node occurrences in root whose subtree sum is s and maxfreq(root) is the largest such frequency over all integers s.
    Preconditions: root is not Tree.Null. Let n be the number of Node occurrences in root; 1 <= n <= 10000. For every node occurrence u in root with value v, -100000 <= v <= 100000. -/
  theorem spec_6 (root : Tree) (h : ValidInput root) :
      ∃ r : alloc.vec.Vec I64,
        find_frequent_tree_sum root = ok r ∧
          ∀ i (hi : i < r.val.length), freqRoot root (r.val[i]'hi).val = maxFreq root := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (h : ValidInput root), ∃ r : alloc.vec.Vec I64,
          find_frequent_tree_sum root = ok r ∧
            ∀ i (hi : i < r.val.length), freqRoot root (r.val[i]'hi).val = maxFreq root) := by
    sorry

  /-- The function returns a result r, and for every integer s, if freq_root(s) = maxfreq(root), then there exists an index i with 0 <= i < len(r) and r[i] = s, where freq_root(s) counts node occurrences in root whose subtree sum is s and maxfreq(root) is the largest such frequency over all integers s.
    Preconditions: root is not Tree.Null. Let n be the number of Node occurrences in root; 1 <= n <= 10000. For every node occurrence u in root with value v, -100000 <= v <= 100000. -/
  theorem spec_7 (root : Tree) (h : ValidInput root) :
      ∃ r : alloc.vec.Vec I64,
        find_frequent_tree_sum root = ok r ∧
          ∀ s : Int, freqRoot root s = maxFreq root →
            ∃ i, ∃ hi : i < r.val.length, (r.val[i]'hi).val = s := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (h : ValidInput root), ∃ r : alloc.vec.Vec I64,
          find_frequent_tree_sum root = ok r ∧
            ∀ s : Int, freqRoot root s = maxFreq root →
              ∃ i, ∃ hi : i < r.val.length, (r.val[i]'hi).val = s) := by
    sorry

  /-- The function returns a result r, and for all indices i and j with 0 <= i < len(r) and 0 <= j < len(r), if r[i] = r[j] then i = j. Thus r contains no duplicate values.
    Preconditions: root is not Tree.Null. Let n be the number of Node occurrences in root; 1 <= n <= 10000. For every node occurrence u in root with value v, -100000 <= v <= 100000. -/
  theorem spec_8 (root : Tree) (h : ValidInput root) :
      ∃ r : alloc.vec.Vec I64,
        find_frequent_tree_sum root = ok r ∧
          ∀ i (hi : i < r.val.length) (j : Nat) (hj : j < r.val.length),
            (r.val[i]'hi).val = (r.val[j]'hj).val → i = j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (h : ValidInput root), ∃ r : alloc.vec.Vec I64,
          find_frequent_tree_sum root = ok r ∧
            ∀ i (hi : i < r.val.length) (j : Nat) (hj : j < r.val.length),
              (r.val[i]'hi).val = (r.val[j]'hj).val → i = j) := by
    sorry

  /-- The function returns a result r, and for every integer s that does not occur as an element of r, freq_root(s) < maxfreq(root), where freq_root(s) counts node occurrences in root whose subtree sum is s and maxfreq(root) is the largest such frequency over all integers s.
    Preconditions: root is not Tree.Null. Let n be the number of Node occurrences in root; 1 <= n <= 10000. For every node occurrence u in root with value v, -100000 <= v <= 100000. -/
  theorem spec_9 (root : Tree) (h : ValidInput root) :
      ∃ r : alloc.vec.Vec I64,
        find_frequent_tree_sum root = ok r ∧
          ∀ s : Int, s ∉ (r.val.map (fun x => x.val)) → freqRoot root s < maxFreq root := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (h : ValidInput root), ∃ r : alloc.vec.Vec I64,
          find_frequent_tree_sum root = ok r ∧
            ∀ s : Int, s ∉ (r.val.map (fun x => x.val)) → freqRoot root s < maxFreq root) := by
    sorry

  /-- The function returns a result r, and len(r) equals the number of distinct integers s such that freq_root(s) = maxfreq(root), where freq_root(s) counts node occurrences in root whose subtree sum is s and maxfreq(root) is the largest such frequency over all integers s.
    Preconditions: root is not Tree.Null. Let n be the number of Node occurrences in root; 1 <= n <= 10000. For every node occurrence u in root with value v, -100000 <= v <= 100000. -/
  theorem spec_10 (root : Tree) (h : ValidInput root) :
      ∃ r : alloc.vec.Vec I64,
        find_frequent_tree_sum root = ok r ∧ r.val.length = maxFreqCount root := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (h : ValidInput root), ∃ r : alloc.vec.Vec I64,
          find_frequent_tree_sum root = ok r ∧ r.val.length = maxFreqCount root) := by
    sorry

  /-- When find_frequent_tree_sum is called on root and on root', both calls return results r and r', and r' is a permutation of r (that is, r and r' have the same elements with the same multiplicities).
    Preconditions: root and root' are non-null trees satisfying the same size and value constraints as in spec_1. root' is the mirror image of root: recursively, Tree.Null remains Tree.Null and Tree.Node(v,l,r) becomes Tree.Node(v, mirror(r), mirror(l)). -/
  theorem spec_11 (root root' : Tree) (h : ValidInput root) (h' : ValidInput root')
      (hmirror : root' = mirror root) :
      ∃ r r' : alloc.vec.Vec I64,
        find_frequent_tree_sum root = ok r ∧ find_frequent_tree_sum root' = ok r' ∧
          (r.val.map (fun x => x.val)).Perm (r'.val.map (fun x => x.val)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root root' : Tree) (h : ValidInput root) (h' : ValidInput root')
        (hmirror : root' = mirror root), ∃ r r' : alloc.vec.Vec I64,
          find_frequent_tree_sum root = ok r ∧ find_frequent_tree_sum root' = ok r' ∧
            (r.val.map (fun x => x.val)).Perm (r'.val.map (fun x => x.val))) := by
    sorry

  end AegisSpec.FindFrequentTreeSum
