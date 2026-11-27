import Aegis.RootCount.Code.Funs

/-!
# Specifications of `Aegis.RootCount.root_count`

LeetCode problem `count-number-of-possible-root-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.RootCount

namespace AegisSpec.RootCount

def vecVal (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

def sliceVal (s : Slice (alloc.vec.Vec Std.I64)) : List (List Int) := s.val.map vecVal

def i64OfInt (x : Int) : Std.I64 := ⟨BitVec.ofInt 64 x⟩

def sumInts (l : List Int) : Int := l.foldl (fun acc x => acc + x) 0

noncomputable def countWhere {α : Type} (p : α → Prop) (l : List α) : Nat :=
  (l.filter (fun a => @decide (p a) (Classical.propDecidable (p a)))).length

def adj (es : List (List Int)) (a b : Int) : Prop := [a, b] ∈ es ∨ [b, a] ∈ es

def walk (es : List (List Int)) (d : Nat) : Int → Int → Prop :=
  Nat.rec (fun a b => a = b)
    (fun (_ : Nat) (S : Int → Int → Prop) (a b : Int) => ∃ c : Int, adj es a c ∧ S c b) d

@[simp]
theorem walk_zero (es : List (List Int)) (a b : Int) : walk es 0 a b ↔ a = b :=
  Iff.rfl

@[simp]
theorem walk_succ (es : List (List Int)) (d : Nat) (a b : Int) :
    walk es (d + 1) a b ↔ ∃ c : Int, adj es a c ∧ walk es d c b :=
  Iff.rfl

def reach (es : List (List Int)) (a b : Int) : Prop := ∃ d : Nat, walk es d a b

def connected (n : Nat) (es : List (List Int)) : Prop :=
  ∀ a b : Int, 0 ≤ a → a < (n : Int) → 0 ≤ b → b < (n : Int) → reach es a b

def eraseEdge (es : List (List Int)) (a b : Int) : List (List Int) :=
  es.filter (fun e => !decide (e = [a, b]) && !decide (e = [b, a]))

def acyclic (es : List (List Int)) : Prop :=
  ∀ a b : Int, adj es a b → ¬ reach (eraseEdge es a b) a b

def isPairList (n : Nat) (es : List (List Int)) : Prop :=
  ∀ e ∈ es, ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < (n : Int) ∧ 0 ≤ b ∧ b < (n : Int) ∧ a ≠ b

def isDist (es : List (List Int)) (a b : Int) (d : Nat) : Prop :=
  walk es d a b ∧ ∀ d' : Nat, walk es d' a b → d ≤ d'

def isParent (es : List (List Int)) (r u v : Int) : Prop :=
  adj es u v ∧ ∃ du dv : Nat, isDist es r u du ∧ isDist es r v dv ∧ du + 1 = dv

noncomputable def trueGuesses (es gs : List (List Int)) (r : Int) : Nat :=
  countWhere (fun g => ∃ u v : Int, g = [u, v] ∧ isParent es r u v) gs

noncomputable def countRootsGe (n : Nat) (es gs : List (List Int)) (k : Int) : Nat :=
  countWhere (fun i : Nat => k ≤ (trueGuesses es gs (i : Int) : Int)) (List.range n)

noncomputable def countRootsEq (n : Nat) (es gs : List (List Int)) (k : Int) : Nat :=
  countWhere (fun i : Nat => (trueGuesses es gs (i : Int) : Int) = k) (List.range n)

noncomputable def componentSize (n : Nat) (es : List (List Int)) (a b : Int) : Nat :=
  countWhere (fun i : Nat => reach (eraseEdge es a b) a (i : Int)) (List.range n)

def swappedOneEdge (es es' : List (List Int)) : Prop :=
  ∃ (i : Nat) (a b : Int), es[i]? = some [a, b] ∧ es' = es.set i [b, a]

/-- The function returns a result r, and r = |{ root in {0, 1, ..., n-1} : true_guesses(root) >= k }|, where for each root in {0, 1, ..., n-1}, orient the tree away from root and define true_guesses(root) as the number of indices j with 0 <= j < len(guesses) such that, writing guesses[j] = [u, v], u is the parent of v in this rooted tree; equivalently, u is the unique neighbor of v on the path from root to v, or dist(root, u) + 1 = dist(root, v) where dist is the number of edges on the unique path in the tree. (n = len(edges) + 1.)
  Preconditions: Let n = len(edges) + 1. Then 2 <= n <= 100000. The list edges has length n - 1, and each element is a list of length 2 [a, b] with 0 <= a < n, 0 <= b < n, and a != b. The undirected graph on vertices {0, 1, ..., n-1} whose edges are the unordered pairs {a, b} for each [a, b] in edges is a tree (connected and acyclic). Let m = len(guesses). Then 1 <= m <= 100000. Each element of guesses is a list of length 2 [u, v] with 0 <= u < n, 0 <= v < n, and u != v. For every guess [u, v] in guesses, {u, v} is an edge of the tree. The guesses are pairwise distinct as ordered pairs. The integer k satisfies 0 <= k <= m. -/
theorem spec_1 (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_len_hi : (sliceVal guesses).length ≤ 100000)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int)) :
    ∃ r : Std.I64, root_count edges guesses k = ok r ∧
      r.val = (countRootsGe n (sliceVal edges) (sliceVal guesses) k.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_len_hi : (sliceVal guesses).length ≤ 100000)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int)), ∃ r : Std.I64, root_count edges guesses k = ok r ∧
      r.val = (countRootsGe n (sliceVal edges) (sliceVal guesses) k.val : Int)) := by
  sorry

/-- Whenever the function returns a result r, r <= len(edges) + 1.
  Preconditions: Let n = len(edges) + 1. The list edges has length n - 1, and each element is a list of length 2 [a, b] with 0 <= a < n, 0 <= b < n, and a != b. The undirected graph on vertices {0, 1, ..., n-1} whose edges are the unordered pairs {a, b} for each [a, b] in edges is a tree (connected and acyclic). The list guesses has length at least 1, and each element is a list of length 2 [u, v] with 0 <= u < n, 0 <= v < n, and u != v. For every guess [u, v] in guesses, {u, v} is an edge of the tree. The guesses are pairwise distinct as ordered pairs. The integer k satisfies 0 <= k <= len(guesses). Also n >= 2. -/
theorem spec_2 (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int)) :
    ∀ r : Std.I64, root_count edges guesses k = ok r → r.val ≤ ((sliceVal edges).length : Int) + 1 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int)), ∀ r : Std.I64, root_count edges guesses k = ok r → r.val ≤ ((sliceVal edges).length : Int) + 1) := by
  sorry

/-- The function returns a result r and r equals the number of nodes in the connected component containing u after removing the edge {u, v} from the tree (i.e., the component of u when the tree is split by deleting the edge between u and v).
  Preconditions: Let n = len(edges) + 1. Then 2 <= n <= 100000. The list edges has length n - 1, and each element is a list of length 2 [a, b] with 0 <= a < n, 0 <= b < n, and a != b. The undirected graph on vertices {0, 1, ..., n-1} whose edges are the unordered pairs {a, b} for each [a, b] in edges is a tree (connected and acyclic). Let m = len(guesses). Then 1 <= m <= 100000. Each element of guesses is a list of length 2 [u, v] with 0 <= u < n, 0 <= v < n, and u != v. For every guess [u, v] in guesses, {u, v} is an edge of the tree. The guesses are pairwise distinct as ordered pairs. The integer k satisfies 0 <= k <= m. Additionally, m = 1, k = 1, and guesses[0] = [u, v]. -/
theorem spec_3 (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (u v : Int)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_len_hi : (sliceVal guesses).length ≤ 100000)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int))
    (hm : (sliceVal guesses).length = 1) (hk_one : k.val = 1)
    (hguess_zero : (sliceVal guesses)[0]? = some [u, v]) :
    ∃ r : Std.I64, root_count edges guesses k = ok r ∧
      r.val = (componentSize n (sliceVal edges) u v : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (u v : Int)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_len_hi : (sliceVal guesses).length ≤ 100000)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int))
    (hm : (sliceVal guesses).length = 1) (hk_one : k.val = 1)
    (hguess_zero : (sliceVal guesses)[0]? = some [u, v]), ∃ r : Std.I64, root_count edges guesses k = ok r ∧
      r.val = (componentSize n (sliceVal edges) u v : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every root in {0, 1, ..., n-1}, the number of true guesses for that root is strictly less than k.
  Preconditions: Let n = len(edges) + 1. The list edges has length n - 1, and each element is a list of length 2 [a, b] with 0 <= a < n, 0 <= b < n, and a != b. The undirected graph on vertices {0, 1, ..., n-1} whose edges are the unordered pairs {a, b} for each [a, b] in edges is a tree (connected and acyclic). The list guesses has length at least 1, and each element is a list of length 2 [u, v] with 0 <= u < n, 0 <= v < n, and u != v. For every guess [u, v] in guesses, {u, v} is an edge of the tree. The guesses are pairwise distinct as ordered pairs. The integer k satisfies 0 <= k <= len(guesses). Also n >= 2. -/
theorem spec_4 (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int)) :
    ∀ r : Std.I64, root_count edges guesses k = ok r →
      (r.val = 0 ↔ ∀ root : Int, 0 ≤ root → root < (n : Int) →
        (trueGuesses (sliceVal edges) (sliceVal guesses) root : Int) < k.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int)), ∀ r : Std.I64, root_count edges guesses k = ok r →
      (r.val = 0 ↔ ∀ root : Int, 0 ≤ root → root < (n : Int) →
        (trueGuesses (sliceVal edges) (sliceVal guesses) root : Int) < k.val)) := by
  sorry

/-- If the function returns result r on (edges, guesses, k) and result r' on (edges', guesses', k), then r = r'.
  Preconditions: Let n = len(edges) + 1. The list edges has length n - 1, and each element is a list of length 2 [a, b] with 0 <= a < n, 0 <= b < n, and a != b. The undirected graph on vertices {0, 1, ..., n-1} whose edges are the unordered pairs {a, b} for each [a, b] in edges is a tree (connected and acyclic). The list guesses has length at least 1, and each element is a list of length 2 [u, v] with 0 <= u < n, 0 <= v < n, and u != v. For every guess [u, v] in guesses, {u, v} is an edge of the tree. The guesses are pairwise distinct as ordered pairs. The integer k satisfies 0 <= k <= len(guesses). Also n >= 2. Let edges' be any list that is a permutation of edges (same length and same multiset of elements), and let guesses' be any list that is a permutation of guesses. -/
theorem spec_5 (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (edges' guesses' : Slice (alloc.vec.Vec Std.I64))
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int))
    (hedges'_perm : (sliceVal edges').Perm (sliceVal edges))
    (hguesses'_perm : (sliceVal guesses').Perm (sliceVal guesses)) :
    ∀ r r' : Std.I64, root_count edges guesses k = ok r →
      root_count edges' guesses' k = ok r' → r.val = r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (edges' guesses' : Slice (alloc.vec.Vec Std.I64))
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int))
    (hedges'_perm : (sliceVal edges').Perm (sliceVal edges))
    (hguesses'_perm : (sliceVal guesses').Perm (sliceVal guesses)), ∀ r r' : Std.I64, root_count edges guesses k = ok r →
      root_count edges' guesses' k = ok r' → r.val = r'.val) := by
  sorry

/-- If the function returns result r on (edges, guesses, k) and result r' on (edges', guesses, k), then r = r'.
  Preconditions: Let n = len(edges) + 1. The list edges has length n - 1, and each element is a list of length 2 [a, b] with 0 <= a < n, 0 <= b < n, and a != b. The undirected graph on vertices {0, 1, ..., n-1} whose edges are the unordered pairs {a, b} for each [a, b] in edges is a tree (connected and acyclic). The list guesses has length at least 1, and each element is a list of length 2 [u, v] with 0 <= u < n, 0 <= v < n, and u != v. For every guess [u, v] in guesses, {u, v} is an edge of the tree. The guesses are pairwise distinct as ordered pairs. The integer k satisfies 0 <= k <= len(guesses). Also n >= 2. Let edges' be obtained from edges by replacing one edge [a, b] with [b, a] (swapping the two entries of one edge). -/
theorem spec_6 (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (edges' : Slice (alloc.vec.Vec Std.I64))
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int))
    (hswap : swappedOneEdge (sliceVal edges) (sliceVal edges')) :
    ∀ r r' : Std.I64, root_count edges guesses k = ok r →
      root_count edges' guesses k = ok r' → r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (edges' : Slice (alloc.vec.Vec Std.I64))
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int))
    (hswap : swappedOneEdge (sliceVal edges) (sliceVal edges')), ∀ r r' : Std.I64, root_count edges guesses k = ok r →
      root_count edges' guesses k = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns results r1 on (edges, guesses, k1) and r2 on (edges, guesses, k2), we have r2 <= r1.
  Preconditions: Let n = len(edges) + 1. The list edges has length n - 1, and each element is a list of length 2 [a, b] with 0 <= a < n, 0 <= b < n, and a != b. The undirected graph on vertices {0, 1, ..., n-1} whose edges are the unordered pairs {a, b} for each [a, b] in edges is a tree (connected and acyclic). The list guesses has length at least 1, and each element is a list of length 2 [u, v] with 0 <= u < n, 0 <= v < n, and u != v. For every guess [u, v] in guesses, {u, v} is an edge of the tree. The guesses are pairwise distinct as ordered pairs. The integer k satisfies 0 <= k <= len(guesses). Also n >= 2. Let k1 and k2 be integers with 0 <= k1 <= k2 <= len(guesses). -/
theorem spec_7 (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k₁ k₂ : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk₁_lo : 0 ≤ k₁.val) (hk₂_hi : k₂.val ≤ ((sliceVal guesses).length : Int))
    (hk₁₂ : k₁.val ≤ k₂.val) :
    ∀ r₁ r₂ : Std.I64, root_count edges guesses k₁ = ok r₁ →
      root_count edges guesses k₂ = ok r₂ → r₂.val ≤ r₁.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k₁ k₂ : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk₁_lo : 0 ≤ k₁.val) (hk₂_hi : k₂.val ≤ ((sliceVal guesses).length : Int))
    (hk₁₂ : k₁.val ≤ k₂.val), ∀ r₁ r₂ : Std.I64, root_count edges guesses k₁ = ok r₁ →
      root_count edges guesses k₂ = ok r₂ → r₂.val ≤ r₁.val) := by
  sorry

/-- Whenever the function returns results r_k on (edges, guesses, k) and r_{k+1} on (edges, guesses, k+1), the difference r_k - r_{k+1} equals the number of roots root in {0, 1, ..., n-1} for which the number of true guesses for root is exactly k.
  Preconditions: Let n = len(edges) + 1. The list edges has length n - 1, and each element is a list of length 2 [a, b] with 0 <= a < n, 0 <= b < n, and a != b. The undirected graph on vertices {0, 1, ..., n-1} whose edges are the unordered pairs {a, b} for each [a, b] in edges is a tree (connected and acyclic). The list guesses has length at least 1, and each element is a list of length 2 [u, v] with 0 <= u < n, 0 <= v < n, and u != v. For every guess [u, v] in guesses, {u, v} is an edge of the tree. The guesses are pairwise distinct as ordered pairs. The integer k satisfies 0 <= k <= len(guesses). Also n >= 2. Let k be an integer with 0 <= k < len(guesses). -/
theorem spec_8 (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k k' : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < ((sliceVal guesses).length : Int))
    (hk' : k'.val = k.val + 1) :
    ∀ r r' : Std.I64, root_count edges guesses k = ok r →
      root_count edges guesses k' = ok r' →
      r.val - r'.val = (countRootsEq n (sliceVal edges) (sliceVal guesses) k.val : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k k' : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < ((sliceVal guesses).length : Int))
    (hk' : k'.val = k.val + 1), ∀ r r' : Std.I64, root_count edges guesses k = ok r →
      root_count edges guesses k' = ok r' →
      r.val - r'.val = (countRootsEq n (sliceVal edges) (sliceVal guesses) k.val : Int)) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, panic, or overflow).
  Preconditions: Let n = len(edges) + 1. Then 2 <= n <= 100000. The list edges has length n - 1, and each element is a list of length 2 [a, b] with 0 <= a < n, 0 <= b < n, and a != b. The undirected graph on vertices {0, 1, ..., n-1} whose edges are the unordered pairs {a, b} for each [a, b] in edges is a tree (connected and acyclic). Let m = len(guesses). Then 1 <= m <= 100000. Each element of guesses is a list of length 2 [u, v] with 0 <= u < n, 0 <= v < n, and u != v. For every guess [u, v] in guesses, {u, v} is an edge of the tree. The guesses are pairwise distinct as ordered pairs. The integer k satisfies 0 <= k <= m. -/
theorem spec_9 (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_len_hi : (sliceVal guesses).length ≤ 100000)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int)) :
    ∃ r : Std.I64, root_count edges guesses k = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (edges guesses : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (n : Nat)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_len_hi : (sliceVal guesses).length ≤ 100000)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ ((sliceVal guesses).length : Int)), ∃ r : Std.I64, root_count edges guesses k = ok r) := by
  sorry

/-- The sum_{k=0}^{m} r_k equals the sum over all roots root in {0, 1, ..., n-1} of (true_guesses(root) + 1), where true_guesses(root) is the number of guesses [u, v] in guesses such that u is the parent of v in the tree rooted at root.
  Preconditions: Let n = len(edges) + 1. The list edges has length n - 1, and each element is a list of length 2 [a, b] with 0 <= a < n, 0 <= b < n, and a != b. The undirected graph on vertices {0, 1, ..., n-1} whose edges are the unordered pairs {a, b} for each [a, b] in edges is a tree (connected and acyclic). The list guesses has length at least 1, and each element is a list of length 2 [u, v] with 0 <= u < n, 0 <= v < n, and u != v. For every guess [u, v] in guesses, {u, v} is an edge of the tree. The guesses are pairwise distinct as ordered pairs. The integer k satisfies 0 <= k <= len(guesses). Also n >= 2. Let m = len(guesses). For each k in {0, 1, ..., m}, let r_k be the result of the function on (edges, guesses, k), whenever all these calls return results. -/
theorem spec_10 (edges guesses : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (rs : Nat → Std.I64)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hcalls : ∀ j : Nat, j ≤ (sliceVal guesses).length →
      root_count edges guesses (i64OfInt (j : Int)) = ok (rs j)) :
    sumInts ((List.range ((sliceVal guesses).length + 1)).map (fun j => (rs j).val)) =
      sumInts ((List.range n).map
        (fun i : Nat => (trueGuesses (sliceVal edges) (sliceVal guesses) (i : Int) : Int) + 1)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (edges guesses : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (rs : Nat → Std.I64)
    (hn : n = (sliceVal edges).length + 1)
    (hn_lo : 2 ≤ n)
    (hedge_len : (sliceVal edges).length = n - 1)
    (hedge_shape : isPairList n (sliceVal edges))
    (hconn : connected n (sliceVal edges))
    (hacyc : acyclic (sliceVal edges))
    (hguess_len : 1 ≤ (sliceVal guesses).length)
    (hguess_shape : isPairList n (sliceVal guesses))
    (hguess_edge : ∀ g ∈ sliceVal guesses, ∃ u v : Int, g = [u, v] ∧ adj (sliceVal edges) u v)
    (hguess_nodup : (sliceVal guesses).Nodup)
    (hcalls : ∀ j : Nat, j ≤ (sliceVal guesses).length →
      root_count edges guesses (i64OfInt (j : Int)) = ok (rs j)), sumInts ((List.range ((sliceVal guesses).length + 1)).map (fun j => (rs j).val)) =
      sumInts ((List.range n).map
        (fun i : Nat => (trueGuesses (sliceVal edges) (sliceVal guesses) (i : Int) : Int) + 1))) := by
  sorry

end AegisSpec.RootCount
