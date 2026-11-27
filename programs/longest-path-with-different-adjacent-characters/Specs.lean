import Aegis.LongestPath.Code.Funs

/-!
# Specifications of `Aegis.LongestPath.longest_path`

LeetCode problem `longest-path-with-different-adjacent-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.LongestPath

namespace AegisSpec.LongestPath

def par (p : List Std.I64) (i : Nat) : Nat := ((p[i]!).val).toNat

def nthParent (p : List Std.I64) : Nat → Nat → Nat
  | 0, i => i
  | k + 1, i => nthParent p k (par p i)

def Ancestor (p : List Std.I64) (a b : Nat) : Prop :=
  ∃ k : Nat, 0 < k ∧ nthParent p k b = a

def IsRootedTree (p : List Std.I64) : Prop :=
  0 < p.length ∧
    (p[0]!).val = (-1 : Int) ∧
    (∀ i : Nat, 1 ≤ i → i < p.length →
      0 ≤ (p[i]!).val ∧ (p[i]!).val < (p.length : Int)) ∧
    (∀ i : Nat, 1 ≤ i → i < p.length → Ancestor p 0 i)

def AllLower (s : List Std.U8) : Prop :=
  ∀ i : Nat, i < s.length → 97 ≤ (s[i]!).val ∧ (s[i]!).val ≤ 122

def IsValidPath (p : List Std.I64) (s : List Std.U8) (vs : List Nat) : Prop :=
  1 ≤ vs.length ∧
    (∀ v : Nat, v ∈ vs → v < p.length) ∧
    vs.Nodup ∧
    (∀ i : Nat, i + 1 < vs.length →
      (vs[i + 1]! = par p vs[i]! ∨ vs[i]! = par p vs[i + 1]!) ∧
        (s[vs[i]!]!).val ≠ (s[vs[i + 1]!]!).val)

noncomputable def maxValidPathLen (p : List Std.I64) (s : List Std.U8) : Nat := by
  classical
  exact Nat.findGreatest
    (fun k => ∃ vs : List Nat, IsValidPath p s vs ∧ vs.length = k) p.length

def IsSimplePath (p : List Std.I64) (u v : Nat) (vs : List Nat) : Prop :=
  vs.head? = some u ∧
    vs.getLast? = some v ∧
    vs.Nodup ∧
    (∀ w : Nat, w ∈ vs → w < p.length) ∧
    (∀ i : Nat, i + 1 < vs.length →
      vs[i + 1]! = par p vs[i]! ∨ vs[i]! = par p vs[i + 1]!)

noncomputable def maxSimplePathNodes (p : List Std.I64) : Nat := by
  classical
  exact Nat.findGreatest
    (fun k => ∃ u v : Nat, u < p.length ∧ v < p.length ∧
      ∃ vs : List Nat, IsSimplePath p u v vs ∧ vs.length = k) p.length

noncomputable def maxDiffIntervalLen (s : List Std.U8) : Nat := by
  classical
  exact Nat.findGreatest
    (fun k => ∃ a b : Nat, a ≤ b ∧ b < s.length ∧ b + 1 - a = k ∧
      ∀ j : Nat, a ≤ j → j < b → (s[j]!).val ≠ (s[j + 1]!).val) s.length

def childCount (p : List Std.I64) (i : Nat) : Nat :=
  (p.drop 1).countP (fun x => x.val == (i : Int))

def degree (p : List Std.I64) (i : Nat) : Nat :=
  childCount p i + if i = 0 then 0 else 1

def DegreeAtMostTwo (p : List Std.I64) : Prop :=
  ∀ i : Nat, i < p.length → degree p i ≤ 2

def TwoNonRootDiff (s : List Std.U8) (n : Nat) : Prop :=
  ∃ i j : Nat, 1 ≤ i ∧ i < n ∧ 1 ≤ j ∧ j < n ∧ i ≠ j ∧
    (s[i]!).val ≠ (s[0]!).val ∧ (s[j]!).val ≠ (s[0]!).val

def ExistsNonRootDiff (s : List Std.U8) (n : Nat) : Prop :=
  ∃ i : Nat, 1 ≤ i ∧ i < n ∧ (s[i]!).val ≠ (s[0]!).val

def IsCharTreeIso (p : List Std.I64) (s : List Std.U8)
    (p' : List Std.I64) (s' : List Std.U8) (n : Nat) (f : Nat → Nat) : Prop :=
  (∀ i : Nat, i < n → f i < n) ∧
    (∀ i : Nat, i < n → ∀ j : Nat, j < n → f i = f j → i = j) ∧
    f 0 = 0 ∧
    (∀ i : Nat, 1 ≤ i → i < n →
      (f i = par p' (f (par p i)) ∨ par p' (f i) = f (par p i))) ∧
    (∀ i : Nat, i < n → (s[i]!).val = (s'[f i]!).val)

/-- The function returns a result r, and r is the maximum length (number of nodes) of a valid path in the tree. A valid path is a sequence of distinct nodes v_0, ..., v_{k-1} (k >= 1) such that for every i with 0 <= i < k-1, v_i and v_{i+1} are adjacent in the tree (i.e., v_i = parent[v_{i+1}] or v_{i+1} = parent[v_i]) and s[v_i] != s[v_{i+1}]. The length of such a path is k.
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_1 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val) :
    ∃ r : Std.I64, longest_path parent s = ok r ∧
      r.val = (maxValidPathLen parent.val s.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val), ∃ r : Std.I64, longest_path parent s = ok r ∧
      r.val = (maxValidPathLen parent.val s.val : Int)) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, overflow, panic, or go out of bounds).
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_2 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val) :
    ∃ r : Std.I64, longest_path parent s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val), ∃ r : Std.I64, longest_path parent s = ok r) := by
  sorry

/-- Whenever the function returns a result r, we have 1 <= r <= n.
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_3 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val) :
    ∀ r : Std.I64, longest_path parent s = ok r →
      1 ≤ r.val ∧ r.val ≤ (n : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val), ∀ r : Std.I64, longest_path parent s = ok r →
      1 ≤ r.val ∧ r.val ≤ (n : Int)) := by
  sorry

/-- For every valid path (as defined in spec_1) of length k, we have k <= r.
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_4 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val) :
    ∀ r : Std.I64, longest_path parent s = ok r →
      ∀ vs : List Nat, IsValidPath parent.val s.val vs → (vs.length : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val), ∀ r : Std.I64, longest_path parent s = ok r →
      ∀ vs : List Nat, IsValidPath parent.val s.val vs → (vs.length : Int) ≤ r.val) := by
  sorry

/-- There exist nodes u and v with 0 <= u < n and 0 <= v < n such that the unique simple path between u and v in the tree is a valid path (as defined in spec_1) and has exactly r nodes.
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_5 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val) :
    ∀ r : Std.I64, longest_path parent s = ok r →
      ∃ u v : Nat, u < n ∧ v < n ∧
        ∃ vs : List Nat, IsSimplePath parent.val u v vs ∧
          IsValidPath parent.val s.val vs ∧ (vs.length : Int) = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val), ∀ r : Std.I64, longest_path parent s = ok r →
      ∃ u v : Nat, u < n ∧ v < n ∧
        ∃ vs : List Nat, IsSimplePath parent.val u v vs ∧
          IsValidPath parent.val s.val vs ∧ (vs.length : Int) = r.val) := by
  sorry

/-- If every edge in the tree connects nodes with different characters, then the function returns r equal to the maximum number of nodes on any simple path in the tree (i.e., the tree diameter in nodes). Equivalently, r = 1 + max_{u,v in [0,n)} dist(u,v), where dist(u,v) is the number of edges on the unique simple path between u and v.
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122); and for every i with 1 <= i < n, s[i] != s[parent[i]]. -/
theorem spec_6 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (hedge : ∀ i : Nat, 1 ≤ i → i < n →
      (s[i]!).val ≠ (s[par parent.val i]!).val) :
    ∀ r : Std.I64, longest_path parent s = ok r →
      r.val = (maxSimplePathNodes parent.val : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (hedge : ∀ i : Nat, 1 ≤ i → i < n →
      (s[i]!).val ≠ (s[par parent.val i]!).val), ∀ r : Std.I64, longest_path parent s = ok r →
      r.val = (maxSimplePathNodes parent.val : Int)) := by
  sorry

/-- Whenever the function returns ok r, r is the maximum, over all pairs (a, b) with 0 <= a <= b < n and, for every k with a <= k < b, s[k] != s[k+1], of the number of nodes b - a + 1 in that interval.
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122); and for every i with 1 <= i < n, parent[i] = i-1 (so the tree is a path 0-1-2-...-(n-1)). -/
theorem spec_7 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (hpath : ∀ i : Nat, 1 ≤ i → i < n → par parent.val i = i - 1) :
    ∀ r : Std.I64, longest_path parent s = ok r →
      r.val = (maxDiffIntervalLen s.val : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (hpath : ∀ i : Nat, 1 ≤ i → i < n → par parent.val i = i - 1), ∀ r : Std.I64, longest_path parent s = ok r →
      r.val = (maxDiffIntervalLen s.val : Int)) := by
  sorry

/-- If the tree is a star with center 0, then: if there exist two distinct indices i, j with 1 <= i < n, 1 <= j < n, i != j, such that s[i] != s[0] and s[j] != s[0], then r = 3; else if there exists an index i with 1 <= i < n such that s[i] != s[0], then r = 2; else r = 1.
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122); and for every i with 1 <= i < n, parent[i] = 0 (so the tree is a star with center 0). -/
theorem spec_8 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (hstar : ∀ i : Nat, 1 ≤ i → i < n → par parent.val i = 0) :
    ∀ r : Std.I64, longest_path parent s = ok r →
      (TwoNonRootDiff s.val n → r.val = 3) ∧
        (¬ TwoNonRootDiff s.val n → ExistsNonRootDiff s.val n → r.val = 2) ∧
        (¬ ExistsNonRootDiff s.val n → r.val = 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (hstar : ∀ i : Nat, 1 ≤ i → i < n → par parent.val i = 0), ∀ r : Std.I64, longest_path parent s = ok r →
      (TwoNonRootDiff s.val n → r.val = 3) ∧
        (¬ TwoNonRootDiff s.val n → ExistsNonRootDiff s.val n → r.val = 2) ∧
        (¬ ExistsNonRootDiff s.val n → r.val = 1)) := by
  sorry

/-- The function returns r = 1 if and only if for every i with 1 <= i < n, s[i] = s[parent[i]]. Equivalently, r >= 2 if and only if there exists an index i with 1 <= i < n such that s[i] != s[parent[i]].
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_9 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val) :
    ∀ r : Std.I64, longest_path parent s = ok r →
      (r.val = 1 ↔
          ∀ i : Nat, 1 ≤ i → i < n →
            (s[i]!).val = (s[par parent.val i]!).val) ∧
        (2 ≤ r.val ↔
          ∃ i : Nat, 1 ≤ i ∧ i < n ∧
            (s[i]!).val ≠ (s[par parent.val i]!).val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val), ∀ r : Std.I64, longest_path parent s = ok r →
      (r.val = 1 ↔
          ∀ i : Nat, 1 ≤ i → i < n →
            (s[i]!).val = (s[par parent.val i]!).val) ∧
        (2 ≤ r.val ↔
          ∃ i : Nat, 1 ≤ i ∧ i < n ∧
            (s[i]!).val ≠ (s[par parent.val i]!).val)) := by
  sorry

/-- The function returns r = n if and only if the underlying undirected tree is a path (i.e., every node has degree at most 2) and for every i with 1 <= i < n, s[i] != s[parent[i]].
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_10 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val) :
    ∀ r : Std.I64, longest_path parent s = ok r →
      (r.val = (n : Int) ↔
        DegreeAtMostTwo parent.val ∧
          (∀ i : Nat, 1 ≤ i → i < n →
            (s[i]!).val ≠ (s[par parent.val i]!).val)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val), ∀ r : Std.I64, longest_path parent s = ok r →
      (r.val = (n : Int) ↔
        DegreeAtMostTwo parent.val ∧
          (∀ i : Nat, 1 ≤ i → i < n →
            (s[i]!).val ≠ (s[par parent.val i]!).val))) := by
  sorry

/-- The function returns the same result when called with (parent, s) and with (parent', s'). That is, longest_path(parent, s) = longest_path(parent', s').
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122). Let parent' be an array of length n with parent'[0] = -1 and for every i with 1 <= i < n, 0 <= parent'[i] < n, such that parent' defines a tree rooted at 0. Let s' be an array of length n with lowercase English letters. Suppose there exists a bijection f: [0,n) -> [0,n) such that f(0) = 0, for every i with 1 <= i < n the unordered pair {f(i), f(parent[i])} is an edge in the tree defined by parent' (i.e., f(i) = parent'[f(parent[i])] or f(parent[i]) = parent'[f(i)]), and s[i] = s'[f(i)] for all i. -/
theorem spec_11 (parent parent' : Slice Std.I64) (s s' : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (hpar' : parent'.val.length = n) (hs' : s'.val.length = n)
    (htree' : IsRootedTree parent'.val) (hlower' : AllLower s'.val)
    (hiso : ∃ f : Nat → Nat, IsCharTreeIso parent.val s.val parent'.val s'.val n f) :
    longest_path parent s = longest_path parent' s' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (parent parent' : Slice Std.I64) (s s' : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (hpar' : parent'.val.length = n) (hs' : s'.val.length = n)
    (htree' : IsRootedTree parent'.val) (hlower' : AllLower s'.val)
    (hiso : ∃ f : Nat → Nat, IsCharTreeIso parent.val s.val parent'.val s'.val n f), longest_path parent s = longest_path parent' s') := by
  sorry

/-- longest_path(parent', s') = longest_path(parent, s).
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122). Let parent' be an array of length n+1 such that parent'[i] = parent[i] for 0 <= i < n, and parent'[n] = j for some j with 0 <= j < n. Let s' be an array of length n+1 such that s'[i] = s[i] for 0 <= i < n, and s'[n] = s[j]. Then parent' defines a tree rooted at 0 (with n+1 nodes) and s' consists of lowercase English letters. -/
theorem spec_12 (parent parent' : Slice Std.I64) (s s' : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (j : Std.I64) (hj : 0 ≤ j.val) (hjn : j.val < (n : Int))
    (hpar' : parent'.val = parent.val ++ [j])
    (hs' : s'.val = s.val ++ [s.val[j.val.toNat]!])
    (htree' : IsRootedTree parent'.val) (hlower' : AllLower s'.val) :
    longest_path parent' s' = longest_path parent s := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (parent parent' : Slice Std.I64) (s s' : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (j : Std.I64) (hj : 0 ≤ j.val) (hjn : j.val < (n : Int))
    (hpar' : parent'.val = parent.val ++ [j])
    (hs' : s'.val = s.val ++ [s.val[j.val.toNat]!])
    (htree' : IsRootedTree parent'.val) (hlower' : AllLower s'.val), longest_path parent' s' = longest_path parent s) := by
  sorry

/-- longest_path(parent', s') is either longest_path(parent, s) or longest_path(parent, s) + 1.
  Preconditions: n = len(parent) = len(s); n >= 1; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n and following parent pointers from i eventually reaches 0 (so parent defines a tree rooted at 0); for every i with 0 <= i < n, s[i] is a lowercase English letter (97 <= s[i] <= 122). Let parent' be an array of length n+1 such that parent'[i] = parent[i] for 0 <= i < n, and parent'[n] = j for some j with 0 <= j < n. Let s' be an array of length n+1 such that s'[i] = s[i] for 0 <= i < n, and s'[n] = c where c is a lowercase English letter and c != s[j]. Then parent' defines a tree rooted at 0 (with n+1 nodes) and s' consists of lowercase English letters. -/
theorem spec_13 (parent parent' : Slice Std.I64) (s s' : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (j : Std.I64) (hj : 0 ≤ j.val) (hjn : j.val < (n : Int))
    (c : Std.U8) (hc : 97 ≤ c.val ∧ c.val ≤ 122)
    (hcne : c.val ≠ (s.val[j.val.toNat]!).val)
    (hpar' : parent'.val = parent.val ++ [j])
    (hs' : s'.val = s.val ++ [c])
    (htree' : IsRootedTree parent'.val) (hlower' : AllLower s'.val) :
    ∀ r r' : Std.I64, longest_path parent s = ok r → longest_path parent' s' = ok r' →
      r'.val = r.val ∨ r'.val = r.val + 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (parent parent' : Slice Std.I64) (s s' : Slice Std.U8) (n : Nat)
    (hpar : parent.val.length = n) (hs : s.val.length = n) (hn : 1 ≤ n)
    (htree : IsRootedTree parent.val) (hlower : AllLower s.val)
    (j : Std.I64) (hj : 0 ≤ j.val) (hjn : j.val < (n : Int))
    (c : Std.U8) (hc : 97 ≤ c.val ∧ c.val ≤ 122)
    (hcne : c.val ≠ (s.val[j.val.toNat]!).val)
    (hpar' : parent'.val = parent.val ++ [j])
    (hs' : s'.val = s.val ++ [c])
    (htree' : IsRootedTree parent'.val) (hlower' : AllLower s'.val), ∀ r r' : Std.I64, longest_path parent s = ok r → longest_path parent' s' = ok r' →
      r'.val = r.val ∨ r'.val = r.val + 1) := by
  sorry

end AegisSpec.LongestPath
