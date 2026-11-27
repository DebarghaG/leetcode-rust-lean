import Aegis.FindAnswer.Code.Funs

/-!
# Specifications of `Aegis.FindAnswer.find_answer`

LeetCode problem `check-if-dfs-strings-are-palindromes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindAnswer

def byteChars (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

def byteAt (s : Slice Std.U8) (i : Nat) : Nat := (s.val.getD i (0#u8)).val

def parentStep (parent : List Int) (i : Nat) : Nat :=
  if i = 0 then 0 else (parent.getD i (0#i64)).toNat

def ancestor (parent : List Int) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => ancestor parent k (parentStep parent x)

def childrenOf (parent : List Int) (n x : Nat) : List Nat :=
  (List.range n).filter (fun y => decide (parent.getD y (0#i64) = (x : Int)))

def subtreePost (parent : List Int) (n : Nat) (chars : List Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, x =>
      (childrenOf parent n x).flatMap (fun y => subtreePost parent n chars fuel y) ++
        [chars.getD x 0]

def firstCharNode (parent : List Int) (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
      match childrenOf parent n x with
      | [] => x
      | c :: _ => firstCharNode parent n fuel c

def D (parent : Slice Std.I64) (s : Slice Std.U8) (n x : Nat) : List Nat :=
  subtreePost parent.val n (byteChars s) n x

def F (parent : Slice Std.I64) (n x : Nat) : Nat := firstCharNode parent.val n n x

def IsPalindrome (l : List Nat) : Prop :=
  ∀ k, k < l.length → l.getD k 0 = l.getD (l.length - 1 - k) 0

def NotPalindromeWitness (l : List Nat) : Prop :=
  ∃ k, k < l.length / 2 ∧ l.getD k 0 ≠ l.getD (l.length - 1 - k) 0

def countOcc (a : Nat) (l : List Nat) : Nat := l.countP (fun b => b = a)

def AtMostOneOdd (l : List Nat) : Prop :=
  ∀ a b, countOcc a l % 2 = 1 → countOcc b l % 2 = 1 → a = b

def InSubtree (parent : List Int) (x i : Nat) : Prop := ∃ k, ancestor parent k x = i

def ReachesRoot (parent : List Int) (n : Nat) : Prop :=
  ∀ i, i < n → ∃ k, ancestor parent k i = 0

def Acyclic (parent : List Int) (n : Nat) : Prop :=
  ∀ i, i < n → i ≠ 0 → ∀ k, 0 < k → ancestor parent k i ≠ i

structure ValidInput (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat) : Prop where

  len_parent : parent.val.length = n

  len_s : s.val.length = n

  n_pos : 1 ≤ n

  n_le : n ≤ 100000

  root_parent : (parent.val.getD 0 (0#i64)).val = -1

  parent_range : ∀ i, 1 ≤ i → i < n →
    0 ≤ (parent.val.getD i (0#i64)).val ∧ (parent.val.getD i (0#i64)).val < (n : Int)

  acyclic : Acyclic parent.val n

  reaches_root : ReachesRoot parent.val n

  chars_range : ∀ i, i < n → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122

/-- The function returns a result r and len(r) = n. For each x with 0 <= x < n, let children(x) = { y | 0 <= y < n and parent[y] = x }, and let D(x) be the byte string obtained by concatenating D(y) for all y in children(x) in increasing numerical order and then appending the one-byte string s[x]. Then for every i with 0 <= i < n, r[i] = true if and only if D(i) is a palindrome, meaning that for every k with 0 <= k < len(D(i)), D(i)[k] = D(i)[len(D(i)) - 1 - k].
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_1 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) :
    ∃ r : alloc.vec.Vec Bool,
      Aegis.FindAnswer.find_answer parent s = ok r ∧
      r.val.length = n ∧
      ∀ i, i < n →
        (r.val.getD i false = true ↔
          IsPalindrome (D parent s n i)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n), ∃ r : alloc.vec.Vec Bool,
      Aegis.FindAnswer.find_answer parent s = ok r ∧
      r.val.length = n ∧
      ∀ i, i < n →
        (r.val.getD i false = true ↔
          IsPalindrome (D parent s n i))) := by
  sorry

/-- Whenever the function returns a result r, len(r) = n = len(parent) = len(s).
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_2 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r) :
    r.val.length = n ∧ n = parent.val.length ∧ n = s.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r), r.val.length = n ∧ n = parent.val.length ∧ n = s.val.length) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (an ok value); it does not fail.
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_3 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) :
    ∃ r : alloc.vec.Vec Bool, Aegis.FindAnswer.find_answer parent s = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n), ∃ r : alloc.vec.Vec Bool, Aegis.FindAnswer.find_answer parent s = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if there is no j with 0 <= j < n and parent[j] = i, then r[i] = true.
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_4 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r) :
    ∀ i, i < n →
      (∀ j, j < n → (parent.val.getD j (0#i64)).val ≠ (i : Int)) →
      r.val.getD i false = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r), ∀ i, i < n →
      (∀ j, j < n → (parent.val.getD j (0#i64)).val ≠ (i : Int)) →
      r.val.getD i false = true) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if every node x in the subtree rooted at i (the set of nodes whose repeated parent steps reach i, including i itself) has the same character s[x], then r[i] = true.
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_5 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r) :
    ∀ i, i < n →
      (∀ x, x < n → InSubtree parent.val x i →
        ∀ y, y < n → InSubtree parent.val y i → byteAt s x = byteAt s y) →
      r.val.getD i false = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r), ∀ i, i < n →
      (∀ x, x < n → InSubtree parent.val x i →
        ∀ y, y < n → InSubtree parent.val y i → byteAt s x = byteAt s y) →
      r.val.getD i false = true) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] = true then the first character of D(i) equals the last character of D(i). The last character of D(i) is s[i]. The first character is s[f(i)], where f(i) is defined recursively by f(i)=i if i has no children, and by f(i)=f(c) for the smallest child c of i otherwise. Thus r[i] = true implies s[f(i)] = s[i].
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_6 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r) :
    ∀ i, i < n → r.val.getD i false = true →
      byteAt s (F parent n i) = byteAt s i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r), ∀ i, i < n → r.val.getD i false = true →
      byteAt s (F parent n i) = byteAt s i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] = false then there exists an integer k with 0 <= k < len(D(i)) / 2 such that D(i)[k] != D(i)[len(D(i)) - 1 - k], where D(i) is the postorder DFS string of the subtree rooted at i (children taken in increasing order, character s[x] appended after all children).
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_7 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r) :
    ∀ i, i < n → r.val.getD i false = false →
      NotPalindromeWitness (D parent s n i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r), ∀ i, i < n → r.val.getD i false = false →
      NotPalindromeWitness (D parent s n i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if i has exactly one child c and c has no children, then r[i] = true if and only if s[i] = s[c].
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_8 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r) :
    ∀ i, i < n → ∀ c,
      childrenOf parent.val n i = [c] → childrenOf parent.val n c = [] →
      (r.val.getD i false = true ↔ byteAt s i = byteAt s c) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r), ∀ i, i < n → ∀ c,
      childrenOf parent.val n i = [c] → childrenOf parent.val n c = [] →
      (r.val.getD i false = true ↔ byteAt s i = byteAt s c)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if i has exactly two children c1 and c2 with c1 < c2, and both c1 and c2 have no children, then r[i] = true if and only if s[c1] = s[i].
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_9 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r) :
    ∀ i, i < n → ∀ c1 c2, c1 < c2 →
      childrenOf parent.val n i = [c1, c2] →
      childrenOf parent.val n c1 = [] → childrenOf parent.val n c2 = [] →
      (r.val.getD i false = true ↔ byteAt s c1 = byteAt s i) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r), ∀ i, i < n → ∀ c1 c2, c1 < c2 →
      childrenOf parent.val n i = [c1, c2] →
      childrenOf parent.val n c1 = [] → childrenOf parent.val n c2 = [] →
      (r.val.getD i false = true ↔ byteAt s c1 = byteAt s i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if i has exactly one child c, c has exactly one child d, and d has no children, then r[i] = true if and only if s[i] = s[d].
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_10 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r) :
    ∀ i, i < n → ∀ c,
      childrenOf parent.val n i = [c] → ∀ d,
      childrenOf parent.val n c = [d] → childrenOf parent.val n d = [] →
      (r.val.getD i false = true ↔ byteAt s i = byteAt s d) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r), ∀ i, i < n → ∀ c,
      childrenOf parent.val n i = [c] → ∀ d,
      childrenOf parent.val n c = [d] → childrenOf parent.val n d = [] →
      (r.val.getD i false = true ↔ byteAt s i = byteAt s d)) := by
  sorry

/-- Whenever the function returns a result r, if n = 1 then len(r) = 1 and r[0] = true.
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_11 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r) :
    n = 1 → r.val.length = 1 ∧ r.val.getD 0 false = true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r), n = 1 → r.val.length = 1 ∧ r.val.getD 0 false = true) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] = true then among the characters of D(i) at most one character occurs an odd number of times. Here D(i) is the postorder DFS string of the subtree rooted at i.
  Preconditions: n = len(parent) = len(s); 1 <= n <= 100000; parent[0] = -1; for every i with 1 <= i < n, 0 <= parent[i] < n; parent represents a valid tree rooted at node 0 (the directed graph with edges parent[i] -> i for 1 <= i < n has no cycles and every node reaches 0 by repeatedly following parent); for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_12 (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r) :
    ∀ i, i < n → r.val.getD i false = true →
      AtMostOneOdd (D parent s n i) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8) (n : Nat)
    (hpre : ValidInput parent s n) (r : alloc.vec.Vec Bool)
    (hres : Aegis.FindAnswer.find_answer parent s = ok r), ∀ i, i < n → r.val.getD i false = true →
      AtMostOneOdd (D parent s n i)) := by
  sorry

  end AegisSpec.FindAnswer
