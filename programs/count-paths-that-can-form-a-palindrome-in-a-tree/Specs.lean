import Aegis.CountPalindromePaths.Code.Funs

/-!
# Specifications of `Aegis.CountPalindromePaths.count_palindrome_paths`

LeetCode problem `count-paths-that-can-form-a-palindrome-in-a-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountPalindromePaths

  namespace AegisSpec.CountPalindromePaths

  def parAt (parent : List Std.I64) (i : Nat) : Int :=
    ((parent[i]?).map (fun x => x.val)).getD (-1)

  def byteAt (s : List Std.U8) (i : Nat) : Nat :=
    ((s[i]?).map (fun x => x.val)).getD 0

  def AllLower (s : List Std.U8) : Prop :=
    ∀ i, i < s.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122

  def IsLowerLetter (c : Nat) : Prop := 97 ≤ c ∧ c ≤ 122

  def parStep (parent : List Std.I64) (i : Nat) : Option Nat :=
    if h : i < parent.length then
      (let p := (parent.get ⟨i, h⟩).val
       if 0 ≤ p ∧ p < (parent.length : Int) then some p.toNat else none)
    else none

  def parChainAux (parent : List Std.I64) : Nat → Nat → List Nat
    | 0, _ => []
    | k + 1, i =>
      match parStep parent i with
      | none => []
      | some p => i :: parChainAux parent k p

  def rootChain (parent : List Std.I64) (u : Nat) : List Nat :=
    parChainAux parent parent.length u

  def parIter (parent : List Std.I64) : Nat → Nat → Option Nat
    | 0, i => some i
    | k + 1, i => (parIter parent k i).bind (parStep parent)

  def ReachesRoot (parent : List Std.I64) (i : Nat) : Prop := ∃ k, parIter parent k i = some 0

  def InSubtree (parent : List Std.I64) (i w : Nat) : Prop := i ∈ rootChain parent w

  instance decInSubtree (parent : List Std.I64) (i w : Nat) : Decidable (InSubtree parent i w) :=
    inferInstanceAs (Decidable (i ∈ rootChain parent w))

  def IsTree (parent : List Std.I64) : Prop :=
    ∀ i, i < parent.length → ReachesRoot parent i

  def pathEdges (parent : List Std.I64) (u v : Nat) : List Nat :=
    (List.range parent.length).filter (fun i =>
      decide (1 ≤ i) && (decide (InSubtree parent i u) != decide (InSubtree parent i v)))

  def pathLabels (parent : List Std.I64) (s : List Std.U8) (u v : Nat) : List Nat :=
    (pathEdges parent u v).map (fun i => byteAt s i)

  def letterCount (ls : List Nat) (c : Nat) : Nat := ls.countP (fun x => x == c)

  def oddLetterCount (ls : List Nat) : Nat :=
    ((List.range 26).filter (fun k => (letterCount ls (97 + k)) % 2 == 1)).length

  def PalindromePath (parent : List Std.I64) (s : List Std.U8) (u v : Nat) : Prop :=
    oddLetterCount (pathLabels parent s u v) ≤ 1

  instance decPalindromePath (parent : List Std.I64) (s : List Std.U8) (u v : Nat) :
      Decidable (PalindromePath parent s u v) :=
    inferInstanceAs (Decidable (oddLetterCount (pathLabels parent s u v) ≤ 1))

  def palindromePairCount (parent : List Std.I64) (s : List Std.U8) : Nat :=
    ((List.range parent.length).product (List.range parent.length)).countP
      (fun p => decide (p.1 < p.2 ∧ PalindromePath parent s p.1 p.2))

  def letterCountFromOne (s : List Std.U8) (c : Nat) : Nat :=
    ((List.range s.length).filter (fun i => decide (1 ≤ i) && (byteAt s i == c))).length

  def starPairCount (s : List Std.U8) : Nat :=
    (s.length - 1) +
      ((List.range 26).map (fun k =>
        (let m := letterCountFromOne s (97 + k); m * (m - 1) / 2))).sum

  def segmentLabels (s : List Std.U8) (a b : Nat) : List Nat :=
    (List.range (b + 1 - a)).map (fun k => byteAt s (a + k + 1))

  def chainPalindromePairCount (s : List Std.U8) : Nat :=
    (((List.range (s.length - 1)).product (List.range (s.length - 1))).countP
      (fun p => decide (p.1 ≤ p.2 ∧ oddLetterCount (segmentLabels s p.1 p.2) ≤ 1)))

  /-- For every pair of nodes u and v, let P(u,v) be the unique simple path between them in this tree, regarded as a set of undirected edges; for i with 1 <= i < n, the edge {i, parent[i]} has label s[i] (s[0] is not used). For a letter c, let odd_c(u,v) be the number of edges e of P(u,v) whose label is c, taken modulo 2. The function returns a result r and r is exactly the number of pairs (u,v) such that 0 <= u < v < n and at most one letter c in 'a'..'z' has odd_c(u,v) = 1 (equivalently, the edge labels on P(u,v) can be rearranged to form a palindrome).
    Preconditions: Let n = len(parent). The arrays satisfy len(parent) = len(s) = n, 1 <= n <= 100000, parent[0] = -1, and for every i with 1 <= i < n, 0 <= parent[i] < n. The undirected graph on {0,...,n-1} with an edge between i and parent[i] for each i with 1 <= i < n is a tree rooted at 0 (connected and acyclic). For every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_1 (parent : Slice Std.I64) (s : Slice Std.U8)
      (hlen : parent.val.length = s.val.length)
      (hn_pos : 1 ≤ parent.val.length)
      (hn_le : parent.val.length ≤ 100000)
      (hroot : parAt parent.val 0 = -1)
      (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
        0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
      (htree : IsTree parent.val)
      (hlower : AllLower s.val) :
      ∃ r : Std.I64,
        count_palindrome_paths parent s = ok r ∧
          r.val = (palindromePairCount parent.val s.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8)
        (hlen : parent.val.length = s.val.length)
        (hn_pos : 1 ≤ parent.val.length)
        (hn_le : parent.val.length ≤ 100000)
        (hroot : parAt parent.val 0 = -1)
        (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
          0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
        (htree : IsTree parent.val)
        (hlower : AllLower s.val), ∃ r : Std.I64,
          count_palindrome_paths parent s = ok r ∧
            r.val = (palindromePairCount parent.val s.val : Int)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
    Preconditions: Let n = len(parent). The arrays satisfy len(parent) = len(s) = n, 1 <= n <= 100000, parent[0] = -1, and for every i with 1 <= i < n, 0 <= parent[i] < n. The undirected graph on {0,...,n-1} with an edge between i and parent[i] for each i with 1 <= i < n is a tree rooted at 0 (connected and acyclic). For every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_2 (parent : Slice Std.I64) (s : Slice Std.U8)
      (hlen : parent.val.length = s.val.length)
      (hn_pos : 1 ≤ parent.val.length)
      (hn_le : parent.val.length ≤ 100000)
      (hroot : parAt parent.val 0 = -1)
      (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
        0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
      (htree : IsTree parent.val)
      (hlower : AllLower s.val) :
      ∃ r : Std.I64, count_palindrome_paths parent s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8)
        (hlen : parent.val.length = s.val.length)
        (hn_pos : 1 ≤ parent.val.length)
        (hn_le : parent.val.length ≤ 100000)
        (hroot : parAt parent.val 0 = -1)
        (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
          0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
        (htree : IsTree parent.val)
        (hlower : AllLower s.val), ∃ r : Std.I64, count_palindrome_paths parent s = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= n*(n-1)/2.
    Preconditions: Let n = len(parent). The arrays satisfy len(parent) = len(s) = n, 1 <= n <= 100000, parent[0] = -1, and for every i with 1 <= i < n, 0 <= parent[i] < n. The undirected graph on {0,...,n-1} with an edge between i and parent[i] for each i with 1 <= i < n is a tree rooted at 0 (connected and acyclic). For every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_3 (parent : Slice Std.I64) (s : Slice Std.U8)
      (hlen : parent.val.length = s.val.length)
      (hn_pos : 1 ≤ parent.val.length)
      (hn_le : parent.val.length ≤ 100000)
      (hroot : parAt parent.val 0 = -1)
      (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
        0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
      (htree : IsTree parent.val)
      (hlower : AllLower s.val) :
      ∃ r : Std.I64,
        count_palindrome_paths parent s = ok r ∧
          0 ≤ r.val ∧
            r.val ≤ ((parent.val.length : Int) * ((parent.val.length : Int) - 1)) / 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8)
        (hlen : parent.val.length = s.val.length)
        (hn_pos : 1 ≤ parent.val.length)
        (hn_le : parent.val.length ≤ 100000)
        (hroot : parAt parent.val 0 = -1)
        (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
          0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
        (htree : IsTree parent.val)
        (hlower : AllLower s.val), ∃ r : Std.I64,
          count_palindrome_paths parent s = ok r ∧
            0 ≤ r.val ∧
              r.val ≤ ((parent.val.length : Int) * ((parent.val.length : Int) - 1)) / 2) := by
    sorry

  /-- The function returns a result r and r >= n - 1.
    Preconditions: Let n = len(parent). The arrays satisfy len(parent) = len(s) = n, 1 <= n <= 100000, parent[0] = -1, and for every i with 1 <= i < n, 0 <= parent[i] < n. The undirected graph on {0,...,n-1} with an edge between i and parent[i] for each i with 1 <= i < n is a tree rooted at 0 (connected and acyclic). For every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_4 (parent : Slice Std.I64) (s : Slice Std.U8)
      (hlen : parent.val.length = s.val.length)
      (hn_pos : 1 ≤ parent.val.length)
      (hn_le : parent.val.length ≤ 100000)
      (hroot : parAt parent.val 0 = -1)
      (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
        0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
      (htree : IsTree parent.val)
      (hlower : AllLower s.val) :
      ∃ r : Std.I64,
        count_palindrome_paths parent s = ok r ∧
          (parent.val.length : Int) - 1 ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8)
        (hlen : parent.val.length = s.val.length)
        (hn_pos : 1 ≤ parent.val.length)
        (hn_le : parent.val.length ≤ 100000)
        (hroot : parAt parent.val 0 = -1)
        (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
          0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
        (htree : IsTree parent.val)
        (hlower : AllLower s.val), ∃ r : Std.I64,
          count_palindrome_paths parent s = ok r ∧
            (parent.val.length : Int) - 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = n*(n-1)/2.
    Preconditions: Let n = len(parent). The arrays satisfy len(parent) = len(s) = n, 1 <= n <= 100000, parent[0] = -1, and for every i with 1 <= i < n, 0 <= parent[i] < n. The undirected graph on {0,...,n-1} with an edge between i and parent[i] for each i with 1 <= i < n is a tree rooted at 0 (connected and acyclic). For every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). There exists a letter c with 'a' <= c <= 'z' such that s[i] = c for every i with 1 <= i < n. -/
  theorem spec_5 (parent : Slice Std.I64) (s : Slice Std.U8)
      (hlen : parent.val.length = s.val.length)
      (hn_pos : 1 ≤ parent.val.length)
      (hn_le : parent.val.length ≤ 100000)
      (hroot : parAt parent.val 0 = -1)
      (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
        0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
      (htree : IsTree parent.val)
      (hlower : AllLower s.val)
      (hconst : ∃ c : Nat, IsLowerLetter c ∧
        ∀ i, 1 ≤ i → i < parent.val.length → byteAt s.val i = c) :
      ∃ r : Std.I64,
        count_palindrome_paths parent s = ok r ∧
          r.val = ((parent.val.length : Int) * ((parent.val.length : Int) - 1)) / 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8)
        (hlen : parent.val.length = s.val.length)
        (hn_pos : 1 ≤ parent.val.length)
        (hn_le : parent.val.length ≤ 100000)
        (hroot : parAt parent.val 0 = -1)
        (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
          0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
        (htree : IsTree parent.val)
        (hlower : AllLower s.val)
        (hconst : ∃ c : Nat, IsLowerLetter c ∧
          ∀ i, 1 ≤ i → i < parent.val.length → byteAt s.val i = c), ∃ r : Std.I64,
          count_palindrome_paths parent s = ok r ∧
            r.val = ((parent.val.length : Int) * ((parent.val.length : Int) - 1)) / 2) := by
    sorry

  /-- The function returns a result r and r = n - 1.
    Preconditions: Let n = len(parent). The arrays satisfy len(parent) = len(s) = n, 1 <= n <= 100000, parent[0] = -1, and for every i with 1 <= i < n, 0 <= parent[i] < n. The undirected graph on {0,...,n-1} with an edge between i and parent[i] for each i with 1 <= i < n is a tree rooted at 0 (connected and acyclic). For every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). For every i and j with 1 <= i < j < n, s[i] != s[j]. -/
  theorem spec_6 (parent : Slice Std.I64) (s : Slice Std.U8)
      (hlen : parent.val.length = s.val.length)
      (hn_pos : 1 ≤ parent.val.length)
      (hn_le : parent.val.length ≤ 100000)
      (hroot : parAt parent.val 0 = -1)
      (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
        0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
      (htree : IsTree parent.val)
      (hlower : AllLower s.val)
      (hdistinct : ∀ i j, 1 ≤ i → i < j → j < parent.val.length →
        byteAt s.val i ≠ byteAt s.val j) :
      ∃ r : Std.I64,
        count_palindrome_paths parent s = ok r ∧
          r.val = (parent.val.length : Int) - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8)
        (hlen : parent.val.length = s.val.length)
        (hn_pos : 1 ≤ parent.val.length)
        (hn_le : parent.val.length ≤ 100000)
        (hroot : parAt parent.val 0 = -1)
        (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
          0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
        (htree : IsTree parent.val)
        (hlower : AllLower s.val)
        (hdistinct : ∀ i j, 1 ≤ i → i < j → j < parent.val.length →
          byteAt s.val i ≠ byteAt s.val j), ∃ r : Std.I64,
          count_palindrome_paths parent s = ok r ∧
            r.val = (parent.val.length : Int) - 1) := by
    sorry

  /-- Let m_c be the number of indices i with 1 <= i < n and s[i] = c, for each lowercase letter c. The function returns a result r and r = (n - 1) + sum_{c='a'..'z'} (m_c * (m_c - 1)) / 2.
    Preconditions: Let n = len(parent). The arrays satisfy len(parent) = len(s) = n, 1 <= n <= 100000, parent[0] = -1, and for every i with 1 <= i < n, 0 <= parent[i] < n. The undirected graph on {0,...,n-1} with an edge between i and parent[i] for each i with 1 <= i < n is a tree rooted at 0 (connected and acyclic). For every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). For every i with 1 <= i < n, parent[i] = 0. -/
  theorem spec_7 (parent : Slice Std.I64) (s : Slice Std.U8)
      (hlen : parent.val.length = s.val.length)
      (hn_pos : 1 ≤ parent.val.length)
      (hn_le : parent.val.length ≤ 100000)
      (hroot : parAt parent.val 0 = -1)
      (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
        0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
      (htree : IsTree parent.val)
      (hlower : AllLower s.val)
      (hstar : ∀ i, 1 ≤ i → i < parent.val.length → parAt parent.val i = 0) :
      ∃ r : Std.I64,
        count_palindrome_paths parent s = ok r ∧
          r.val = (starPairCount s.val : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8)
        (hlen : parent.val.length = s.val.length)
        (hn_pos : 1 ≤ parent.val.length)
        (hn_le : parent.val.length ≤ 100000)
        (hroot : parAt parent.val 0 = -1)
        (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
          0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
        (htree : IsTree parent.val)
        (hlower : AllLower s.val)
        (hstar : ∀ i, 1 ≤ i → i < parent.val.length → parAt parent.val i = 0), ∃ r : Std.I64,
          count_palindrome_paths parent s = ok r ∧
            r.val = (starPairCount s.val : Int)) := by
    sorry

  /-- Define t as the sequence of length n-1 with t[j] = s[j+1] for 0 <= j < n-1. The function returns a result r and r equals the number of pairs (a,b) such that 0 <= a <= b < n-1 and the contiguous substring t[a],...,t[b] can be rearranged to form a palindrome (equivalently, at most one letter occurs an odd number of times in that substring).
    Preconditions: Let n = len(parent). The arrays satisfy len(parent) = len(s) = n, 1 <= n <= 100000, parent[0] = -1, and for every i with 1 <= i < n, 0 <= parent[i] < n. The undirected graph on {0,...,n-1} with an edge between i and parent[i] for each i with 1 <= i < n is a tree rooted at 0 (connected and acyclic). For every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). For every i with 1 <= i < n, parent[i] = i - 1. -/
  theorem spec_8 (parent : Slice Std.I64) (s : Slice Std.U8)
      (hlen : parent.val.length = s.val.length)
      (hn_pos : 1 ≤ parent.val.length)
      (hn_le : parent.val.length ≤ 100000)
      (hroot : parAt parent.val 0 = -1)
      (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
        0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
      (htree : IsTree parent.val)
      (hlower : AllLower s.val)
      (hchain : ∀ i, 1 ≤ i → i < parent.val.length → parAt parent.val i = (i : Int) - 1) :
      ∃ r : Std.I64,
        count_palindrome_paths parent s = ok r ∧
          r.val = (chainPalindromePairCount s.val : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8)
        (hlen : parent.val.length = s.val.length)
        (hn_pos : 1 ≤ parent.val.length)
        (hn_le : parent.val.length ≤ 100000)
        (hroot : parAt parent.val 0 = -1)
        (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
          0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
        (htree : IsTree parent.val)
        (hlower : AllLower s.val)
        (hchain : ∀ i, 1 ≤ i → i < parent.val.length → parAt parent.val i = (i : Int) - 1), ∃ r : Std.I64,
          count_palindrome_paths parent s = ok r ∧
            r.val = (chainPalindromePairCount s.val : Int)) := by
    sorry

  /-- The function returns results r and r' for (parent,s) and (parent,s') respectively, and r = r'.
    Preconditions: Let n = len(parent). The arrays satisfy len(parent) = len(s) = n, 1 <= n <= 100000, parent[0] = -1, and for every i with 1 <= i < n, 0 <= parent[i] < n. The undirected graph on {0,...,n-1} with an edge between i and parent[i] for each i with 1 <= i < n is a tree rooted at 0 (connected and acyclic). For every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). Let pi be a bijection from the 26 lowercase ASCII letters to themselves. Let s' be a byte array of length n such that s'[i] = pi(s[i]) for every i with 1 <= i < n, s'[0] is any lowercase ASCII letter, and s'[i] is lowercase for all i. -/
  theorem spec_9 (parent : Slice Std.I64) (s s' : Slice Std.U8)
      (hlen : parent.val.length = s.val.length)
      (hn_pos : 1 ≤ parent.val.length)
      (hn_le : parent.val.length ≤ 100000)
      (hroot : parAt parent.val 0 = -1)
      (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
        0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
      (htree : IsTree parent.val)
      (hlower : AllLower s.val)
      (hlen' : s'.val.length = parent.val.length)
      (hlower' : AllLower s'.val)
      (pi : Nat → Nat)
      (hpi_maps : ∀ c, IsLowerLetter c → IsLowerLetter (pi c))
      (hpi_inj : ∀ c₁ c₂, IsLowerLetter c₁ → IsLowerLetter c₂ → pi c₁ = pi c₂ → c₁ = c₂)
      (hpi_agree : ∀ i, 1 ≤ i → i < parent.val.length → byteAt s'.val i = pi (byteAt s.val i)) :
      ∃ r r' : Std.I64,
        count_palindrome_paths parent s = ok r ∧
          count_palindrome_paths parent s' = ok r' ∧
            r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (parent : Slice Std.I64) (s s' : Slice Std.U8)
        (hlen : parent.val.length = s.val.length)
        (hn_pos : 1 ≤ parent.val.length)
        (hn_le : parent.val.length ≤ 100000)
        (hroot : parAt parent.val 0 = -1)
        (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
          0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
        (htree : IsTree parent.val)
        (hlower : AllLower s.val)
        (hlen' : s'.val.length = parent.val.length)
        (hlower' : AllLower s'.val)
        (pi : Nat → Nat)
        (hpi_maps : ∀ c, IsLowerLetter c → IsLowerLetter (pi c))
        (hpi_inj : ∀ c₁ c₂, IsLowerLetter c₁ → IsLowerLetter c₂ → pi c₁ = pi c₂ → c₁ = c₂)
        (hpi_agree : ∀ i, 1 ≤ i → i < parent.val.length → byteAt s'.val i = pi (byteAt s.val i)), ∃ r r' : Std.I64,
          count_palindrome_paths parent s = ok r ∧
            count_palindrome_paths parent s' = ok r' ∧
              r.val = r'.val) := by
    sorry

  /-- The function returns results r and r' for (parent,s) and (parent',s') respectively, and r = r'.
    Preconditions: Let n = len(parent) = len(parent'). Both (parent,s) and (parent',s') satisfy: len(parent) = len(s) = len(parent') = len(s') = n, 1 <= n <= 100000, parent[0] = parent'[0] = -1, for every i with 1 <= i < n, 0 <= parent[i] < n and 0 <= parent'[i] < n, each directed parent relation forms a tree rooted at 0, and all bytes of s and s' are lowercase ASCII letters. There is a bijection phi from {0,...,n-1} to itself with phi(0)=0 such that for every i with 1 <= i < n, parent'[phi(i)] = phi(parent[i]) and s'[phi(i)] = s[i]; s'[0] is arbitrary lowercase. -/
  theorem spec_10 (parent parent' : Slice Std.I64) (s s' : Slice Std.U8)
      (hlen : parent.val.length = s.val.length)
      (hlen' : parent'.val.length = s'.val.length)
      (hlen_eq : parent.val.length = parent'.val.length)
      (hn_pos : 1 ≤ parent.val.length)
      (hn_le : parent.val.length ≤ 100000)
      (hroot : parAt parent.val 0 = -1)
      (hroot' : parAt parent'.val 0 = -1)
      (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
        0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
      (hpar' : ∀ i, 1 ≤ i → i < parent'.val.length →
        0 ≤ parAt parent'.val i ∧ parAt parent'.val i < (parent'.val.length : Int))
      (htree : IsTree parent.val)
      (htree' : IsTree parent'.val)
      (hlower : AllLower s.val)
      (hlower' : AllLower s'.val)
      (phi : Nat → Nat)
      (hphi_zero : phi 0 = 0)
      (hphi_maps : ∀ i, i < parent.val.length → phi i < parent.val.length)
      (hphi_inj : ∀ i j, i < parent.val.length → j < parent.val.length →
        phi i = phi j → i = j)
      (hphi_parent : ∀ i, 1 ≤ i → i < parent.val.length →
        parAt parent'.val (phi i) = ((phi (parAt parent.val i).toNat : Nat) : Int))
      (hphi_label : ∀ i, 1 ≤ i → i < parent.val.length →
        byteAt s'.val (phi i) = byteAt s.val i) :
      ∃ r r' : Std.I64,
        count_palindrome_paths parent s = ok r ∧
          count_palindrome_paths parent' s' = ok r' ∧
            r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (parent parent' : Slice Std.I64) (s s' : Slice Std.U8)
        (hlen : parent.val.length = s.val.length)
        (hlen' : parent'.val.length = s'.val.length)
        (hlen_eq : parent.val.length = parent'.val.length)
        (hn_pos : 1 ≤ parent.val.length)
        (hn_le : parent.val.length ≤ 100000)
        (hroot : parAt parent.val 0 = -1)
        (hroot' : parAt parent'.val 0 = -1)
        (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
          0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
        (hpar' : ∀ i, 1 ≤ i → i < parent'.val.length →
          0 ≤ parAt parent'.val i ∧ parAt parent'.val i < (parent'.val.length : Int))
        (htree : IsTree parent.val)
        (htree' : IsTree parent'.val)
        (hlower : AllLower s.val)
        (hlower' : AllLower s'.val)
        (phi : Nat → Nat)
        (hphi_zero : phi 0 = 0)
        (hphi_maps : ∀ i, i < parent.val.length → phi i < parent.val.length)
        (hphi_inj : ∀ i j, i < parent.val.length → j < parent.val.length →
          phi i = phi j → i = j)
        (hphi_parent : ∀ i, 1 ≤ i → i < parent.val.length →
          parAt parent'.val (phi i) = ((phi (parAt parent.val i).toNat : Nat) : Int))
        (hphi_label : ∀ i, 1 ≤ i → i < parent.val.length →
          byteAt s'.val (phi i) = byteAt s.val i), ∃ r r' : Std.I64,
          count_palindrome_paths parent s = ok r ∧
            count_palindrome_paths parent' s' = ok r' ∧
              r.val = r'.val) := by
    sorry

  /-- The function returns a result r and r = 2 + (1 if s[1] = s[2] else 0).
    Preconditions: Let n = len(parent). The arrays satisfy len(parent) = len(s) = n, 1 <= n <= 100000, parent[0] = -1, and for every i with 1 <= i < n, 0 <= parent[i] < n. The undirected graph on {0,...,n-1} with an edge between i and parent[i] for each i with 1 <= i < n is a tree rooted at 0 (connected and acyclic). For every i with 0 <= i < n, s[i] is an ASCII lowercase letter (97 <= s[i] <= 122). n = 3. -/
  theorem spec_11 (parent : Slice Std.I64) (s : Slice Std.U8)
      (hlen : parent.val.length = s.val.length)
      (hn_pos : 1 ≤ parent.val.length)
      (hn_le : parent.val.length ≤ 100000)
      (hroot : parAt parent.val 0 = -1)
      (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
        0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
      (htree : IsTree parent.val)
      (hlower : AllLower s.val)
      (hn3 : parent.val.length = 3) :
      ∃ r : Std.I64,
        count_palindrome_paths parent s = ok r ∧
          r.val = (2 : Int) + (if byteAt s.val 1 = byteAt s.val 2 then 1 else 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (parent : Slice Std.I64) (s : Slice Std.U8)
        (hlen : parent.val.length = s.val.length)
        (hn_pos : 1 ≤ parent.val.length)
        (hn_le : parent.val.length ≤ 100000)
        (hroot : parAt parent.val 0 = -1)
        (hpar : ∀ i, 1 ≤ i → i < parent.val.length →
          0 ≤ parAt parent.val i ∧ parAt parent.val i < (parent.val.length : Int))
        (htree : IsTree parent.val)
        (hlower : AllLower s.val)
        (hn3 : parent.val.length = 3), ∃ r : Std.I64,
          count_palindrome_paths parent s = ok r ∧
            r.val = (2 : Int) + (if byteAt s.val 1 = byteAt s.val 2 then 1 else 0)) := by
    sorry

  end AegisSpec.CountPalindromePaths
