import Aegis.ShortestWordDistance.Code.Funs

/-!
# Specifications of `Aegis.ShortestWordDistance.shortest_word_distance`

LeetCode problem `shortest-word-distance-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ShortestWordDistance

open Aegis.ShortestWordDistance (shortest_word_distance)

def bytesOfList (l : List Std.U8) : List Nat := l.map (fun b => b.val)

def bytesOfSlice (s : Slice Std.U8) : List Nat := bytesOfList s.val

def wordAt? (wordsDict : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : Option (List Nat) :=
  (wordsDict.val[i]?).map (fun w => bytesOfList w.val)

def WordAt (wordsDict : Slice (alloc.vec.Vec Std.U8)) (i : Nat) (w : Slice Std.U8) : Prop :=
  wordAt? wordsDict i = some (bytesOfSlice w)

def Occurs (wordsDict : Slice (alloc.vec.Vec Std.U8)) (w : Slice Std.U8) : Prop :=
  ∃ i, WordAt wordsDict i w

instance decidableWordAt (wordsDict : Slice (alloc.vec.Vec Std.U8)) (i : Nat)
    (w : Slice Std.U8) : Decidable (WordAt wordsDict i w) :=
  inferInstanceAs (Decidable (wordAt? wordsDict i = some (bytesOfSlice w)))

def occIndices (wordsDict : Slice (alloc.vec.Vec Std.U8)) (w : Slice Std.U8) : Finset Nat :=
  (Finset.range wordsDict.val.length).filter (fun i => WordAt wordsDict i w)

def absDiff (i j : Nat) : Nat := (i - j) + (j - i)

def distSet (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8) :
    Finset Nat :=
  (((occIndices wordsDict word1).product (occIndices wordsDict word2)).filter
      (fun p => p.1 ≠ p.2)).image (fun p => absDiff p.1 p.2)

def distsToWord (wordsDict : Slice (alloc.vec.Vec Std.U8)) (w : Slice Std.U8) (p : Nat) :
    Finset Nat :=
  (occIndices wordsDict w).image (fun j => absDiff p j)

def consecutiveDiffs (ps : List Nat) : List Nat :=
  (ps.zip ps.tail).map (fun p => p.2 - p.1)

def differingConsecutiveDiffs (wordsDict : Slice (alloc.vec.Vec Std.U8)) (ps : List Nat) :
    List Nat :=
  (ps.zip ps.tail).filterMap (fun p =>
    if wordAt? wordsDict p.1 ≠ wordAt? wordsDict p.2 then some (p.2 - p.1) else none)

def IsIndexListOf (wordsDict : Slice (alloc.vec.Vec Std.U8)) (w : Slice Std.U8)
    (ps : List Nat) : Prop :=
  ps.Pairwise (· < ·) ∧
    (∀ p ∈ ps, WordAt wordsDict p w) ∧
    (∀ p, WordAt wordsDict p w → p ∈ ps)

def IsMixedIndexListOf (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (ps : List Nat) : Prop :=
  ps.Pairwise (· < ·) ∧
    (∀ p ∈ ps, WordAt wordsDict p word1 ∨ WordAt wordsDict p word2) ∧
    (∀ p, (WordAt wordsDict p word1 ∨ WordAt wordsDict p word2) → p ∈ ps)

def IsLowerWord (l : List Nat) : Prop :=
  1 ≤ l.length ∧ l.length ≤ 10 ∧ ∀ c ∈ l, 97 ≤ c ∧ c ≤ 122

def DictOK (wordsDict : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  1 ≤ wordsDict.val.length ∧ wordsDict.val.length ≤ 100000 ∧
    ∀ (i : Nat) (w : alloc.vec.Vec Std.U8),
      wordsDict.val[i]? = some w → IsLowerWord (bytesOfList w.val)

def ProblemConstraints (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8) :
    Prop :=
  DictOK wordsDict ∧ Occurs wordsDict word1 ∧ Occurs wordsDict word2 ∧
    (bytesOfSlice word1 = bytesOfSlice word2 →
      ∃ i j, i ≠ j ∧ WordAt wordsDict i word1 ∧ WordAt wordsDict j word1)

/-- The function returns a result r, and r = min { |i - j| : 0 <= i < n, 0 <= j < n, i != j, wordsDict[i] = word1, wordsDict[j] = word2 }. The minimum is over a nonempty finite set by the preconditions. Equivalently, r is the shortest distance between two distinct occurrences, one of word1 and one of word2; when word1 = word2 the two occurrences are required to be at different indices.
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict, i.e. there is an index i with wordsDict[i] = word1 and an index j with wordsDict[j] = word2; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings means equality of their byte sequences; wordsDict[i] = word1 abbreviates equality of the corresponding byte sequences. -/
theorem spec_1 (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2) :
    ∃ r, shortest_word_distance wordsDict word1 word2 = ok r ∧
      ∃ hs : (distSet wordsDict word1 word2).Nonempty,
        r.val = ((distSet wordsDict word1 word2).min' hs : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2), ∃ r, shortest_word_distance wordsDict word1 word2 = ok r ∧
      ∃ hs : (distSet wordsDict word1 word2).Nonempty,
        r.val = ((distSet wordsDict word1 word2).min' hs : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail: it does not panic, access out of bounds, or overflow. In particular, the result is a defined Std.I64 value.
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings is equality of byte sequences. -/
theorem spec_2 (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2) :
    ∃ r, shortest_word_distance wordsDict word1 word2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2), ∃ r, shortest_word_distance wordsDict word1 word2 = ok r) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, 1 <= r <= n - 1, where n = len(wordsDict).
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings is equality of byte sequences. -/
theorem spec_3 (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2) :
    ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      1 ≤ r.val ∧ r.val ≤ (wordsDict.val.length : Int) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2), ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      1 ≤ r.val ∧ r.val ≤ (wordsDict.val.length : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, there exist indices i and j such that 0 <= i < n, 0 <= j < n, i != j, wordsDict[i] = word1, wordsDict[j] = word2, and r = |i - j|.
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings is equality of byte sequences. -/
theorem spec_4 (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2) :
    ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∃ i j : Nat, i < wordsDict.val.length ∧ j < wordsDict.val.length ∧ i ≠ j ∧
        WordAt wordsDict i word1 ∧ WordAt wordsDict j word2 ∧
        r.val = (absDiff i j : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2), ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∃ i j : Nat, i < wordsDict.val.length ∧ j < wordsDict.val.length ∧ i ≠ j ∧
        WordAt wordsDict i word1 ∧ WordAt wordsDict j word2 ∧
        r.val = (absDiff i j : Int)) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, for every pair of indices i and j with 0 <= i < n, 0 <= j < n, i != j, wordsDict[i] = word1, and wordsDict[j] = word2, we have r <= |i - j|.
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings is equality of byte sequences. -/
theorem spec_5 (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2) :
    ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∀ i j : Nat, i < wordsDict.val.length → j < wordsDict.val.length → i ≠ j →
        WordAt wordsDict i word1 → WordAt wordsDict j word2 →
        r.val ≤ (absDiff i j : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2), ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∀ i j : Nat, i < wordsDict.val.length → j < wordsDict.val.length → i ≠ j →
        WordAt wordsDict i word1 → WordAt wordsDict j word2 →
        r.val ≤ (absDiff i j : Int)) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, r = 1 if and only if there exists an index i with 0 <= i < n - 1 such that (wordsDict[i] = word1 and wordsDict[i+1] = word2) or (wordsDict[i] = word2 and wordsDict[i+1] = word1).
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings is equality of byte sequences. -/
theorem spec_6 (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2) :
    ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      (r.val = 1 ↔
        ∃ i : Nat, i < wordsDict.val.length - 1 ∧
          ((WordAt wordsDict i word1 ∧ WordAt wordsDict (i + 1) word2) ∨
            (WordAt wordsDict i word2 ∧ WordAt wordsDict (i + 1) word1))) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2), ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      (r.val = 1 ↔
        ∃ i : Nat, i < wordsDict.val.length - 1 ∧
          ((WordAt wordsDict i word1 ∧ WordAt wordsDict (i + 1) word2) ∨
            (WordAt wordsDict i word2 ∧ WordAt wordsDict (i + 1) word1)))) := by
  sorry

/-- Whenever the function returns a result r, r = min { p_{k+1} - p_k : 0 <= k < m - 1 }.
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings is equality of byte sequences. Assume word1 = word2. Let p_0 < p_1 < ... < p_{m-1} be the increasing list of all indices p with wordsDict[p] = word1; the preconditions imply m >= 2. -/
theorem spec_7 (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2)
    (heq : bytesOfSlice word1 = bytesOfSlice word2)
    (ps : List Nat) (hps : IsIndexListOf wordsDict word1 ps) :
    ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∃ hs : (consecutiveDiffs ps).toFinset.Nonempty,
        r.val = ((consecutiveDiffs ps).toFinset.min' hs : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2)
    (heq : bytesOfSlice word1 = bytesOfSlice word2)
    (ps : List Nat) (hps : IsIndexListOf wordsDict word1 ps), ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∃ hs : (consecutiveDiffs ps).toFinset.Nonempty,
        r.val = ((consecutiveDiffs ps).toFinset.min' hs : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = min { p_{k+1} - p_k : 0 <= k < m - 1 and wordsDict[p_k] != wordsDict[p_{k+1}] }.
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings is equality of byte sequences. Assume word1 != word2. Let p_0 < p_1 < ... < p_{m-1} be the increasing list of all indices p at which wordsDict[p] = word1 or wordsDict[p] = word2; the preconditions imply m >= 2 and that at least one consecutive pair has different words. -/
theorem spec_8 (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2)
    (hne : bytesOfSlice word1 ≠ bytesOfSlice word2)
    (ps : List Nat) (hps : IsMixedIndexListOf wordsDict word1 word2 ps) :
    ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∃ hs : (differingConsecutiveDiffs wordsDict ps).toFinset.Nonempty,
        r.val = ((differingConsecutiveDiffs wordsDict ps).toFinset.min' hs : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2)
    (hne : bytesOfSlice word1 ≠ bytesOfSlice word2)
    (ps : List Nat) (hps : IsMixedIndexListOf wordsDict word1 word2 ps), ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∃ hs : (differingConsecutiveDiffs wordsDict ps).toFinset.Nonempty,
        r.val = ((differingConsecutiveDiffs wordsDict ps).toFinset.min' hs : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = min { |p - j| : 0 <= j < n and wordsDict[j] = word2 }.
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings is equality of byte sequences. Assume word1 != word2 and word1 occurs exactly once; let p be the unique index with wordsDict[p] = word1. -/
theorem spec_9 (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2)
    (hne : bytesOfSlice word1 ≠ bytesOfSlice word2)
    (p : Nat) (hp : WordAt wordsDict p word1)
    (huniq : ∀ q, WordAt wordsDict q word1 → q = p) :
    ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∃ hs : (distsToWord wordsDict word2 p).Nonempty,
        r.val = ((distsToWord wordsDict word2 p).min' hs : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2)
    (hne : bytesOfSlice word1 ≠ bytesOfSlice word2)
    (p : Nat) (hp : WordAt wordsDict p word1)
    (huniq : ∀ q, WordAt wordsDict q word1 → q = p), ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∃ hs : (distsToWord wordsDict word2 p).Nonempty,
        r.val = ((distsToWord wordsDict word2 p).min' hs : Int)) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, there exist indices i and j such that 0 <= i < n, 0 <= j < n, i != j, wordsDict[i] = word1, wordsDict[j] = word2, r = |i - j|, and for every k with min(i,j) < k < max(i,j), wordsDict[k] != word1 and wordsDict[k] != word2.
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings is equality of byte sequences. -/
theorem spec_10 (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2) :
    ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∃ i j : Nat, i < wordsDict.val.length ∧ j < wordsDict.val.length ∧ i ≠ j ∧
        WordAt wordsDict i word1 ∧ WordAt wordsDict j word2 ∧
        r.val = (absDiff i j : Int) ∧
        ∀ k, min i j < k → k < max i j → ¬ WordAt wordsDict k word1 ∧
          ¬ WordAt wordsDict k word2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2), ∀ r, shortest_word_distance wordsDict word1 word2 = ok r →
      ∃ i j : Nat, i < wordsDict.val.length ∧ j < wordsDict.val.length ∧ i ≠ j ∧
        WordAt wordsDict i word1 ∧ WordAt wordsDict j word2 ∧
        r.val = (absDiff i j : Int) ∧
        ∀ k, min i j < k → k < max i j → ¬ WordAt wordsDict k word1 ∧
          ¬ WordAt wordsDict k word2) := by
  sorry

/-- Whenever the function returns r on arguments (wordsDict, word1, word2) and returns r_swapped on arguments (wordsDict, word2, word1), we have r = r_swapped.
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings is equality of byte sequences. Assume word1 != word2. -/
theorem spec_11 (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2)
    (hne : bytesOfSlice word1 ≠ bytesOfSlice word2) :
    ∀ r r', shortest_word_distance wordsDict word1 word2 = ok r →
      shortest_word_distance wordsDict word2 word1 = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (h : ProblemConstraints wordsDict word1 word2)
    (hne : bytesOfSlice word1 ≠ bytesOfSlice word2), ∀ r r', shortest_word_distance wordsDict word1 word2 = ok r →
      shortest_word_distance wordsDict word2 word1 = ok r' → r = r') := by
  sorry

/-- For any slice wordsDict' of byte vectors of the same length n such that for every i with 0 <= i < n, (wordsDict'[i] = word1 if and only if wordsDict[i] = word1) and (wordsDict'[i] = word2 if and only if wordsDict[i] = word2), if the function returns r on (wordsDict, word1, word2) and r' on (wordsDict', word1, word2), then r = r'.
  Preconditions: Let n = len(wordsDict). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, wordsDict[i] is a nonempty byte string of length at most 10 consisting of lowercase English letters; word1 and word2 are byte strings that occur in wordsDict; if word1 = word2 then there are at least two distinct indices i != j with wordsDict[i] = wordsDict[j] = word1. Equality of strings is equality of byte sequences. -/
theorem spec_12 (wordsDict wordsDict' : Slice (alloc.vec.Vec Std.U8))
    (word1 word2 : Slice Std.U8) (h : ProblemConstraints wordsDict word1 word2)
    (hlen : wordsDict'.val.length = wordsDict.val.length)
    (h1 : ∀ i, i < wordsDict.val.length → (WordAt wordsDict' i word1 ↔ WordAt wordsDict i word1))
    (h2 : ∀ i, i < wordsDict.val.length → (WordAt wordsDict' i word2 ↔ WordAt wordsDict i word2)) :
    ∀ r r', shortest_word_distance wordsDict word1 word2 = ok r →
      shortest_word_distance wordsDict' word1 word2 = ok r' → r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (wordsDict wordsDict' : Slice (alloc.vec.Vec Std.U8))
    (word1 word2 : Slice Std.U8) (h : ProblemConstraints wordsDict word1 word2)
    (hlen : wordsDict'.val.length = wordsDict.val.length)
    (h1 : ∀ i, i < wordsDict.val.length → (WordAt wordsDict' i word1 ↔ WordAt wordsDict i word1))
    (h2 : ∀ i, i < wordsDict.val.length → (WordAt wordsDict' i word2 ↔ WordAt wordsDict i word2)), ∀ r r', shortest_word_distance wordsDict word1 word2 = ok r →
      shortest_word_distance wordsDict' word1 word2 = ok r' → r = r') := by
  sorry

end AegisSpec.ShortestWordDistance
