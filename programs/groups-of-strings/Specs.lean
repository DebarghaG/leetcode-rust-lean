import Aegis.GroupStrings.Code.Funs

/-!
# Specifications of `Aegis.GroupStrings.group_strings`

LeetCode problem `groups-of-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GroupStrings

def letterSet (w : alloc.vec.Vec Std.U8) : Finset ℕ :=
  (w.val.filterMap fun b =>
    if 97 ≤ b.val ∧ b.val ≤ 122 then some (b.val - 97) else none).toFinset

def symmDiffCard (s t : Finset ℕ) : ℕ := (s \ t).card + (t \ s).card

def related (s t : Finset ℕ) : Prop :=
  (s.card = t.card ∧ symmDiffCard s t ≤ 2) ∨
    (Int.natAbs ((s.card : ℤ) - (t.card : ℤ)) = 1 ∧ symmDiffCard s t = 1)

def vertexSet (ws : List (alloc.vec.Vec Std.U8)) (i : ℕ) : Finset ℕ :=
  match ws[i]? with
  | some w => letterSet w
  | none => ∅

def adj (ws : List (alloc.vec.Vec Std.U8)) (i j : ℕ) : Prop :=
  i < ws.length ∧ j < ws.length ∧ i ≠ j ∧ related (vertexSet ws i) (vertexSet ws j)

def edge (ws : List (alloc.vec.Vec Std.U8)) (i j : ℕ) : Prop := adj ws i j ∨ adj ws j i

def conn (ws : List (alloc.vec.Vec Std.U8)) (i j : ℕ) : Prop :=
  Relation.ReflTransGen (edge ws) i j

noncomputable def reachClass (ws : List (alloc.vec.Vec Std.U8)) (i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range ws.length).filter fun j => conn ws i j

def IsComponent (ws : List (alloc.vec.Vec Std.U8)) (C : Finset ℕ) : Prop :=
  ∃ i, i < ws.length ∧ C = reachClass ws i

noncomputable def numComponents (ws : List (alloc.vec.Vec Std.U8)) : ℕ := by
  classical
  exact ((Finset.range ws.length).image fun i => reachClass ws i).card

noncomputable def maxComponentSize (ws : List (alloc.vec.Vec Std.U8)) : ℕ := by
  classical
  exact ((Finset.range ws.length).image fun i => (reachClass ws i).card).sup id

def entry (r : alloc.vec.Vec Std.I64) (i : ℕ) : ℤ := (r.val[i]?).map (fun x => x.val) |>.getD 0

def IsWord (w : alloc.vec.Vec Std.U8) : Prop :=
  1 ≤ w.val.length ∧ w.val.length ≤ 26 ∧
    (∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) ∧ w.val.Nodup

def Precondition (words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  1 ≤ words.val.length ∧ words.val.length ≤ 20000 ∧ ∀ w ∈ words.val, IsWord w

def PairwiseNonAdjacent (ws : List (alloc.vec.Vec Std.U8)) : Prop :=
  ∀ i j, i < j → j < ws.length → ¬ adj ws i j

def PairwiseAdjacent (ws : List (alloc.vec.Vec Std.U8)) : Prop :=
  ∀ i j, i < j → j < ws.length → adj ws i j

def IsPermImage (ws ws' : List (alloc.vec.Vec Std.U8)) : Prop :=
  ws'.length = ws.length ∧
    ∃ π : Equiv.Perm (Fin ws.length), ∀ i : Fin ws.length, ws'[(i : ℕ)]? = some (ws.get (π i))

/-- Whenever the function returns a result r, r has length 2, and r[0] equals the number of connected components of G, and r[1] equals the maximum size of a connected component of G, where G is the undirected graph on {0,...,len(words)-1} defined as follows: for each i, let S_i = { c in {0,...,25} | byte 97+c occurs in words[i] }; for i != j, i and j are adjacent in G iff (|S_i| = |S_j| and |S_i Delta S_j| <= 2) or (| |S_i| - |S_j| | = 1 and |S_i Delta S_j| = 1). A connected component is a maximal set of vertices connected by paths in G.
  Preconditions: words is a slice of vectors of bytes satisfying: 1 <= len(words) <= 20000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 26; each words[i] consists of distinct lowercase ASCII letters (bytes 97..122). -/
theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words) :
    ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      r.val.length = 2 ∧ entry r 0 = (numComponents words.val : ℤ) ∧
        entry r 1 = (maxComponentSize words.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words), ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      r.val.length = 2 ∧ entry r 0 = (numComponents words.val : ℤ) ∧
        entry r 1 = (maxComponentSize words.val : ℤ)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: words is a slice of vectors of bytes satisfying: 1 <= len(words) <= 20000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 26; each words[i] consists of distinct lowercase ASCII letters (bytes 97..122). -/
theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words) :
    ∃ r, Aegis.GroupStrings.group_strings words = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words), ∃ r, Aegis.GroupStrings.group_strings words = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 2.
  Preconditions: words is a slice of vectors of bytes satisfying: 1 <= len(words) <= 20000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 26; each words[i] consists of distinct lowercase ASCII letters (bytes 97..122). -/
theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words) :
    ∀ r, Aegis.GroupStrings.group_strings words = ok r → r.val.length = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words), ∀ r, Aegis.GroupStrings.group_strings words = ok r → r.val.length = 2) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r[0] <= len(words).
  Preconditions: words is a slice of vectors of bytes satisfying: 1 <= len(words) <= 20000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 26; each words[i] consists of distinct lowercase ASCII letters (bytes 97..122). -/
theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words) :
    ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      1 ≤ entry r 0 ∧ entry r 0 ≤ (words.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words), ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      1 ≤ entry r 0 ∧ entry r 0 ≤ (words.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r[1] <= len(words).
  Preconditions: words is a slice of vectors of bytes satisfying: 1 <= len(words) <= 20000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 26; each words[i] consists of distinct lowercase ASCII letters (bytes 97..122). -/
theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words) :
    ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      1 ≤ entry r 1 ∧ entry r 1 ≤ (words.val.length : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words), ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      1 ≤ entry r 1 ∧ entry r 1 ≤ (words.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r[0] * r[1] >= len(words).
  Preconditions: words is a slice of vectors of bytes satisfying: 1 <= len(words) <= 20000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 26; each words[i] consists of distinct lowercase ASCII letters (bytes 97..122). -/
theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words) :
    ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      (words.val.length : ℤ) ≤ entry r 0 * entry r 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words), ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      (words.val.length : ℤ) ≤ entry r 0 * entry r 1) := by
  sorry

/-- Whenever the function returns a result r, r[0] = len(words) and r[1] = 1.
  Preconditions: words is a slice of vectors of bytes satisfying the problem constraints: 1 <= len(words) <= 20000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 26; each words[i] consists of distinct lowercase ASCII letters (bytes 97..122). Additionally, for every i, j with 0 <= i < j < len(words), connected(i,j) does not hold, where S_i is the set of letters of words[i] and connected(i,j) means (|S_i| = |S_j| and |S_i Delta S_j| <= 2) or (| |S_i| - |S_j| | = 1 and |S_i Delta S_j| = 1). -/
theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words)
    (hdisconnected : PairwiseNonAdjacent words.val) :
    ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      entry r 0 = (words.val.length : ℤ) ∧ entry r 1 = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words)
    (hdisconnected : PairwiseNonAdjacent words.val), ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      entry r 0 = (words.val.length : ℤ) ∧ entry r 1 = 1) := by
  sorry

/-- Whenever the function returns a result r, r[0] = 1 and r[1] = len(words).
  Preconditions: words is a slice of vectors of bytes satisfying the problem constraints: 1 <= len(words) <= 20000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 26; each words[i] consists of distinct lowercase ASCII letters (bytes 97..122). Additionally, for every i, j with 0 <= i < j < len(words), connected(i,j) holds, where S_i is the set of letters of words[i] and connected(i,j) means (|S_i| = |S_j| and |S_i Delta S_j| <= 2) or (| |S_i| - |S_j| | = 1 and |S_i Delta S_j| = 1). -/
theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words)
    (hconnected : PairwiseAdjacent words.val) :
    ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      entry r 0 = 1 ∧ entry r 1 = (words.val.length : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words)
    (hconnected : PairwiseAdjacent words.val), ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      entry r 0 = 1 ∧ entry r 1 = (words.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, there exists a connected component C of G such that |C| = r[1], where G is defined as in spec_1.
  Preconditions: words is a slice of vectors of bytes satisfying: 1 <= len(words) <= 20000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 26; each words[i] consists of distinct lowercase ASCII letters (bytes 97..122). -/
theorem spec_9 (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words) :
    ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      ∃ C, IsComponent words.val C ∧ (C.card : ℤ) = entry r 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words), ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      ∃ C, IsComponent words.val C ∧ (C.card : ℤ) = entry r 1) := by
  sorry

/-- Whenever the function returns a result r, for every connected component C of G, |C| <= r[1], where G is defined as in spec_1.
  Preconditions: words is a slice of vectors of bytes satisfying: 1 <= len(words) <= 20000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 26; each words[i] consists of distinct lowercase ASCII letters (bytes 97..122). -/
theorem spec_10 (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words) :
    ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      ∀ C, IsComponent words.val C → (C.card : ℤ) ≤ entry r 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words), ∀ r, Aegis.GroupStrings.group_strings words = ok r →
      ∀ C, IsComponent words.val C → (C.card : ℤ) ≤ entry r 1) := by
  sorry

/-- Let words' be any slice of the same length such that there exists a permutation pi of {0,...,len(words)-1} with words'[i] = words[pi(i)] for all i. Whenever group_strings(words) returns r and group_strings(words') returns r', we have r'[0] = r[0] and r'[1] = r[1].
  Preconditions: words is a slice of vectors of bytes satisfying: 1 <= len(words) <= 20000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 26; each words[i] consists of distinct lowercase ASCII letters (bytes 97..122). -/
theorem spec_11 (words words' : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words)
    (hperm : IsPermImage words.val words'.val) (r r' : alloc.vec.Vec Std.I64)
    (h : Aegis.GroupStrings.group_strings words = ok r)
    (h' : Aegis.GroupStrings.group_strings words' = ok r') :
    entry r' 0 = entry r 0 ∧ entry r' 1 = entry r 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8)) (hpre : Precondition words)
    (hperm : IsPermImage words.val words'.val) (r r' : alloc.vec.Vec Std.I64)
    (h : Aegis.GroupStrings.group_strings words = ok r)
    (h' : Aegis.GroupStrings.group_strings words' = ok r'), entry r' 0 = entry r 0 ∧ entry r' 1 = entry r 1) := by
  sorry

end AegisSpec.GroupStrings
