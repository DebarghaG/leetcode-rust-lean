import Aegis.ShortestDistance.Code.Funs

/-!
# Specifications of `Aegis.ShortestDistance.shortest_distance`

LeetCode problem `shortest-word-distance`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ShortestDistance

def wordAt (wordsDict : Slice (alloc.vec.Vec U8)) (i : ℕ) : Option (List U8) :=
  (wordsDict.val[i]?).map (fun v => v.val)

def Occ (wordsDict : Slice (alloc.vec.Vec U8)) (word : Slice U8) (i : ℕ) : Prop :=
  wordAt wordsDict i = some word.val

def IsLower (b : U8) : Prop :=
  97 ≤ b.val ∧ b.val ≤ 122

def EntryOk (wordsDict : Slice (alloc.vec.Vec U8)) (i : ℕ) : Prop :=
  ∃ w, wordAt wordsDict i = some w ∧ 1 ≤ w.length ∧ w.length ≤ 10 ∧ ∀ b ∈ w, IsLower b

def idxDist (i j : ℕ) : ℕ :=
  Nat.max i j - Nat.min i j

def dists (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8) : Set ℕ :=
  { d | ∃ i j, Occ wordsDict word1 i ∧ Occ wordsDict word2 j ∧ idxDist i j = d }

noncomputable def minDist (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8) : ℕ :=
  sInf (dists wordsDict word1 word2)

def occPos (wordsDict : Slice (alloc.vec.Vec U8)) (word : Slice U8) : Set ℕ :=
  { i | i < wordsDict.val.length ∧ Occ wordsDict word i }

noncomputable def firstOcc (wordsDict : Slice (alloc.vec.Vec U8)) (word : Slice U8) : ℕ :=
  sInf (occPos wordsDict word)

noncomputable def lastOcc (wordsDict : Slice (alloc.vec.Vec U8)) (word : Slice U8) : ℕ :=
  sSup (occPos wordsDict word)

/-- Whenever the function returns a result r, the following holds. Let d be the minimum of the natural-number distances |i-j| over all pairs of indices i,j with 0 <= i < len(wordsDict), 0 <= j < len(wordsDict), wordsDict[i] = word1, and wordsDict[j] = word2. Then r equals the i64 value of d.
  Preconditions: len(wordsDict) >= 2 and len(wordsDict) <= 30000; for every i with 0 <= i < len(wordsDict), 1 <= len(wordsDict[i]) <= 10 and every byte of wordsDict[i] is a lowercase English letter; there exist indices a and b with 0 <= a < len(wordsDict) and 0 <= b < len(wordsDict) such that wordsDict[a] = word1 and wordsDict[b] = word2; word1 != word2. -/
theorem spec_1
    (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r) :
    r.val = (minDist wordsDict word1 word2 : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r), r.val = (minDist wordsDict word1 word2 : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r >= 1 as an i64 value.
  Preconditions: len(wordsDict) >= 2 and len(wordsDict) <= 30000; for every i with 0 <= i < len(wordsDict), 1 <= len(wordsDict[i]) <= 10 and every byte of wordsDict[i] is a lowercase English letter; there exist indices a and b with 0 <= a < len(wordsDict) and 0 <= b < len(wordsDict) such that wordsDict[a] = word1 and wordsDict[b] = word2; word1 != word2. -/
theorem spec_2
    (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r) :
    (1 : ℤ) ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r), (1 : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= (len(wordsDict) - 1) as an i64 value.
  Preconditions: len(wordsDict) >= 2 and len(wordsDict) <= 30000; for every i with 0 <= i < len(wordsDict), 1 <= len(wordsDict[i]) <= 10 and every byte of wordsDict[i] is a lowercase English letter; there exist indices a and b with 0 <= a < len(wordsDict) and 0 <= b < len(wordsDict) such that wordsDict[a] = word1 and wordsDict[b] = word2; word1 != word2. -/
theorem spec_3
    (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r) :
    r.val ≤ (wordsDict.val.length : ℤ) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r), r.val ≤ (wordsDict.val.length : ℤ) - 1) := by
  sorry

/-- Whenever the function returns a result r, there exist indices i and j such that 0 <= i < len(wordsDict), 0 <= j < len(wordsDict), wordsDict[i] = word1, wordsDict[j] = word2, and |i-j| equals the natural-number value of r.
  Preconditions: len(wordsDict) >= 2 and len(wordsDict) <= 30000; for every i with 0 <= i < len(wordsDict), 1 <= len(wordsDict[i]) <= 10 and every byte of wordsDict[i] is a lowercase English letter; there exist indices a and b with 0 <= a < len(wordsDict) and 0 <= b < len(wordsDict) such that wordsDict[a] = word1 and wordsDict[b] = word2; word1 != word2. -/
theorem spec_4
    (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r) :
    ∃ i j, i < wordsDict.val.length ∧ j < wordsDict.val.length ∧
      Occ wordsDict word1 i ∧ Occ wordsDict word2 j ∧ r.val.natAbs = idxDist i j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r), ∃ i j, i < wordsDict.val.length ∧ j < wordsDict.val.length ∧
      Occ wordsDict word1 i ∧ Occ wordsDict word2 j ∧ r.val.natAbs = idxDist i j) := by
  sorry

/-- Whenever the function returns a result r, for every pair of indices i,j with 0 <= i < len(wordsDict), 0 <= j < len(wordsDict), wordsDict[i] = word1, and wordsDict[j] = word2, we have r <= |i-j|, comparing r as a natural number with the distance |i-j|.
  Preconditions: len(wordsDict) >= 2 and len(wordsDict) <= 30000; for every i with 0 <= i < len(wordsDict), 1 <= len(wordsDict[i]) <= 10 and every byte of wordsDict[i] is a lowercase English letter; there exist indices a and b with 0 <= a < len(wordsDict) and 0 <= b < len(wordsDict) such that wordsDict[a] = word1 and wordsDict[b] = word2; word1 != word2. -/
theorem spec_5
    (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r) :
    ∀ i j, i < wordsDict.val.length → j < wordsDict.val.length →
      Occ wordsDict word1 i → Occ wordsDict word2 j →
      r.val.natAbs ≤ idxDist i j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r), ∀ i j, i < wordsDict.val.length → j < wordsDict.val.length →
      Occ wordsDict word1 i → Occ wordsDict word2 j →
      r.val.natAbs ≤ idxDist i j) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if there exists an index k with 0 <= k < len(wordsDict) - 1 such that either (wordsDict[k] = word1 and wordsDict[k+1] = word2) or (wordsDict[k] = word2 and wordsDict[k+1] = word1).
  Preconditions: len(wordsDict) >= 2 and len(wordsDict) <= 30000; for every i with 0 <= i < len(wordsDict), 1 <= len(wordsDict[i]) <= 10 and every byte of wordsDict[i] is a lowercase English letter; there exist indices a and b with 0 <= a < len(wordsDict) and 0 <= b < len(wordsDict) such that wordsDict[a] = word1 and wordsDict[b] = word2; word1 != word2. -/
theorem spec_6
    (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r) :
    (r.val = 1 ↔ ∃ k, k < wordsDict.val.length - 1 ∧
      ((Occ wordsDict word1 k ∧ Occ wordsDict word2 (k + 1)) ∨
       (Occ wordsDict word2 k ∧ Occ wordsDict word1 (k + 1)))) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r), (r.val = 1 ↔ ∃ k, k < wordsDict.val.length - 1 ∧
      ((Occ wordsDict word1 k ∧ Occ wordsDict word2 (k + 1)) ∨
       (Occ wordsDict word2 k ∧ Occ wordsDict word1 (k + 1))))) := by
  sorry

/-- Whenever the function returns r for (wordsDict, word1, word2) and also returns r' for (wordsDict, word2, word1), both under the preconditions, we have r = r'.
  Preconditions: len(wordsDict) >= 2 and len(wordsDict) <= 30000; for every i with 0 <= i < len(wordsDict), 1 <= len(wordsDict[i]) <= 10 and every byte of wordsDict[i] is a lowercase English letter; there exist indices a and b with 0 <= a < len(wordsDict) and 0 <= b < len(wordsDict) such that wordsDict[a] = word1 and wordsDict[b] = word2; word1 != word2. -/
theorem spec_7
    (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r r' : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r)
    (hr' : Aegis.ShortestDistance.shortest_distance wordsDict word2 word1 = ok r') :
    r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (r r' : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r)
    (hr' : Aegis.ShortestDistance.shortest_distance wordsDict word2 word1 = ok r'), r = r') := by
  sorry

/-- Suppose that for every i with 0 <= i < len(wordsDict), wordsDict[i] = word1 if and only if wordsDict'[i] = word1, and wordsDict[i] = word2 if and only if wordsDict'[i] = word2. If the call on wordsDict returns r and the call on wordsDict' returns r', then r = r'.
  Preconditions: Both (wordsDict, word1, word2) and (wordsDict', word1, word2) satisfy: list length >= 2 and <= 30000; every entry has length 1..10 and consists of lowercase English letters; word1 and word2 occur in the list; word1 != word2. Also len(wordsDict) = len(wordsDict'). -/
theorem spec_8
    (wordsDict wordsDict' : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hlen_ge' : 2 ≤ wordsDict'.val.length)
    (hlen_le' : wordsDict'.val.length ≤ 30000)
    (hentries' : ∀ i, i < wordsDict'.val.length → EntryOk wordsDict' i)
    (hocc1' : ∃ a, a < wordsDict'.val.length ∧ Occ wordsDict' word1 a)
    (hocc2' : ∃ b, b < wordsDict'.val.length ∧ Occ wordsDict' word2 b)
    (hne : word1.val ≠ word2.val)
    (hlen_eq : wordsDict.val.length = wordsDict'.val.length)
    (hword1 : ∀ i, i < wordsDict.val.length →
      (Occ wordsDict word1 i ↔ Occ wordsDict' word1 i))
    (hword2 : ∀ i, i < wordsDict.val.length →
      (Occ wordsDict word2 i ↔ Occ wordsDict' word2 i))
    (r r' : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r)
    (hr' : Aegis.ShortestDistance.shortest_distance wordsDict' word1 word2 = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (wordsDict wordsDict' : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hlen_ge' : 2 ≤ wordsDict'.val.length)
    (hlen_le' : wordsDict'.val.length ≤ 30000)
    (hentries' : ∀ i, i < wordsDict'.val.length → EntryOk wordsDict' i)
    (hocc1' : ∃ a, a < wordsDict'.val.length ∧ Occ wordsDict' word1 a)
    (hocc2' : ∃ b, b < wordsDict'.val.length ∧ Occ wordsDict' word2 b)
    (hne : word1.val ≠ word2.val)
    (hlen_eq : wordsDict.val.length = wordsDict'.val.length)
    (hword1 : ∀ i, i < wordsDict.val.length →
      (Occ wordsDict word1 i ↔ Occ wordsDict' word1 i))
    (hword2 : ∀ i, i < wordsDict.val.length →
      (Occ wordsDict word2 i ↔ Occ wordsDict' word2 i))
    (r r' : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r)
    (hr' : Aegis.ShortestDistance.shortest_distance wordsDict' word1 word2 = ok r'), r = r') := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not panic, overflow, or perform an out-of-bounds access.
  Preconditions: len(wordsDict) >= 2 and len(wordsDict) <= 30000; for every i with 0 <= i < len(wordsDict), 1 <= len(wordsDict[i]) <= 10 and every byte of wordsDict[i] is a lowercase English letter; there exist indices a and b with 0 <= a < len(wordsDict) and 0 <= b < len(wordsDict) such that wordsDict[a] = word1 and wordsDict[b] = word2; word1 != word2. -/
theorem spec_9
    (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val) :
    ∃ r, Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val), ∃ r, Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, if every occurrence of word1 is to the left of every occurrence of word2 (that is, for all i,j with 0 <= i < len(wordsDict), 0 <= j < len(wordsDict), wordsDict[i] = word1, and wordsDict[j] = word2, we have i < j), then r equals (min { j | 0 <= j < len(wordsDict) and wordsDict[j] = word2 }) - (max { i | 0 <= i < len(wordsDict) and wordsDict[i] = word1 }), as an i64 value.
  Preconditions: len(wordsDict) >= 2 and len(wordsDict) <= 30000; for every i with 0 <= i < len(wordsDict), 1 <= len(wordsDict[i]) <= 10 and every byte of wordsDict[i] is a lowercase English letter; there exist indices a and b with 0 <= a < len(wordsDict) and 0 <= b < len(wordsDict) such that wordsDict[a] = word1 and wordsDict[b] = word2; word1 != word2. -/
theorem spec_10
    (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (hleft : ∀ i j, i < wordsDict.val.length → j < wordsDict.val.length →
      Occ wordsDict word1 i → Occ wordsDict word2 j → i < j)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r) :
    r.val = (firstOcc wordsDict word2 : ℤ) - (lastOcc wordsDict word1 : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (wordsDict : Slice (alloc.vec.Vec U8)) (word1 word2 : Slice U8)
    (hlen_ge : 2 ≤ wordsDict.val.length)
    (hlen_le : wordsDict.val.length ≤ 30000)
    (hentries : ∀ i, i < wordsDict.val.length → EntryOk wordsDict i)
    (hocc1 : ∃ a, a < wordsDict.val.length ∧ Occ wordsDict word1 a)
    (hocc2 : ∃ b, b < wordsDict.val.length ∧ Occ wordsDict word2 b)
    (hne : word1.val ≠ word2.val)
    (hleft : ∀ i j, i < wordsDict.val.length → j < wordsDict.val.length →
      Occ wordsDict word1 i → Occ wordsDict word2 j → i < j)
    (r : I64)
    (hr : Aegis.ShortestDistance.shortest_distance wordsDict word1 word2 = ok r), r.val = (firstOcc wordsDict word2 : ℤ) - (lastOcc wordsDict word1 : ℤ)) := by
  sorry

end AegisSpec.ShortestDistance
