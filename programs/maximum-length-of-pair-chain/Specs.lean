import Aegis.FindLongestChain.Code.Funs

/-!
# Specifications of `Aegis.FindLongestChain.find_longest_chain`

LeetCode problem `maximum-length-of-pair-chain`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindLongestChain

abbrev PairVec : Type := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

def pairEntries (v : PairVec) : List ℤ := v.val.map (fun x => x.val)

def pairList (pairs : Slice PairVec) : List (List ℤ) := pairs.val.map pairEntries

def PairAt (l : List (List ℤ)) (i : ℕ) : List ℤ := l[i]!

def StartAt (l : List (List ℤ)) (i : ℕ) : ℤ := (l[i]!)[0]!

def EndAt (l : List (List ℤ)) (i : ℕ) : ℤ := (l[i]!)[1]!

def AllPairsLen2 (l : List (List ℤ)) : Prop := ∀ i, i < l.length → (l[i]!).length = 2

def EntriesInRange (l : List (List ℤ)) : Prop :=
  ∀ i j, i < l.length → j < (l[i]!).length → -1000 ≤ (l[i]!)[j]! ∧ (l[i]!)[j]! ≤ 1000

def ProperIntervals (l : List (List ℤ)) : Prop := ∀ i, i < l.length → StartAt l i < EndAt l i

def BoundedOrdered (l : List (List ℤ)) : Prop :=
  ∀ i, i < l.length → -1000 ≤ StartAt l i ∧ StartAt l i < EndAt l i ∧ EndAt l i ≤ 1000

def ChainAdj (l : List (List ℤ)) (idxs : List ℕ) : Prop :=
  ∀ t : ℕ, t + 1 < idxs.length → EndAt l (idxs[t]!) < StartAt l (idxs[t + 1]!)

def IsChain (l : List (List ℤ)) (idxs : List ℕ) : Prop :=
  (∀ i ∈ idxs, i < l.length) ∧ idxs.Nodup ∧ ChainAdj l idxs

def Achievable (l : List (List ℤ)) (k : ℕ) : Prop :=
  ∃ idxs : List ℕ, idxs.length = k ∧ IsChain l idxs

def StrictIncr (js : List ℕ) : Prop := ∀ t : ℕ, t + 1 < js.length → js[t]! < js[t + 1]!

def IsSubseqOf (l l' : List (List ℤ)) : Prop :=
  ∃ js : List ℕ,
    js.length = l.length ∧ (∀ j ∈ js, j < l'.length) ∧ StrictIncr js ∧
      ∀ i : ℕ, i < l.length → l'[js[i]!]! = l[i]!

def BijectionOn (n : ℕ) (σ : ℕ → ℕ) : Prop :=
  (∀ i, i < n → σ i < n) ∧
    (∀ i, i < n → ∀ j, j < n → σ i = σ j → i = j) ∧
      ∀ j, j < n → ∃ i, i < n ∧ σ i = j

def numDistinct (l : List (List ℤ)) : ℕ := l.toFinset.card

/-- The function returns a result r and r = L(pairs), where L(pairs) is the largest integer k ≥ 0 such that there exist pairwise distinct indices i_0, ..., i_{k-1} in {0, ..., len(pairs)-1} with pairs[i_t][1] < pairs[i_{t+1}][0] for every t with 0 ≤ t < k-1. (For k=0 the sequence is empty; for k=1 there is one index and the adjacency condition is vacuous.)
  Preconditions: Every element of pairs has length exactly 2; 1 ≤ len(pairs) ≤ 1000; for every i with 0 ≤ i < len(pairs), -1000 ≤ pairs[i][0] < pairs[i][1] ≤ 1000. -/
theorem spec_1 (pairs : Slice PairVec)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hlen_ge : 1 ≤ (pairList pairs).length)
    (hlen_le : (pairList pairs).length ≤ 1000)
    (hbo : BoundedOrdered (pairList pairs)) :
    ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧ 0 ≤ r.val ∧
        Achievable (pairList pairs) r.val.toNat ∧
          ∀ k : ℕ, Achievable (pairList pairs) k → (k : ℤ) ≤ r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (pairs : Slice PairVec)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hlen_ge : 1 ≤ (pairList pairs).length)
    (hlen_le : (pairList pairs).length ≤ 1000)
    (hbo : BoundedOrdered (pairList pairs)), ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧ 0 ≤ r.val ∧
        Achievable (pairList pairs) r.val.toNat ∧
          ∀ k : ℕ, Achievable (pairList pairs) k → (k : ℤ) ≤ r.val) := by
  sorry

/-- The function returns a result r (it does not overflow, panic, or access out of bounds).
  Preconditions: Every element of pairs has length exactly 2 and len(pairs) ≤ 1000; the integer entries may be arbitrary 64-bit integers. -/
theorem spec_2 (pairs : Slice PairVec)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hlen_le : (pairList pairs).length ≤ 1000) :
    ∃ r : Std.I64, Aegis.FindLongestChain.find_longest_chain pairs = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (pairs : Slice PairVec)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hlen_le : (pairList pairs).length ≤ 1000), ∃ r : Std.I64, Aegis.FindLongestChain.find_longest_chain pairs = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 ≤ r ≤ len(pairs).
  Preconditions: Every element of pairs has length exactly 2 and len(pairs) ≤ 1000; the integer entries may be arbitrary 64-bit integers. -/
theorem spec_3 (pairs : Slice PairVec)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hlen_le : (pairList pairs).length ≤ 1000) :
    ∀ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r →
        0 ≤ r.val ∧ r.val ≤ ((pairList pairs).length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (pairs : Slice PairVec)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hlen_le : (pairList pairs).length ≤ 1000), ∀ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r →
        0 ≤ r.val ∧ r.val ≤ ((pairList pairs).length : ℤ)) := by
  sorry

/-- The function returns the result r = 1.
  Preconditions: len(pairs) = 1 and pairs[0] has length exactly 2. -/
theorem spec_4 (pairs : Slice PairVec)
    (hlen : (pairList pairs).length = 1)
    (hlen2 : AllPairsLen2 (pairList pairs)) :
    ∃ r : Std.I64, Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧ r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (pairs : Slice PairVec)
    (hlen : (pairList pairs).length = 1)
    (hlen2 : AllPairsLen2 (pairList pairs)), ∃ r : Std.I64, Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result r, and r = 2 if (pairs[0][1] < pairs[1][0] or pairs[1][1] < pairs[0][0]); otherwise r = 1.
  Preconditions: len(pairs) = 2; both pairs[0] and pairs[1] have length exactly 2; for i ∈ {0,1}, -1000 ≤ pairs[i][0] < pairs[i][1] ≤ 1000. -/
theorem spec_5 (pairs : Slice PairVec)
    (hlen : (pairList pairs).length = 2)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hbo : BoundedOrdered (pairList pairs)) :
    ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧
        (if EndAt (pairList pairs) 0 < StartAt (pairList pairs) 1 ∨
            EndAt (pairList pairs) 1 < StartAt (pairList pairs) 0 then
          r.val = 2
        else r.val = 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (pairs : Slice PairVec)
    (hlen : (pairList pairs).length = 2)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hbo : BoundedOrdered (pairList pairs)), ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧
        (if EndAt (pairList pairs) 0 < StartAt (pairList pairs) 1 ∨
            EndAt (pairList pairs) 1 < StartAt (pairList pairs) 0 then
          r.val = 2
        else r.val = 1)) := by
  sorry

/-- The function returns a result r, and there exist pairwise distinct indices i_0, ..., i_{r-1} in {0, ..., len(pairs)-1} such that pairs[i_t][1] < pairs[i_{t+1}][0] for every t with 0 ≤ t < r-1.
  Preconditions: Every element of pairs has length exactly 2; 1 ≤ len(pairs) ≤ 1000; for every i with 0 ≤ i < len(pairs), -1000 ≤ pairs[i][0] < pairs[i][1] ≤ 1000. -/
theorem spec_6 (pairs : Slice PairVec)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hlen_ge : 1 ≤ (pairList pairs).length)
    (hlen_le : (pairList pairs).length ≤ 1000)
    (hbo : BoundedOrdered (pairList pairs)) :
    ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧ Achievable (pairList pairs) r.val.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (pairs : Slice PairVec)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hlen_ge : 1 ≤ (pairList pairs).length)
    (hlen_le : (pairList pairs).length ≤ 1000)
    (hbo : BoundedOrdered (pairList pairs)), ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧ Achievable (pairList pairs) r.val.toNat) := by
  sorry

/-- The function returns a result r, and for every k ≥ 0 and every sequence of pairwise distinct indices i_0, ..., i_{k-1} in {0, ..., len(pairs)-1} satisfying pairs[i_t][1] < pairs[i_{t+1}][0] for all 0 ≤ t < k-1, we have k ≤ r.
  Preconditions: Every element of pairs has length exactly 2; 1 ≤ len(pairs) ≤ 1000; for every i with 0 ≤ i < len(pairs), -1000 ≤ pairs[i][0] < pairs[i][1] ≤ 1000. -/
theorem spec_7 (pairs : Slice PairVec)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hlen_ge : 1 ≤ (pairList pairs).length)
    (hlen_le : (pairList pairs).length ≤ 1000)
    (hbo : BoundedOrdered (pairList pairs)) :
    ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧
        ∀ k : ℕ, Achievable (pairList pairs) k → k ≤ r.val.toNat := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (pairs : Slice PairVec)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hlen_ge : 1 ≤ (pairList pairs).length)
    (hlen_le : (pairList pairs).length ≤ 1000)
    (hbo : BoundedOrdered (pairList pairs)), ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧
        ∀ k : ℕ, Achievable (pairList pairs) k → k ≤ r.val.toNat) := by
  sorry

/-- If the function returns r on input pairs and r' on input pairs', then r = r'.
  Preconditions: pairs and pairs' are slices of two-element vectors, each of length n with 0 ≤ n ≤ 1000; every entry of every pair lies in [-1000, 1000]; for every i with 0 ≤ i < n, pairs[i][0] < pairs[i][1] (and hence also pairs'[i][0] < pairs'[i][1]); there is a bijection f from {0, ..., n-1} to itself such that pairs'[f(i)] = pairs[i] for every i. -/
theorem spec_8 (pairs pairs' : Slice PairVec) (n : ℕ)
    (hlen : (pairList pairs).length = n)
    (hlen' : (pairList pairs').length = n)
    (hn_nonneg : 0 ≤ n)
    (hn_le : n ≤ 1000)
    (hrange : EntriesInRange (pairList pairs))
    (hrange' : EntriesInRange (pairList pairs'))
    (hproper : ProperIntervals (pairList pairs))
    (hproper' : ProperIntervals (pairList pairs'))
    (hperm : ∃ σ : ℕ → ℕ,
      BijectionOn n σ ∧ ∀ i, i < n → (pairList pairs')[σ i]! = (pairList pairs)[i]!) :
    ∀ r r' : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r →
        Aegis.FindLongestChain.find_longest_chain pairs' = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (pairs pairs' : Slice PairVec) (n : ℕ)
    (hlen : (pairList pairs).length = n)
    (hlen' : (pairList pairs').length = n)
    (hn_nonneg : 0 ≤ n)
    (hn_le : n ≤ 1000)
    (hrange : EntriesInRange (pairList pairs))
    (hrange' : EntriesInRange (pairList pairs'))
    (hproper : ProperIntervals (pairList pairs))
    (hproper' : ProperIntervals (pairList pairs'))
    (hperm : ∃ σ : ℕ → ℕ,
      BijectionOn n σ ∧ ∀ i, i < n → (pairList pairs')[σ i]! = (pairList pairs)[i]!), ∀ r r' : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r →
        Aegis.FindLongestChain.find_longest_chain pairs' = ok r' → r.val = r'.val) := by
  sorry

/-- If the function returns r on input pairs and r' on input pairs', then r ≤ r'.
  Preconditions: pairs and pairs' are slices of two-element vectors; len(pairs) ≤ 1000, len(pairs') ≤ 1000; every entry lies in [-1000, 1000]; pairs is a subsequence of pairs', meaning there exist indices j_0 < j_1 < ... < j_{len(pairs)-1} in {0, ..., len(pairs')-1} such that pairs'[j_i] = pairs[i] for every i. -/
theorem spec_9 (pairs pairs' : Slice PairVec)
    (hlen_le : (pairList pairs).length ≤ 1000)
    (hlen_le' : (pairList pairs').length ≤ 1000)
    (hrange : EntriesInRange (pairList pairs))
    (hrange' : EntriesInRange (pairList pairs'))
    (hsub : IsSubseqOf (pairList pairs) (pairList pairs')) :
    ∀ r r' : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r →
        Aegis.FindLongestChain.find_longest_chain pairs' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (pairs pairs' : Slice PairVec)
    (hlen_le : (pairList pairs).length ≤ 1000)
    (hlen_le' : (pairList pairs').length ≤ 1000)
    (hrange : EntriesInRange (pairList pairs))
    (hrange' : EntriesInRange (pairList pairs'))
    (hsub : IsSubseqOf (pairList pairs) (pairList pairs')), ∀ r r' : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r →
        Aegis.FindLongestChain.find_longest_chain pairs' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- The function returns the result r = n.
  Preconditions: len(pairs) = n with 1 ≤ n ≤ 1000; every pair has length exactly 2; every entry lies in [-1000, 1000]; for every i, pairs[i][0] < pairs[i][1]; for every i with 0 ≤ i < n-1, pairs[i][1] < pairs[i+1][0]. -/
theorem spec_10 (pairs : Slice PairVec) (n : ℕ)
    (hlen : (pairList pairs).length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 1000)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hrange : EntriesInRange (pairList pairs))
    (hproper : ProperIntervals (pairList pairs))
    (hsorted : ∀ i : ℕ, i + 1 < n →
      EndAt (pairList pairs) i < StartAt (pairList pairs) (i + 1)) :
    ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧ r.val = (n : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (pairs : Slice PairVec) (n : ℕ)
    (hlen : (pairList pairs).length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 1000)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hrange : EntriesInRange (pairList pairs))
    (hproper : ProperIntervals (pairList pairs))
    (hsorted : ∀ i : ℕ, i + 1 < n →
      EndAt (pairList pairs) i < StartAt (pairList pairs) (i + 1)), ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧ r.val = (n : ℤ)) := by
  sorry

/-- The function returns a result r, and r ≤ D, where D is the number of distinct two-element vectors among the entries of pairs (that is, the cardinality of the set {pairs[i] | 0 ≤ i < n}).
  Preconditions: len(pairs) = n with 1 ≤ n ≤ 1000; every pair has length exactly 2; every entry lies in [-1000, 1000]; for every i, pairs[i][0] < pairs[i][1]. -/
theorem spec_11 (pairs : Slice PairVec) (n : ℕ)
    (hlen : (pairList pairs).length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 1000)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hrange : EntriesInRange (pairList pairs))
    (hproper : ProperIntervals (pairList pairs)) :
    ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧
        r.val ≤ ((numDistinct (pairList pairs) : ℕ) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (pairs : Slice PairVec) (n : ℕ)
    (hlen : (pairList pairs).length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 1000)
    (hlen2 : AllPairsLen2 (pairList pairs))
    (hrange : EntriesInRange (pairList pairs))
    (hproper : ProperIntervals (pairList pairs)), ∃ r : Std.I64,
      Aegis.FindLongestChain.find_longest_chain pairs = ok r ∧
        r.val ≤ ((numDistinct (pairList pairs) : ℕ) : ℤ)) := by
  sorry

end AegisSpec.FindLongestChain
