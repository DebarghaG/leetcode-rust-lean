import Aegis.NumMatchingSubseq.Code.Funs

/-!
# Specifications of `Aegis.NumMatchingSubseq.num_matching_subseq`

LeetCode problem `number-of-matching-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.NumMatchingSubseq
open Classical

namespace AegisSpec.NumMatchingSubseq

def BytesInRange (l : List Std.U8) : Prop :=
  ∀ b ∈ l, 97 ≤ b.val ∧ b.val ≤ 122

def WordsSizeOK (ws : List (alloc.vec.Vec Std.U8)) : Prop :=
  ∀ w ∈ ws, 1 ≤ w.val.length ∧ w.val.length ≤ 50

def IsSubseq (w s : List Std.U8) : Prop :=
  ∃ f : Fin w.length → Fin s.length,
    (∀ k l : Fin w.length, k < l → f k < f l) ∧
      ∀ k : Fin w.length, s.get (f k) = w.get k

def OccursByte (b : Std.U8) (s : List Std.U8) : Prop :=
  ∃ (j : Nat) (hj : j < s.length), s.get ⟨j, hj⟩ = b

def AllBytesOccur (w s : List Std.U8) : Prop :=
  ∀ b ∈ w, OccursByte b s

def BytewiseEq (w s : List Std.U8) : Prop :=
  ∀ (k : Nat) (hk : k < s.length) (hkw : k < w.length), w.get ⟨k, hkw⟩ = s.get ⟨k, hk⟩

def IsPermutationOf {α : Type} (l' l : List α) : Prop :=
  ∃ p : Fin l'.length → Fin l.length,
    Function.Bijective p ∧ ∀ i : Fin l'.length, l'.get i = l.get (p i)

def deleteAt {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, n + 1 => x :: deleteAt xs n

noncomputable def countMatching
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) : Nat :=
  (words.val.filter (fun w => decide (IsSubseq w.val s.val))).length

noncomputable def countLenLe
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) : Nat :=
  (words.val.filter (fun w => decide (w.val.length ≤ s.val.length))).length

noncomputable def countMatchingEqLen
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) : Nat :=
  (words.val.filter (fun w => decide (w.val.length = s.val.length ∧ IsSubseq w.val s.val))).length

noncomputable def countEqLenWords
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) : Nat :=
  (words.val.filter (fun w => decide (w.val.length = s.val.length ∧ w.val = s.val))).length

noncomputable def countMatchingLenOne
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) : Nat :=
  (words.val.filter (fun w => decide (w.val.length = 1 ∧ IsSubseq w.val s.val))).length

noncomputable def countLenOneOccur
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) : Nat :=
  (words.val.filter (fun w => decide (w.val.length = 1 ∧ AllBytesOccur w.val s.val))).length

noncomputable def countAllBytesOccur
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) : Nat :=
  (words.val.filter (fun w => decide (AllBytesOccur w.val s.val))).length

def firstOcc (b : Std.U8) : List Std.U8 → Option Nat
  | [] => none
  | x :: xs => if x = b then some 0 else (firstOcc b xs).map (· + 1)

def greedyPositions : List Std.U8 → List Std.U8 → Nat → Option (List Nat)
  | [], _, _ => some []
  | b :: rest, s, p =>
    match firstOcc b (s.drop p) with
    | none => none
    | some k =>
      match greedyPositions rest s (p + k + 1) with
      | none => none
      | some ps => some ((p + k) :: ps)

/-- Whenever the function returns a result r, r equals the number of indices i with 0 <= i < len(words) such that words[i] is a subsequence of s. Here words[i] is a subsequence of s iff there exist indices 0 <= j_0 < ... < j_{len(words[i])-1} < len(s) with s[j_k] = words[i][k] for every k with 0 <= k < len(words[i]). Duplicate entries in words are counted once per index.
  Preconditions: len(s) >= 1, len(s) <= 50000, len(words) >= 1, len(words) <= 5000, and for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50; every byte of s and of every words[i] is between 97 and 122 inclusive. -/
theorem spec_1
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r) :
    r.val = (countMatching s words : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r), r.val = (countMatching s words : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail. In particular, no arithmetic overflow occurs, because the returned count is at most len(words) <= 5000.
  Preconditions: len(s) >= 1, len(s) <= 50000, len(words) >= 1, len(words) <= 5000, and for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50; every byte of s and of every words[i] is between 97 and 122 inclusive. -/
theorem spec_2
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val) :
    ∃ r : Std.I64, num_matching_subseq s words = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val), ∃ r : Std.I64, num_matching_subseq s words = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(words).
  Preconditions: len(s) >= 1, len(s) <= 50000, len(words) >= 1, len(words) <= 5000, and for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50; every byte of s and of every words[i] is between 97 and 122 inclusive. -/
theorem spec_3
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r) :
    0 ≤ r.val ∧ r.val ≤ (words.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r), 0 ≤ r.val ∧ r.val ≤ (words.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r is at most the number of indices i with 0 <= i < len(words) and len(words[i]) <= len(s).
  Preconditions: len(s) >= 1, len(s) <= 50000, len(words) >= 1, len(words) <= 5000, and for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50; every byte of s and of every words[i] is between 97 and 122 inclusive. -/
theorem spec_4
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r) :
    r.val ≤ (countLenLe s words : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r), r.val ≤ (countLenLe s words : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = len(words) if and only if for every i with 0 <= i < len(words), words[i] is a subsequence of s. Subsequence means there exist indices 0 <= j_0 < ... < j_{len(words[i])-1} < len(s) with s[j_k] = words[i][k] for every k with 0 <= k < len(words[i]).
  Preconditions: len(s) >= 1, len(s) <= 50000, len(words) >= 1, len(words) <= 5000, and for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50; every byte of s and of every words[i] is between 97 and 122 inclusive. -/
theorem spec_5
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r) :
    r.val = (words.val.length : Int) ↔ ∀ w ∈ words.val, IsSubseq w.val s.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r), r.val = (words.val.length : Int) ↔ ∀ w ∈ words.val, IsSubseq w.val s.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is no index i with 0 <= i < len(words) such that words[i] is a subsequence of s. Subsequence means there exist indices 0 <= j_0 < ... < j_{len(words[i])-1} < len(s) with s[j_k] = words[i][k] for every k with 0 <= k < len(words[i]).
  Preconditions: len(s) >= 1, len(s) <= 50000, len(words) >= 1, len(words) <= 5000, and for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50; every byte of s and of every words[i] is between 97 and 122 inclusive. -/
theorem spec_6
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r) :
    r.val = 0 ↔ ¬ ∃ w ∈ words.val, IsSubseq w.val s.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r), r.val = 0 ↔ ¬ ∃ w ∈ words.val, IsSubseq w.val s.val) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exists an index i with 0 <= i < len(words) and indices 0 <= j_0 < ... < j_{len(words[i])-1} < len(s) such that s[j_k] = words[i][k] for every k with 0 <= k < len(words[i]).
  Preconditions: len(s) >= 1, len(s) <= 50000, len(words) >= 1, len(words) <= 5000, and for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50; every byte of s and of every words[i] is between 97 and 122 inclusive. -/
theorem spec_7
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r) :
    0 < r.val → ∃ w ∈ words.val, IsSubseq w.val s.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r), 0 < r.val → ∃ w ∈ words.val, IsSubseq w.val s.val) := by
  sorry

/-- Whenever the function returns a result r with r < len(words), there exists an index i with 0 <= i < len(words) such that words[i] is not a subsequence of s. Here words[i] is not a subsequence of s means there are no indices 0 <= j_0 < ... < j_{len(words[i])-1} < len(s) with s[j_k] = words[i][k] for every k with 0 <= k < len(words[i]).
  Preconditions: len(s) >= 1, len(s) <= 50000, len(words) >= 1, len(words) <= 5000, and for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50; every byte of s and of every words[i] is between 97 and 122 inclusive. -/
theorem spec_8
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r) :
    r.val < (words.val.length : Int) → ∃ w ∈ words.val, ¬ IsSubseq w.val s.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r), r.val < (words.val.length : Int) → ∃ w ∈ words.val, ¬ IsSubseq w.val s.val) := by
  sorry

/-- Whenever the function returns r for (s, words) and r' for (s, words'), we have r = r'.
  Preconditions: s and words satisfy: len(s) >= 1, len(s) <= 50000, len(words) >= 1, len(words) <= 5000, and for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50; every byte of s and of every words[i] is between 97 and 122 inclusive. The list words' also satisfies the same length and byte constraints, and words' is a permutation of words: len(words') = len(words) and there is a bijection p on {0,...,len(words)-1} with words'[i] = words[p(i)] for every i. -/
theorem spec_9
    (s : Slice Std.U8) (words words' : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (hw'_lower : 1 ≤ words'.val.length) (hw'_upper : words'.val.length ≤ 5000)
    (hwl' : WordsSizeOK words'.val)
    (hw'_bytes : ∀ w ∈ words'.val, BytesInRange w.val)
    (hperm : IsPermutationOf words'.val words.val)
    (r r' : Std.I64)
    (hr : num_matching_subseq s words = ok r)
    (hr' : num_matching_subseq s words' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (words words' : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (hw'_lower : 1 ≤ words'.val.length) (hw'_upper : words'.val.length ≤ 5000)
    (hwl' : WordsSizeOK words'.val)
    (hw'_bytes : ∀ w ∈ words'.val, BytesInRange w.val)
    (hperm : IsPermutationOf words'.val words.val)
    (r r' : Std.I64)
    (hr : num_matching_subseq s words = ok r)
    (hr' : num_matching_subseq s words' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns r for (s, words) and r' for (s, words'), if for every i with 0 <= i < len(words), words[i] is a subsequence of s if and only if words'[i] is a subsequence of s, then r = r'. Subsequence is defined by the existence of strictly increasing matching indices in s.
  Preconditions: s, words, and words' all satisfy: len(s) >= 1, len(s) <= 50000, len(words) >= 1, len(words) <= 5000, len(words') >= 1, len(words') <= 5000, and all their word lengths are between 1 and 50; every byte of s and of every words[i] and words'[i] is between 97 and 122 inclusive. Also len(words') = len(words). -/
theorem spec_10
    (s : Slice Std.U8) (words words' : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (hw'_lower : 1 ≤ words'.val.length) (hw'_upper : words'.val.length ≤ 5000)
    (hwl' : WordsSizeOK words'.val)
    (hw'_bytes : ∀ w ∈ words'.val, BytesInRange w.val)
    (hs_bytes : BytesInRange s.val)
    (hlen : words'.val.length = words.val.length)
    (hiff : ∀ (i : Nat) (hi : i < words.val.length) (hi' : i < words'.val.length),
      IsSubseq (words.val.get ⟨i, hi⟩).val s.val ↔
        IsSubseq (words'.val.get ⟨i, hi'⟩).val s.val)
    (r r' : Std.I64)
    (hr : num_matching_subseq s words = ok r)
    (hr' : num_matching_subseq s words' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (words words' : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (hw'_lower : 1 ≤ words'.val.length) (hw'_upper : words'.val.length ≤ 5000)
    (hwl' : WordsSizeOK words'.val)
    (hw'_bytes : ∀ w ∈ words'.val, BytesInRange w.val)
    (hs_bytes : BytesInRange s.val)
    (hlen : words'.val.length = words.val.length)
    (hiff : ∀ (i : Nat) (hi : i < words.val.length) (hi' : i < words'.val.length),
      IsSubseq (words.val.get ⟨i, hi⟩).val s.val ↔
        IsSubseq (words'.val.get ⟨i, hi'⟩).val s.val)
    (r r' : Std.I64)
    (hr : num_matching_subseq s words = ok r)
    (hr' : num_matching_subseq s words' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns r for (s, words) and r' for (s, words'), if words[i] is a subsequence of s then r = r' + 1, and otherwise r = r'. Subsequence is defined by the existence of strictly increasing matching indices in s.
  Preconditions: s and words satisfy len(s) >= 1, len(s) <= 50000, len(words) >= 2, len(words) <= 5000, and every word length is between 1 and 50; every byte of s and of every words[i] is between 97 and 122 inclusive. Also 0 <= i < len(words), and words' is obtained from words by deleting index i: len(words') = len(words) - 1, words'[j] = words[j] for j < i, and words'[j] = words[j+1] for j >= i. -/
theorem spec_11
    (s : Slice Std.U8) (words words' : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_two : 2 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (i : Nat) (hi : i < words.val.length)
    (hdel : words'.val = deleteAt words.val i)
    (r r' : Std.I64)
    (hr : num_matching_subseq s words = ok r)
    (hr' : num_matching_subseq s words' = ok r') :
    (IsSubseq (words.val.get ⟨i, hi⟩).val s.val → r.val = r'.val + 1) ∧
      (¬ IsSubseq (words.val.get ⟨i, hi⟩).val s.val → r.val = r'.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (words words' : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_two : 2 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (i : Nat) (hi : i < words.val.length)
    (hdel : words'.val = deleteAt words.val i)
    (r r' : Std.I64)
    (hr : num_matching_subseq s words = ok r)
    (hr' : num_matching_subseq s words' = ok r'), (IsSubseq (words.val.get ⟨i, hi⟩).val s.val → r.val = r'.val + 1) ∧
      (¬ IsSubseq (words.val.get ⟨i, hi⟩).val s.val → r.val = r'.val)) := by
  sorry

/-- Whenever the function returns r for (s, words), r1 for (s, words1), and r2 for (s, words2), we have r = r1 + r2.
  Preconditions: s, words1, and words2 all satisfy the input constraints: len(s) >= 1, len(s) <= 50000, len(words1) >= 1, len(words1) <= 5000, len(words2) >= 1, len(words2) <= 5000, all word lengths are between 1 and 50, and all bytes are between 97 and 122 inclusive. Also words is the concatenation words1 ++ words2. -/
theorem spec_12
    (s : Slice Std.U8) (words words1 words2 : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hw1_lower : 1 ≤ words1.val.length) (hw1_upper : words1.val.length ≤ 5000)
    (hw2_lower : 1 ≤ words2.val.length) (hw2_upper : words2.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hwl1 : WordsSizeOK words1.val)
    (hwl2 : WordsSizeOK words2.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (hw1_bytes : ∀ w ∈ words1.val, BytesInRange w.val)
    (hw2_bytes : ∀ w ∈ words2.val, BytesInRange w.val)
    (hcat : words.val = words1.val ++ words2.val)
    (r r1 r2 : Std.I64)
    (hr : num_matching_subseq s words = ok r)
    (hr1 : num_matching_subseq s words1 = ok r1)
    (hr2 : num_matching_subseq s words2 = ok r2) :
    r.val = r1.val + r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (words words1 words2 : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hw1_lower : 1 ≤ words1.val.length) (hw1_upper : words1.val.length ≤ 5000)
    (hw2_lower : 1 ≤ words2.val.length) (hw2_upper : words2.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hwl1 : WordsSizeOK words1.val)
    (hwl2 : WordsSizeOK words2.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (hw1_bytes : ∀ w ∈ words1.val, BytesInRange w.val)
    (hw2_bytes : ∀ w ∈ words2.val, BytesInRange w.val)
    (hcat : words.val = words1.val ++ words2.val)
    (r r1 r2 : Std.I64)
    (hr : num_matching_subseq s words = ok r)
    (hr1 : num_matching_subseq s words1 = ok r1)
    (hr2 : num_matching_subseq s words2 = ok r2), r.val = r1.val + r2.val) := by
  sorry

/-- Whenever the function returns r for (s, words) and r' for (s', words), we have r <= r'. (Equivalently: every word that is a subsequence of s is also a subsequence of s', by transitivity of the subsequence relation.)
  Preconditions: s and s' with 1 <= len(s) <= 50000, 1 <= len(s') <= 50000 and all bytes of s and s' between 97 and 122; words with 1 <= len(words) <= 5000, 1 <= len(words[i]) <= 50 and all bytes between 97 and 122; and s is a subsequence of s', i.e. there are 0 <= k_0 < ... < k_{len(s)-1} < len(s') with s'[k_t] = s[t] for all 0 <= t < len(s). -/
theorem spec_13
    (s s' : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hs_bytes : BytesInRange s.val)
    (hs'_lower : 1 ≤ s'.val.length) (hs'_upper : s'.val.length ≤ 50000)
    (hs'_bytes : BytesInRange s'.val)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (hsub : IsSubseq s.val s'.val)
    (r r' : Std.I64)
    (hr : num_matching_subseq s words = ok r)
    (hr' : num_matching_subseq s' words = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s s' : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hs_bytes : BytesInRange s.val)
    (hs'_lower : 1 ≤ s'.val.length) (hs'_upper : s'.val.length ≤ 50000)
    (hs'_bytes : BytesInRange s'.val)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (hsub : IsSubseq s.val s'.val)
    (r r' : Std.I64)
    (hr : num_matching_subseq s words = ok r)
    (hr' : num_matching_subseq s' words = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(words), if some byte b with 97 <= b <= 122 occurs in words[i] but does not occur in s (there is no j with 0 <= j < len(s) and s[j] = b), then words[i] is not a subsequence of s; consequently r is at most the number of indices i such that every byte of words[i] occurs in s.
  Preconditions: len(s) >= 1, len(s) <= 50000, len(words) >= 1, len(words) <= 5000, and for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50; every byte of s and of every words[i] is between 97 and 122 inclusive. -/
theorem spec_14
    (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r) :
    (∀ (i : Nat) (hi : i < words.val.length),
        (∃ b ∈ (words.val.get ⟨i, hi⟩).val,
            ∀ (j : Nat) (hj : j < s.val.length), s.val.get ⟨j, hj⟩ ≠ b) →
          ¬ IsSubseq (words.val.get ⟨i, hi⟩).val s.val) ∧
      r.val ≤ (countAllBytesOccur s words : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 50000)
    (hw_lower : 1 ≤ words.val.length) (hw_upper : words.val.length ≤ 5000)
    (hwl : WordsSizeOK words.val)
    (hs_bytes : BytesInRange s.val)
    (hw_bytes : ∀ w ∈ words.val, BytesInRange w.val)
    (r : Std.I64) (hr : num_matching_subseq s words = ok r), (∀ (i : Nat) (hi : i < words.val.length),
        (∃ b ∈ (words.val.get ⟨i, hi⟩).val,
            ∀ (j : Nat) (hj : j < s.val.length), s.val.get ⟨j, hj⟩ ≠ b) →
          ¬ IsSubseq (words.val.get ⟨i, hi⟩).val s.val) ∧
      r.val ≤ (countAllBytesOccur s words : Int)) := by
  sorry

end AegisSpec.NumMatchingSubseq
