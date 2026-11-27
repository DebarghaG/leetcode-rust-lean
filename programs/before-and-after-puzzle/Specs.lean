import Aegis.BeforeAndAfterPuzzles.Code.Funs

/-!
# Specifications of `Aegis.BeforeAndAfterPuzzles.before_and_after_puzzles`

LeetCode problem `before-and-after-puzzle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.BeforeAndAfterPuzzles

open Aegis.BeforeAndAfterPuzzles

def toBytes (p : alloc.vec.Vec Std.U8) : List ℕ := p.val.map (fun b => b.val)

def phraseBytes (phrases : Slice (alloc.vec.Vec Std.U8)) (i : ℕ) : List ℕ :=
  ((phrases.val[i]?).map toBytes).getD []

def outBytes (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) : List (List ℕ) :=
  r.val.map toBytes

def IsLowerLetterVal (b : ℕ) : Prop := 97 ≤ b ∧ b ≤ 122

def IsPhraseByteVal (b : ℕ) : Prop := b = 32 ∨ IsLowerLetterVal b

def NoConsecutiveSpaces : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => ¬ (a = 32 ∧ b = 32) ∧ NoConsecutiveSpaces (b :: rest)

def IsPhraseShape (l : List ℕ) : Prop :=
  (∀ b, b ∈ l → IsPhraseByteVal b) ∧
  l.head? ≠ some 32 ∧
  l.getLast? ≠ some 32 ∧
  NoConsecutiveSpaces l

def IsValidPhraseList (l : List ℕ) : Prop :=
  1 ≤ l.length ∧ l.length ≤ 100 ∧ IsPhraseShape l

def IsValidPhrase (p : alloc.vec.Vec Std.U8) : Prop := IsValidPhraseList (toBytes p)

def IsValidInput (phrases : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  1 ≤ phrases.val.length ∧ phrases.val.length ≤ 100 ∧
  ∀ p, p ∈ phrases.val → IsValidPhrase p

def firstWord (l : List ℕ) : List ℕ := l.takeWhile (fun b => b != 32)

def lastWord (l : List ℕ) : List ℕ := (l.reverse.takeWhile (fun b => b != 32)).reverse

def suffixAfterFirstWord (l : List ℕ) : List ℕ := l.dropWhile (fun b => b != 32)

def merge (p q : List ℕ) : List ℕ := p ++ suffixAfterFirstWord q

def lexLt : List ℕ → List ℕ → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a :: a', b :: b' => a < b ∨ (a = b ∧ lexLt a' b')

def lexLe (l₁ l₂ : List ℕ) : Prop := lexLt l₁ l₂ ∨ l₁ = l₂

def StrictlySorted : List (List ℕ) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => lexLt a b ∧ StrictlySorted (b :: rest)

def SortedNondecreasing : List (List ℕ) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => lexLe a b ∧ SortedNondecreasing (b :: rest)

def IsMergeCandidate (phrases : Slice (alloc.vec.Vec Std.U8)) (s : List ℕ) : Prop :=
  ∃ i j, i < phrases.val.length ∧ j < phrases.val.length ∧ i ≠ j ∧
    lastWord (phraseBytes phrases i) = firstWord (phraseBytes phrases j) ∧
    s = merge (phraseBytes phrases i) (phraseBytes phrases j)

def HasMatch (phrases : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  ∃ i j, i < phrases.val.length ∧ j < phrases.val.length ∧ i ≠ j ∧
    lastWord (phraseBytes phrases i) = firstWord (phraseBytes phrases j)

def Occurs (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (s : List ℕ) : Prop :=
  s ∈ outBytes r

def matchPairCount (phrases : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
  ((List.range phrases.val.length).product (List.range phrases.val.length)).countP
    (fun ij => decide (ij.1 ≠ ij.2 ∧
      lastWord (phraseBytes phrases ij.1) = firstWord (phraseBytes phrases ij.2)))

def IsPermutation (phrases phrases₂ : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  ∀ x : List ℕ, (phrases.val.map toBytes).count x = (phrases₂.val.map toBytes).count x

/-- For a valid phrase p, let firstWord(p) be p[0..f], where f = min{ g | 0<=g<len(p) and p[g]=32 } if this set is nonempty, otherwise f=len(p). Let lastWord(p) be p[l..len(p)], where l=0 if p has no space, otherwise l=1+max{ g | 0<=g<len(p) and p[g]=32 }. For a valid phrase q, let suffixAfterFirstWord(q) be q[f..len(q)] where f is as for firstWord(q). For valid phrases p,q, let merge(p,q) be the concatenation of p and suffixAfterFirstWord(q). The function returns a result r (so it does not fail) and, with this notation, for every byte array s, s occurs in r (meaning there exists k with 0<=k<len(r) and r[k]=s) if and only if there exist indices i,j with 0<=i<len(phrases), 0<=j<len(phrases), i != j, lastWord(phrases[i])=firstWord(phrases[j]), and s=merge(phrases[i],phrases[j]); moreover, for every k with 0<=k<len(r)-1, r[k] < r[k+1] in standard lexicographic order on byte arrays (a proper prefix is smaller than the longer array; otherwise the first differing byte decides by its unsigned value).
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_1 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      before_and_after_puzzles phrases = ok r ∧
      (∀ s : List ℕ, Occurs r s ↔ IsMergeCandidate phrases s) ∧
      StrictlySorted (outBytes r) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      before_and_after_puzzles phrases = ok r ∧
      (∀ s : List ℕ, Occurs r s ↔ IsMergeCandidate phrases s) ∧
      StrictlySorted (outBytes r)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access memory out of bounds for any input satisfying the preconditions.
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_2 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0<=k<len(r), there exist indices i,j with 0<=i<len(phrases), 0<=j<len(phrases), i != j, such that the last word of phrases[i] equals the first word of phrases[j] and r[k] is the merge of phrases[i] and phrases[j], where the merge is phrases[i] followed by phrases[j] with its first word removed (equivalently, phrases[i] concatenated with phrases[j] starting immediately after the first word of phrases[j]).
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_3 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ s, s ∈ outBytes r → IsMergeCandidate phrases s := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ s, s ∈ outBytes r → IsMergeCandidate phrases s) := by
  sorry

/-- Whenever the function returns a result r, for every i,j with 0<=i<len(phrases), 0<=j<len(phrases), and i != j, if the last word of phrases[i] equals the first word of phrases[j], then there exists k with 0<=k<len(r) such that r[k] is the merge of phrases[i] and phrases[j], defined as phrases[i] followed by phrases[j] with its first word removed.
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_4 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ i j, i < phrases.val.length → j < phrases.val.length → i ≠ j →
        lastWord (phraseBytes phrases i) = firstWord (phraseBytes phrases j) →
        ∃ s, s ∈ outBytes r ∧
          s = merge (phraseBytes phrases i) (phraseBytes phrases j) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ i j, i < phrases.val.length → j < phrases.val.length → i ≠ j →
        lastWord (phraseBytes phrases i) = firstWord (phraseBytes phrases j) →
        ∃ s, s ∈ outBytes r ∧
          s = merge (phraseBytes phrases i) (phraseBytes phrases j)) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0<=k<len(r)-1, r[k] <= r[k+1] in standard lexicographic order on byte arrays (a proper prefix is smaller than the longer array; otherwise the first differing byte decides by its unsigned value).
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_5 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      SortedNondecreasing (outBytes r) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      SortedNondecreasing (outBytes r)) := by
  sorry

/-- Whenever the function returns a result r, for every k,l with 0<=k<len(r) and 0<=l<len(r), if r[k]=r[l] then k=l.
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_6 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      (outBytes r).Nodup := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      (outBytes r).Nodup) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0<=k<len(r), 1 <= len(r[k]) <= 199.
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_7 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ s, s ∈ outBytes r → 1 ≤ s.length ∧ s.length ≤ 199 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ s, s ∈ outBytes r → 1 ≤ s.length ∧ s.length ≤ 199) := by
  sorry

/-- Whenever the function returns a result r, len(r) is at most the number of ordered pairs (i,j) such that 0<=i<len(phrases), 0<=j<len(phrases), i != j, and the last word of phrases[i] equals the first word of phrases[j].
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_8 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      (outBytes r).length ≤ matchPairCount phrases := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      (outBytes r).length ≤ matchPairCount phrases) := by
  sorry

/-- Whenever the function returns a result r, if for every i,j with 0<=i<len(phrases), 0<=j<len(phrases), and i != j, the last word of phrases[i] is not equal to the first word of phrases[j], then len(r)=0.
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_9 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ¬ HasMatch phrases → (outBytes r).length = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ¬ HasMatch phrases → (outBytes r).length = 0) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0<=k<len(r), r[k] is a valid phrase: len(r[k])>=1; every byte of r[k] is either 32 or a lowercase ASCII letter with code 97..122; r[k][0] != 32; r[k][len(r[k])-1] != 32; and for every t with 0<=t<len(r[k])-1, not (r[k][t]=32 and r[k][t+1]=32).
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_10 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ s, s ∈ outBytes r → 1 ≤ s.length ∧ IsPhraseShape s := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ s, s ∈ outBytes r → 1 ≤ s.length ∧ IsPhraseShape s) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0<=k<len(r), there exist indices i,j with 0<=i<len(phrases), 0<=j<len(phrases), i != j, such that lastWord(phrases[i]) = firstWord(phrases[j]) and r[k] = merge(phrases[i], phrases[j]), where merge(p,q) is p followed by q with q's first word removed (equivalently, p concatenated with q starting immediately after q's first word). Moreover, for every i,j that satisfy these same conditions (i != j, lastWord(phrases[i]) = firstWord(phrases[j]), and r[k] = merge(phrases[i], phrases[j])), firstWord(r[k]) = firstWord(phrases[i]) and lastWord(r[k]) = lastWord(phrases[j]); here firstWord and lastWord are applied to r[k] using the same definition, and r[k] is a valid phrase because it is such a merge.
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_11 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ s, s ∈ outBytes r →
        IsMergeCandidate phrases s ∧
        ∀ i j, i < phrases.val.length → j < phrases.val.length → i ≠ j →
          lastWord (phraseBytes phrases i) = firstWord (phraseBytes phrases j) →
          s = merge (phraseBytes phrases i) (phraseBytes phrases j) →
          firstWord s = firstWord (phraseBytes phrases i) ∧
            lastWord s = lastWord (phraseBytes phrases j) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ s, s ∈ outBytes r →
        IsMergeCandidate phrases s ∧
        ∀ i j, i < phrases.val.length → j < phrases.val.length → i ≠ j →
          lastWord (phraseBytes phrases i) = firstWord (phraseBytes phrases j) →
          s = merge (phraseBytes phrases i) (phraseBytes phrases j) →
          firstWord s = firstWord (phraseBytes phrases i) ∧
            lastWord s = lastWord (phraseBytes phrases j)) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0<=k<len(r), for every i,j with 0<=i<len(phrases), 0<=j<len(phrases), i != j, if the last word of phrases[i] equals the first word of phrases[j] and r[k] is the merge of phrases[i] and phrases[j], then len(r[k]) = len(phrases[i]) + len(phrases[j]) - len(firstWord(phrases[j])), where firstWord(phrases[j]) is the first word of phrases[j].
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_12 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ s, s ∈ outBytes r →
        ∀ i j, i < phrases.val.length → j < phrases.val.length → i ≠ j →
          lastWord (phraseBytes phrases i) = firstWord (phraseBytes phrases j) →
          s = merge (phraseBytes phrases i) (phraseBytes phrases j) →
          s.length = (phraseBytes phrases i).length + (phraseBytes phrases j).length -
            (firstWord (phraseBytes phrases j)).length := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      ∀ s, s ∈ outBytes r →
        ∀ i j, i < phrases.val.length → j < phrases.val.length → i ≠ j →
          lastWord (phraseBytes phrases i) = firstWord (phraseBytes phrases j) →
          s = merge (phraseBytes phrases i) (phraseBytes phrases j) →
          s.length = (phraseBytes phrases i).length + (phraseBytes phrases j).length -
            (firstWord (phraseBytes phrases j)).length) := by
  sorry

/-- Whenever before_and_after_puzzles(phrases) returns a result r and before_and_after_puzzles(phrases2) returns a result r2, we have r = r2 (the two byte-array lists are equal elementwise).
  Preconditions: len(phrases) is between 1 and 100 inclusive and every element of phrases is a valid phrase as described in S1 (bytes are spaces or lowercase ASCII letters 97..122, no leading or trailing spaces, no consecutive spaces, lengths 1..100). Also phrases2 is a list of valid phrases with len(phrases2) between 1 and 100 inclusive, and phrases2 is a permutation of phrases: for every byte array x, the number of indices i with 0<=i<len(phrases) and phrases[i]=x equals the number of indices j with 0<=j<len(phrases2) and phrases2[j]=x. -/
theorem spec_13 (phrases phrases₂ : Slice (alloc.vec.Vec Std.U8))
    (hvalid : IsValidInput phrases) (hvalid₂ : IsValidInput phrases₂)
    (hperm : IsPermutation phrases phrases₂) :
    ∀ r r₂ : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      before_and_after_puzzles phrases = ok r → before_and_after_puzzles phrases₂ = ok r₂ →
      outBytes r = outBytes r₂ := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (phrases phrases₂ : Slice (alloc.vec.Vec Std.U8))
    (hvalid : IsValidInput phrases) (hvalid₂ : IsValidInput phrases₂)
    (hperm : IsPermutation phrases phrases₂), ∀ r r₂ : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      before_and_after_puzzles phrases = ok r → before_and_after_puzzles phrases₂ = ok r₂ →
      outBytes r = outBytes r₂) := by
  sorry

/-- Whenever the function returns a result r, if there exist i,j with 0<=i<len(phrases), 0<=j<len(phrases), i != j, and the last word of phrases[i] equals the first word of phrases[j], then len(r) > 0.
  Preconditions: len(phrases) is between 1 and 100 inclusive. For every i with 0 <= i < len(phrases), p = phrases[i] is a valid phrase: 1 <= len(p) <= 100; every byte p[t] with 0 <= t < len(p) is either 32 (space) or a lowercase ASCII letter with code 97..122; p[0] != 32; p[len(p)-1] != 32; and for every t with 0 <= t < len(p)-1, not (p[t] = 32 and p[t+1] = 32). Words in a phrase are its maximal non-space substrings; the first word is the prefix before the first space, or the whole phrase if there is no space; the last word is the suffix after the last space, or the whole phrase if there is no space. -/
theorem spec_14 (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      HasMatch phrases → 0 < (outBytes r).length := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (phrases : Slice (alloc.vec.Vec Std.U8)) (hvalid : IsValidInput phrases), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), before_and_after_puzzles phrases = ok r →
      HasMatch phrases → 0 < (outBytes r).length) := by
  sorry

end AegisSpec.BeforeAndAfterPuzzles
