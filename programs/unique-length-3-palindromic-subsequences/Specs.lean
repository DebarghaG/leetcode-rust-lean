import Aegis.CountPalindromicSubsequence.Code.Funs

/-!
# Specifications of `Aegis.CountPalindromicSubsequence.count_palindromic_subsequence`

LeetCode problem `unique-length-3-palindromic-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountPalindromicSubsequence

noncomputable section

open Classical

open Aegis.CountPalindromicSubsequence (count_palindromic_subsequence)

def bytes (s : Slice Std.U8) : List Nat := s.val.map (fun c => c.val)

def validInput (s : Slice Std.U8) : Prop :=
  3 ≤ (bytes s).length ∧ (bytes s).length ≤ 100000 ∧ ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122

def IsFirstOcc (l : List Nat) (a f : Nat) : Prop :=
  l[f]? = some a ∧ ∀ i, i < f → l[i]? ≠ some a

def IsLastOcc (l : List Nat) (a L : Nat) : Prop :=
  l[L]? = some a ∧ ∀ i, L < i → l[i]? ≠ some a

def IsPal3Subseq (l : List Nat) (a b : Nat) : Prop :=
  ∃ (i j k : Nat), i < j ∧ j < k ∧ l[i]? = some a ∧ l[j]? = some b ∧ l[k]? = some a

def BetweenFirstLast (l : List Nat) (a b : Nat) : Prop :=
  ∃ (f L j : Nat), IsFirstOcc l a f ∧ IsLastOcc l a L ∧ f < j ∧ j < L ∧ l[j]? = some b

def HasPal3 (l : List Nat) : Prop :=
  ∃ (i j k a : Nat), i < j ∧ j < k ∧ l[i]? = some a ∧ l[k]? = some a

def NoGappedRepeat (l : List Nat) : Prop :=
  ∀ (i k a : Nat), i < k → l[i]? = some a → l[k]? = some a → k = i + 1

def IsReverseBytes (l l' : List Nat) : Prop :=
  l'.length = l.length ∧ ∀ i, i < l.length → l'[i]? = l[l.length - 1 - i]?

def IsSubsequence (l₁ l₂ : List Nat) : Prop := l₁.Sublist l₂

noncomputable def palCount (l : List Nat) : Nat :=
  (((Finset.Icc 97 122).product (Finset.Icc 97 122)).filter
      (fun p => IsPal3Subseq l p.1 p.2)).card

noncomputable def countFor (l : List Nat) (a : Nat) : Nat :=
  if ∃ f L, IsFirstOcc l a f ∧ IsLastOcc l a L ∧ f < L then
    ((Finset.Icc 97 122).filter (BetweenFirstLast l a)).card
  else 0

def distinctCount (l : List Nat) : Nat := l.toFinset.card

noncomputable def palTripleCount (l : List Nat) : Nat :=
  ((((Finset.range l.length).product (Finset.range l.length)).product
      (Finset.range l.length)).filter
    (fun q => q.1.1 < q.1.2 ∧ q.1.2 < q.2 ∧ l[q.1.1]? = l[q.2]?)).card

noncomputable def spacedCount (l : List Nat) : Nat :=
  ((Finset.Icc 97 122).filter
    (fun a => ∃ (i k : Nat), i < k ∧ i + 2 ≤ k ∧ l[i]? = some a ∧ l[k]? = some a)).card

/-- Let Count(s) be the number of distinct byte triples (a,b,c) such that a=c, 97 <= a <= 122, 97 <= b <= 122, and there exist indices i,j,k with 0 <= i < j < k < len(s), s[i]=a, s[j]=b, s[k]=c. The function returns a result r, and r = Count(s). Equivalently, r is the cardinality of the set of length-three palindromic strings a b a that are a subsequence of s; each distinct string is counted once even if it has several embeddings.
  Preconditions: 3 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_1 (s : Slice Std.U8) (hpre : validInput s) :
    ∃ r : Std.I64, count_palindromic_subsequence s = ok r ∧
      r.val = (palCount (bytes s) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (hpre : validInput s), ∃ r : Std.I64, count_palindromic_subsequence s = ok r ∧
      r.val = (palCount (bytes s) : Int)) := by
  sorry

/-- For every slice s satisfying the preconditions, the function returns a result r; it does not fail by panic, out-of-bounds access, or arithmetic overflow.
  Preconditions: 3 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice Std.U8) (hpre : validInput s) :
    ∃ r : Std.I64, count_palindromic_subsequence s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (hpre : validInput s), ∃ r : Std.I64, count_palindromic_subsequence s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 676.
  Preconditions: 3 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice Std.U8) (hpre : validInput s) :
    ∀ r : Std.I64, count_palindromic_subsequence s = ok r → 0 ≤ r.val ∧ r.val ≤ 676 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (hpre : validInput s), ∀ r : Std.I64, count_palindromic_subsequence s = ok r → 0 ≤ r.val ∧ r.val ≤ 676) := by
  sorry

/-- Whenever the function returns a result r, r <= d*d, where d is the number of distinct byte values occurring in s, i.e., d = |{ s[i] | 0 <= i < len(s) }|.
  Preconditions: 3 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice Std.U8) (hpre : validInput s) :
    ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      r.val ≤ (distinctCount (bytes s) : Int) ^ 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (hpre : validInput s), ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      r.val ≤ (distinctCount (bytes s) : Int) ^ 2) := by
  sorry

/-- Whenever the function returns a result r, r = sum over a from 97 to 122 of C(a), where for each a, C(a) = 0 if a occurs fewer than two times in s, and otherwise C(a) = |{ b | 97 <= b <= 122 and there exists j with first(a) < j < last(a) and s[j]=b }|, with first(a) and last(a) the least and greatest indices where s has byte a.
  Preconditions: 3 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_5 (s : Slice Std.U8) (hpre : validInput s) :
    ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      r.val = ((∑ a ∈ Finset.Icc 97 122, countFor (bytes s) a) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (hpre : validInput s), ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      r.val = ((∑ a ∈ Finset.Icc 97 122, countFor (bytes s) a) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exist indices i,j,k with 0 <= i < j < k < len(s) and s[i]=s[k].
  Preconditions: 3 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_6 (s : Slice Std.U8) (hpre : validInput s) :
    ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      (0 < r.val ↔ HasPal3 (bytes s)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (hpre : validInput s), ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      (0 < r.val ↔ HasPal3 (bytes s))) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every pair of indices i,k with 0 <= i < k < len(s) and s[i]=s[k], we have k = i+1.
  Preconditions: 3 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_7 (s : Slice Std.U8) (hpre : validInput s) :
    ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      (r.val = 0 ↔ NoGappedRepeat (bytes s)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (hpre : validInput s), ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      (r.val = 0 ↔ NoGappedRepeat (bytes s))) := by
  sorry

/-- Let t be any byte slice with len(t)=len(s) and t[i]=s[len(s)-1-i] for all i with 0 <= i < len(s). Whenever the function returns a result r on input s and a result r' on input t, we have r = r'.
  Preconditions: 3 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_8 (s t : Slice Std.U8) (hpre : validInput s)
    (ht : IsReverseBytes (bytes s) (bytes t)) :
    ∀ r r' : Std.I64, count_palindromic_subsequence s = ok r →
      count_palindromic_subsequence t = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice Std.U8) (hpre : validInput s)
    (ht : IsReverseBytes (bytes s) (bytes t)), ∀ r r' : Std.I64, count_palindromic_subsequence s = ok r →
      count_palindromic_subsequence t = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r_s on input s and a result r_t on input t, we have r_s <= r_t.
  Preconditions: 3 <= len(s) <= 100000, 3 <= len(t) <= 100000, every byte of s and t is in 97..122, and s is a subsequence of t (there exist indices j_0 < ... < j_{len(s)-1} with t[j_m]=s[m] for all m with 0 <= m < len(s)). -/
theorem spec_9 (s t : Slice Std.U8) (hs : validInput s) (ht : validInput t)
    (hsub : IsSubsequence (bytes s) (bytes t)) :
    ∀ r_s r_t : Std.I64, count_palindromic_subsequence s = ok r_s →
      count_palindromic_subsequence t = ok r_t → r_s.val ≤ r_t.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice Std.U8) (hs : validInput s) (ht : validInput t)
    (hsub : IsSubsequence (bytes s) (bytes t)), ∀ r_s r_t : Std.I64, count_palindromic_subsequence s = ok r_s →
      count_palindromic_subsequence t = ok r_t → r_s.val ≤ r_t.val) := by
  sorry

/-- Whenever the function returns a result r, r <= E(s), where E(s) is the number of triples of indices (i,j,k) such that 0 <= i < j < k < len(s) and s[i]=s[k].
  Preconditions: 3 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_10 (s : Slice Std.U8) (hpre : validInput s) :
    ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      r.val ≤ (palTripleCount (bytes s) : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (hpre : validInput s), ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      r.val ≤ (palTripleCount (bytes s) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= m, where m is the number of byte values a with 97 <= a <= 122 for which there exist indices i,k with 0 <= i < k < len(s), s[i]=s[k]=a, and k >= i+2 (equivalently, the first and last occurrences of a in s differ by at least 2).
  Preconditions: 3 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_11 (s : Slice Std.U8) (hpre : validInput s) :
    ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      (spacedCount (bytes s) : Int) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (hpre : validInput s), ∀ r : Std.I64, count_palindromic_subsequence s = ok r →
      (spacedCount (bytes s) : Int) ≤ r.val) := by
  sorry

end

end AegisSpec.CountPalindromicSubsequence
