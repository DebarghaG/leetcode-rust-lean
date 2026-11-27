import Aegis.IndexPairs.Code.Funs

/-!
# Specifications of `Aegis.IndexPairs.index_pairs`

LeetCode problem `index-pairs-of-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IndexPairs

namespace AegisSpec.IndexPairs

def byteAt (l : List Std.U8) (t : ℕ) : ℕ := ((l[t]?).map (fun b => b.val)).getD 0

def wordBytes (words : Slice (alloc.vec.Vec Std.U8)) (k : ℕ) : List Std.U8 :=
  ((words.val[k]?).map (fun w => w.val)).getD []

def wordLen (words : Slice (alloc.vec.Vec Std.U8)) (k : ℕ) : ℕ := (wordBytes words k).length

def LowerASCII (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def LowerASCIIList (l : List Std.U8) : Prop := ∀ b ∈ l, LowerASCII b

def LeetCodeInputs (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  1 ≤ text.val.length ∧ text.val.length ≤ 100 ∧
    1 ≤ words.val.length ∧ words.val.length ≤ 20 ∧
      (∀ k : ℕ, k < words.val.length → 1 ≤ wordLen words k ∧ wordLen words k ≤ 50) ∧
        LowerASCIIList text.val ∧
          (∀ k : ℕ, k < words.val.length → LowerASCIIList (wordBytes words k)) ∧
            words.val.Nodup

def BytesMatch (text : Slice Std.U8) (w : List Std.U8) (i : ℤ) : Prop :=
  ∀ t : ℕ, t < w.length → byteAt text.val (i.toNat + t) = byteAt w t

def Occurs (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) (i j : ℤ) : Prop :=
  ∃ k : ℕ,
    k < words.val.length ∧
      j - i + 1 = (wordLen words k : ℤ) ∧ BytesMatch text (wordBytes words k) i

def InTextBounds (text : Slice Std.U8) (i j : ℤ) : Prop :=
  0 ≤ i ∧ i ≤ j ∧ j < (text.val.length : ℤ)

def IsMatch (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) (i j : ℤ) : Prop :=
  InTextBounds text i j ∧ Occurs text words i j

def WordFits (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) (k : ℕ) (i : ℤ) : Prop :=
  k < words.val.length ∧
    i + (wordLen words k : ℤ) ≤ (text.val.length : ℤ) ∧ BytesMatch text (wordBytes words k) i

def PairIs (p : alloc.vec.Vec Std.I64) (i j : ℤ) : Prop :=
  p.val.map (fun x => x.val) = [i, j]

def entryAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a : ℕ) :
    Option (alloc.vec.Vec Std.I64) :=
  r.val[a]?

def PairAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a : ℕ) (i j : ℤ) : Prop :=
  ∃ p : alloc.vec.Vec Std.I64, entryAt r a = some p ∧ PairIs p i j

def OccursOnce (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i j : ℤ) : Prop :=
  ∃ a : ℕ, PairAt r a i j ∧ ∀ b : ℕ, PairAt r b i j → b = a

noncomputable def matchingPairs (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) :
    List (ℤ × ℤ) := by
  classical
  exact
    ((List.range text.val.length).product (List.range text.val.length)).filterMap fun q =>
      if IsMatch text words (q.1 : ℤ) (q.2 : ℤ) then some ((q.1 : ℤ), (q.2 : ℤ)) else none

noncomputable def matchCount (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
  (matchingPairs text words).length

/-- Whenever index_pairs returns a result r, call an ordered pair (i,j) a matching pair when 0 <= i <= j < len(text) and there exists k with 0 <= k < len(words) such that j - i + 1 = len(words[k]) and text[i+t] = words[k][t] for every t with 0 <= t < j - i + 1. Then r is exactly the vector of all matching pairs, each written as the two-element vector [i,j], with every matching pair appearing exactly once and no other entries, in strictly increasing order by first coordinate and then by second coordinate: for every a < b in r, writing r[a]=[i,j] and r[b]=[i',j'], either i < i', or i = i' and j < j'.
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_1 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      (∀ p ∈ r.val, ∃ i j : ℤ, PairIs p i j ∧ IsMatch text words i j) ∧
        (∀ i j : ℤ, IsMatch text words i j → OccursOnce r i j) ∧
          (∀ a b : ℕ, a < b → b < r.val.length → ∀ i j i' j' : ℤ,
            PairAt r a i j → PairAt r b i' j' → i < i' ∨ (i = i' ∧ j < j')) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      (∀ p ∈ r.val, ∃ i j : ℤ, PairIs p i j ∧ IsMatch text words i j) ∧
        (∀ i j : ℤ, IsMatch text words i j → OccursOnce r i j) ∧
          (∀ a b : ℕ, a < b → b < r.val.length → ∀ i j i' j' : ℤ,
            PairAt r a i j → PairAt r b i' j' → i < i' ∨ (i = i' ∧ j < j'))) := by
  sorry

/-- index_pairs returns a result r (in Lean, a Result.ok value); it does not fail, panic, overflow, or access memory out of bounds.
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_2 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r) := by
  sorry

/-- Whenever index_pairs returns a result r, every element p of r is a vector of length 2; equivalently, p = [p[0], p[1]] for every p in r.
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_3 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ p ∈ r.val, p.val.length = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ p ∈ r.val, p.val.length = 2) := by
  sorry

/-- Whenever index_pairs returns a result r, for every element p of r, writing p=[i,j], the coordinates satisfy 0 <= i <= j < len(text).
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_4 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ p ∈ r.val, ∃ i j : ℤ, PairIs p i j ∧ InTextBounds text i j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ p ∈ r.val, ∃ i j : ℤ, PairIs p i j ∧ InTextBounds text i j) := by
  sorry

/-- Whenever index_pairs returns a result r, every returned pair has a word witness: for every element p of r, writing p=[i,j], we have 0 <= i <= j < len(text) and there exists k with 0 <= k < len(words) such that j - i + 1 = len(words[k]) and text[i+t] = words[k][t] for every t with 0 <= t < j - i + 1.
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_5 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ p ∈ r.val, ∃ i j : ℤ, PairIs p i j ∧ IsMatch text words i j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ p ∈ r.val, ∃ i j : ℤ, PairIs p i j ∧ IsMatch text words i j) := by
  sorry

/-- Whenever index_pairs returns a result r, every matching pair occurs in r: for every pair of integers (i,j) with 0 <= i <= j < len(text) for which there exists k with 0 <= k < len(words) such that j - i + 1 = len(words[k]) and text[i+t] = words[k][t] for every t with 0 <= t < j - i + 1, there is an index a with 0 <= a < len(r) and r[a] = [i,j].
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_6 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ i j : ℤ, IsMatch text words i j → ∃ a : ℕ, PairAt r a i j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ i j : ℤ, IsMatch text words i j → ∃ a : ℕ, PairAt r a i j) := by
  sorry

/-- Whenever index_pairs returns a result r, the first coordinates of r are nondecreasing: for every a,b with 0 <= a < b < len(r), writing r[a]=[i,j] and r[b]=[i',j'], we have i <= i'.
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_7 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ a b : ℕ, a < b → b < r.val.length → ∀ i j i' j' : ℤ,
        PairAt r a i j → PairAt r b i' j' → i ≤ i' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ a b : ℕ, a < b → b < r.val.length → ∀ i j i' j' : ℤ,
        PairAt r a i j → PairAt r b i' j' → i ≤ i') := by
  sorry

/-- Whenever index_pairs returns a result r, entries with equal first coordinate are ordered by nondecreasing second coordinate: for every a,b with 0 <= a < b < len(r), writing r[a]=[i,j] and r[b]=[i',j'], if i = i' then j <= j'.
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_8 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ a b : ℕ, a < b → b < r.val.length → ∀ i j i' j' : ℤ,
        PairAt r a i j → PairAt r b i' j' → i = i' → j ≤ j' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ a b : ℕ, a < b → b < r.val.length → ∀ i j i' j' : ℤ,
        PairAt r a i j → PairAt r b i' j' → i = i' → j ≤ j') := by
  sorry

/-- Whenever index_pairs returns a result r, r contains no duplicate ordered pair: for every a,b with 0 <= a < b < len(r), r[a] != r[b].
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_9 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ a b : ℕ, a < b → b < r.val.length → entryAt r a ≠ entryAt r b := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ a b : ℕ, a < b → b < r.val.length → entryAt r a ≠ entryAt r b) := by
  sorry

/-- Whenever index_pairs returns a result r, len(r) is exactly the number of matching pairs (i,j), that is, the number of integer pairs with 0 <= i <= j < len(text) for which there exists k with 0 <= k < len(words), j - i + 1 = len(words[k]), and text[i+t] = words[k][t] for every t with 0 <= t < j - i + 1.
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_10 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      r.val.length = matchCount text words := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      r.val.length = matchCount text words) := by
  sorry

/-- Whenever index_pairs returns a result r, len(r)=0 if and only if there do not exist integers i,j,k with 0 <= i <= j < len(text), 0 <= k < len(words), j - i + 1 = len(words[k]), and text[i+t] = words[k][t] for every t with 0 <= t < j - i + 1.
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_11 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      (r.val.length = 0 ↔ ¬ (∃ i j : ℤ, IsMatch text words i j)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      (r.val.length = 0 ↔ ¬ (∃ i j : ℤ, IsMatch text words i j))) := by
  sorry

/-- Whenever index_pairs returns a result r, every occurrence of every word is reported: for every k with 0 <= k < len(words) and every i with 0 <= i and i + len(words[k]) <= len(text) such that text[i+t] = words[k][t] for every t with 0 <= t < len(words[k]), the pair [i, i + len(words[k]) - 1] occurs as an entry of r.
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_12 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ k : ℕ, k < words.val.length → ∀ i : ℤ, 0 ≤ i →
        i + (wordLen words k : ℤ) ≤ (text.val.length : ℤ) →
          BytesMatch text (wordBytes words k) i →
            ∃ a : ℕ, PairAt r a i (i + (wordLen words k : ℤ) - 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ k : ℕ, k < words.val.length → ∀ i : ℤ, 0 ≤ i →
        i + (wordLen words k : ℤ) ≤ (text.val.length : ℤ) →
          BytesMatch text (wordBytes words k) i →
            ∃ a : ℕ, PairAt r a i (i + (wordLen words k : ℤ) - 1)) := by
  sorry

/-- Whenever index_pairs returns a result r on (text, words) and returns a result r' on (text, words'), we have r = r'.
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. Let words' be any slice of byte vectors that satisfies the same constraints and is a permutation of words. -/
theorem spec_13 (text : Slice Std.U8) (words words' : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) (h' : LeetCodeInputs text words')
    (hperm : words'.val.Perm words.val) :
    ∀ r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      index_pairs text words = ok r → index_pairs text words' = ok r' → r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (text : Slice Std.U8) (words words' : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) (h' : LeetCodeInputs text words')
    (hperm : words'.val.Perm words.val), ∀ r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      index_pairs text words = ok r → index_pairs text words' = ok r' → r = r') := by
  sorry

/-- Whenever index_pairs returns a result r, for every i with 0 <= i < len(text), the entries of r whose first coordinate is i are exactly the pairs [i, i + len(words[k]) - 1] for those k with 0 <= k < len(words), i + len(words[k]) <= len(text), and text[i+t] = words[k][t] for every t with 0 <= t < len(words[k]).
  Preconditions: The inputs satisfy the LeetCode constraints: 1 <= len(text) <= 100; 1 <= len(words) <= 20; for every k with 0 <= k < len(words), 1 <= len(words[k]) <= 50; every byte of text and of every words[k] is an ASCII lowercase letter from 'a' to 'z'; and the word vectors words[0],...,words[len(words)-1] are pairwise distinct. -/
theorem spec_14 (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ i : ℤ, 0 ≤ i → i < (text.val.length : ℤ) →
        (∀ b : ℕ, ∀ j : ℤ, PairAt r b i j →
            ∃ k : ℕ, WordFits text words k i ∧ j = i + (wordLen words k : ℤ) - 1) ∧
          (∀ k : ℕ, WordFits text words k i →
            OccursOnce r i (i + (wordLen words k : ℤ) - 1)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (text : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
    (h : LeetCodeInputs text words), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), index_pairs text words = ok r →
      ∀ i : ℤ, 0 ≤ i → i < (text.val.length : ℤ) →
        (∀ b : ℕ, ∀ j : ℤ, PairAt r b i j →
            ∃ k : ℕ, WordFits text words k i ∧ j = i + (wordLen words k : ℤ) - 1) ∧
          (∀ k : ℕ, WordFits text words k i →
            OccursOnce r i (i + (wordLen words k : ℤ) - 1))) := by
  sorry

end AegisSpec.IndexPairs
