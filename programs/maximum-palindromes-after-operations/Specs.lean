import Aegis.MaxPalindromesAfterOperations.Code.Funs

/-!
# Specifications of `Aegis.MaxPalindromesAfterOperations.max_palindromes_after_operations`

LeetCode problem `maximum-palindromes-after-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxPalindromesAfterOperations

abbrev target : Slice (alloc.vec.Vec Std.U8) → Result Std.I64 :=
  Aegis.MaxPalindromesAfterOperations.max_palindromes_after_operations

def totalChars (words : Slice (alloc.vec.Vec Std.U8)) : Multiset Std.U8 :=
  (words.val.map (fun v => (v.val : Multiset Std.U8))).sum

def charCount (words : Slice (alloc.vec.Vec Std.U8)) (b : Std.U8) : ℕ :=
  (totalChars words).count b

def pairs (words : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
  ∑ b ∈ (totalChars words).toFinset, charCount words b / 2

def oddChars (words : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
  ∑ b ∈ (totalChars words).toFinset, charCount words b % 2

def oddMult (M : Multiset Std.U8) : ℕ :=
  (M.toFinset.filter (fun b => M.count b % 2 = 1)).card

def halvesOf (words : Slice (alloc.vec.Vec Std.U8))
    (S : Finset (Fin words.val.length)) : ℕ :=
  ∑ i ∈ S, (words.val.get i).val.length / 2

def oddLenOf (words : Slice (alloc.vec.Vec Std.U8))
    (S : Finset (Fin words.val.length)) : ℕ :=
  (S.filter (fun i => (words.val.get i).val.length % 2 = 1)).card

def Realizable (words : Slice (alloc.vec.Vec Std.U8))
    (S : Finset (Fin words.val.length)) : Prop :=
  ∃ t : ℕ, halvesOf words S + t ≤ pairs words ∧ oddLenOf words S ≤ oddChars words + 2 * t

abbrev Palindromic (l : List Std.U8) : Prop := l = l.reverse

def unitWordCount (words : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
  (words.val.filter (fun v => v.val.length = 1)).length

def palindromeCount (words : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
  (words.val.filter (fun v => Palindromic v.val)).length

def totalHalves (words : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
  ∑ i : Fin words.val.length, (words.val.get i).val.length / 2

def totalOddLen (words : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
  (Finset.univ.filter
    (fun i : Fin words.val.length => (words.val.get i).val.length % 2 = 1)).card

/-- The function returns a result r. Let n = len(words). For each byte b, let C(b) be the total number of occurrences of b across all words (sum over i of the count of b in words[i]). Let P = sum over all bytes b of floor(C(b)/2), and O = sum over all bytes b of (C(b) mod 2). For a subset S ⊆ {0,1,...,n-1}, define A(S) = sum over i in S of floor(len(words[i])/2), and m(S) = the number of i in S such that len(words[i]) is odd. Then r is the maximum cardinality |S| over all subsets S of {0,1,...,n-1} for which there exists an integer t ≥ 0 satisfying A(S) + t ≤ P and m(S) ≤ O + 2t.
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64, target words = ok r ∧
      (∃ S : Finset (Fin words.val.length),
        Realizable words S ∧ (S.card : ℤ) = r.val) ∧
      (∀ S : Finset (Fin words.val.length),
        Realizable words S → (S.card : ℤ) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, target words = ok r ∧
      (∃ S : Finset (Fin words.val.length),
        Realizable words S ∧ (S.card : ℤ) = r.val) ∧
      (∀ S : Finset (Fin words.val.length),
        Realizable words S → (S.card : ℤ) ≤ r.val)) := by
  sorry

/-- The function returns a result r with 0 ≤ r ≤ len(words).
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64, target words = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (words.val.length : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, target words = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (words.val.length : ℤ)) := by
  sorry

/-- The function returns a result (i.e., it does not fail: no overflow, out-of-bounds, or panic).
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64, target words = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, target words = ok r) := by
  sorry

/-- Let w = words[0]. Let odd(w) be the number of bytes b such that the count of b in w is odd. Then r = 1 if odd(w) ≤ 1, and r = 0 otherwise.
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122); len(words) = 1. -/
theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hone : words.val.length = 1) :
    ∀ w : alloc.vec.Vec Std.U8, words.val = [w] →
      ∃ r : Std.I64, target words = ok r ∧
        (if oddMult (w.val : Multiset Std.U8) ≤ 1 then r.val = 1 else r.val = 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hone : words.val.length = 1), ∀ w : alloc.vec.Vec Std.U8, words.val = [w] →
      ∃ r : Std.I64, target words = ok r ∧
        (if oddMult (w.val : Multiset Std.U8) ≤ 1 then r.val = 1 else r.val = 0)) := by
  sorry

/-- For any permutation π of {0,1,...,n-1} (where n = len(words)), let words' be the list defined by words'[i] = words[π(i)] for 0 ≤ i < n. Then the result of the function on words' equals the result on words.
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (π : Equiv.Perm (Fin words.val.length)) (words' : Slice (alloc.vec.Vec Std.U8)),
      words'.val = List.ofFn (fun i : Fin words.val.length => words.val.get (π i)) →
      target words' = target words := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ (π : Equiv.Perm (Fin words.val.length)) (words' : Slice (alloc.vec.Vec Std.U8)),
      words'.val = List.ofFn (fun i : Fin words.val.length => words.val.get (π i)) →
      target words' = target words) := by
  sorry

/-- Let n = len(words). Then r ≥ the number of indices i with 0 ≤ i < n such that words[i] is a palindrome, i.e., for all j with 0 ≤ j < len(words[i]), words[i][j] = words[i][len(words[i]) - 1 - j].
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64, target words = ok r ∧ (palindromeCount words : ℤ) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, target words = ok r ∧ (palindromeCount words : ℤ) ≤ r.val) := by
  sorry

/-- Let C(b) be the total number of occurrences of byte b across all words, and let P = sum over all bytes b of floor(C(b)/2). If P = 0, then r equals the number of indices i with len(words[i]) = 1.
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hP : pairs words = 0) :
    ∃ r : Std.I64, target words = ok r ∧ (unitWordCount words : ℤ) = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hP : pairs words = 0), ∃ r : Std.I64, target words = ok r ∧ (unitWordCount words : ℤ) = r.val) := by
  sorry

/-- r = len(words).
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122); for all i with 0 ≤ i < len(words), len(words[i]) = 1. -/
theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hall : ∀ v ∈ words.val, v.val.length = 1) :
    ∃ r : Std.I64, target words = ok r ∧ r.val = (words.val.length : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hall : ∀ v ∈ words.val, v.val.length = 1), ∃ r : Std.I64, target words = ok r ∧ r.val = (words.val.length : ℤ)) := by
  sorry

/-- There exists a partition of the total multiset of characters in words into multisets M_0, M_1, ..., M_{n-1} (where n = len(words)) such that for each i, |M_i| = len(words[i]), the disjoint union of all M_i equals the total multiset of characters in words, and the number of indices i for which M_i has at most one byte with odd multiplicity is exactly r.
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_9 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64, target words = ok r ∧
      ∃ M : Fin words.val.length → Multiset Std.U8,
        (∀ i, (M i).card = (words.val.get i).val.length) ∧
        (∑ i, M i) = totalChars words ∧
        ((Finset.univ.filter (fun i => oddMult (M i) ≤ 1)).card : ℤ) = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, target words = ok r ∧
      ∃ M : Fin words.val.length → Multiset Std.U8,
        (∀ i, (M i).card = (words.val.get i).val.length) ∧
        (∑ i, M i) = totalChars words ∧
        ((Finset.univ.filter (fun i => oddMult (M i) ≤ 1)).card : ℤ) = r.val) := by
  sorry

/-- For every partition of the total multiset of characters in words into multisets M_0, M_1, ..., M_{n-1} such that |M_i| = len(words[i]) for all i and the disjoint union is the total multiset, the number of indices i for which M_i has at most one byte with odd multiplicity is at most r.
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_10 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64, target words = ok r ∧
      ∀ M : Fin words.val.length → Multiset Std.U8,
        (∀ i, (M i).card = (words.val.get i).val.length) →
        (∑ i, M i) = totalChars words →
        ((Finset.univ.filter (fun i => oddMult (M i) ≤ 1)).card : ℤ) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, target words = ok r ∧
      ∀ M : Fin words.val.length → Multiset Std.U8,
        (∀ i, (M i).card = (words.val.get i).val.length) →
        (∑ i, M i) = totalChars words →
        ((Finset.univ.filter (fun i => oddMult (M i) ≤ 1)).card : ℤ) ≤ r.val) := by
  sorry

/-- For any list of words' such that for each i with 0 ≤ i < len(words), words'[i] is a permutation of words[i] (i.e., same length and same multiset of bytes), the result of the function on words' equals the result on words.
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_11 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ words' : Slice (alloc.vec.Vec Std.U8),
      List.Forall₂ (fun (x y : alloc.vec.Vec Std.U8) => x.val.Perm y.val)
        words'.val words.val →
      target words' = target words := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ words' : Slice (alloc.vec.Vec Std.U8),
      List.Forall₂ (fun (x y : alloc.vec.Vec Std.U8) => x.val.Perm y.val)
        words'.val words.val →
      target words' = target words) := by
  sorry

/-- If there exists a byte b such that every byte in every words[i] equals b, then r = len(words).
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_12 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hsame : ∃ b : Std.U8, ∀ v ∈ words.val, ∀ x ∈ v.val, x = b) :
    ∃ r : Std.I64, target words = ok r ∧ r.val = (words.val.length : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hsame : ∃ b : Std.U8, ∀ v ∈ words.val, ∀ x ∈ v.val, x = b), ∃ r : Std.I64, target words = ok r ∧ r.val = (words.val.length : ℤ)) := by
  sorry

/-- Let P be the total number of pairs of identical characters across all words, i.e., P = sum over bytes b of floor(C(b)/2). Then r = min(len(words), P).
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122); for all i with 0 ≤ i < len(words), len(words[i]) = 2. -/
theorem spec_13 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hall : ∀ v ∈ words.val, v.val.length = 2) :
    ∃ r : Std.I64, target words = ok r ∧
      r.val = ((min words.val.length (pairs words) : ℕ) : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hall : ∀ v ∈ words.val, v.val.length = 2), ∃ r : Std.I64, target words = ok r ∧
      r.val = ((min words.val.length (pairs words) : ℕ) : ℤ)) := by
  sorry

/-- Let r be the result of the function on words, and r' the result on words'. Then r' ≥ r.
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). Choose an index k with 0 ≤ k < len(words) and a lowercase English letter b (ASCII 97–122) such that len(words[k]) + 2 ≤ 100. Let words' be obtained from words by replacing words[k] with words[k] followed by b, b. (Then words' also satisfies the same input constraints.) -/
theorem spec_14 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (k : Fin words.val.length) (b : Std.U8) (words' : Slice (alloc.vec.Vec Std.U8))
      (v' : alloc.vec.Vec Std.U8),
      97 ≤ b.val → b.val ≤ 122 →
      (words.val.get k).val.length + 2 ≤ 100 →
      v'.val = (words.val.get k).val ++ [b, b] →
      words'.val = words.val.set k.val v' →
      ∀ r r' : Std.I64,
        target words = ok r → target words' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ (k : Fin words.val.length) (b : Std.U8) (words' : Slice (alloc.vec.Vec Std.U8))
      (v' : alloc.vec.Vec Std.U8),
      97 ≤ b.val → b.val ≤ 122 →
      (words.val.get k).val.length + 2 ≤ 100 →
      v'.val = (words.val.get k).val ++ [b, b] →
      words'.val = words.val.set k.val v' →
      ∀ r r' : Std.I64,
        target words = ok r → target words' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- Let O be the total number of bytes with odd total count across all words, i.e., O = sum over bytes b of (C(b) mod 2). If O = 0, then r = len(words).
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_15 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hO : oddChars words = 0) :
    ∃ r : Std.I64, target words = ok r ∧ r.val = (words.val.length : ℤ) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hO : oddChars words = 0), ∃ r : Std.I64, target words = ok r ∧ r.val = (words.val.length : ℤ)) := by
  sorry

/-- For any two valid inputs words and words' with the same multiset of word lengths and the same total multiset of bytes across all words, the result on words equals the result on words'.
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_16 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ words' : Slice (alloc.vec.Vec Std.U8),
      (words.val.map (fun v => v.val.length)).Perm (words'.val.map (fun v => v.val.length)) →
      totalChars words = totalChars words' →
      target words' = target words := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ words' : Slice (alloc.vec.Vec Std.U8),
      (words.val.map (fun v => v.val.length)).Perm (words'.val.map (fun v => v.val.length)) →
      totalChars words = totalChars words' →
      target words' = target words) := by
  sorry

/-- If words' is words with w appended as an additional word, so len(words') = len(words)+1, then the result of the function on words' is at least the result on words.
  Preconditions: 1 ≤ len(words) < 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122); let w be any nonempty string of lowercase English letters with 1 ≤ len(w) ≤ 100. -/
theorem spec_17 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hlt : words.val.length < 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (w : alloc.vec.Vec Std.U8) (words' : Slice (alloc.vec.Vec Std.U8)),
      1 ≤ w.val.length → w.val.length ≤ 100 →
      (∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) →
      words'.val = words.val ++ [w] →
      ∀ r r' : Std.I64,
        target words = ok r → target words' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hlt : words.val.length < 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ (w : alloc.vec.Vec Std.U8) (words' : Slice (alloc.vec.Vec Std.U8)),
      1 ≤ w.val.length → w.val.length ≤ 100 →
      (∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) →
      words'.val = words.val ++ [w] →
      ∀ r r' : Std.I64,
        target words = ok r → target words' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- Let n = len(words), let P and O be as in spec_1, let A_total = sum_{i=0}^{n-1} floor(len(words[i])/2), and let m_total be the number of indices i with len(words[i]) odd. Then r = n if and only if there exists an integer t ≥ 0 such that A_total + t ≤ P and m_total ≤ O + 2t.
  Preconditions: 1 ≤ len(words) ≤ 1000; for every i with 0 ≤ i < len(words), 1 ≤ len(words[i]) ≤ 100; every byte in every words[i] is a lowercase English letter (ASCII 97–122). -/
theorem spec_18 (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64, target words = ok r ∧
      (r.val = (words.val.length : ℤ) ↔
        ∃ t : ℕ,
          totalHalves words + t ≤ pairs words ∧
          totalOddLen words ≤ oddChars words + 2 * t) := by
  sorry

theorem spec_18_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
    (hne : 1 ≤ words.val.length) (hle : words.val.length ≤ 1000)
    (hlen : ∀ v ∈ words.val, 1 ≤ v.val.length ∧ v.val.length ≤ 100)
    (hlower : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, target words = ok r ∧
      (r.val = (words.val.length : ℤ) ↔
        ∃ t : ℕ,
          totalHalves words + t ≤ pairs words ∧
          totalOddLen words ≤ oddChars words + 2 * t)) := by
  sorry

end AegisSpec.MaxPalindromesAfterOperations
