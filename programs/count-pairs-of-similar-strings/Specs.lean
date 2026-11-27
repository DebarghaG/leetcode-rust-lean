import Aegis.SimilarPairs.Code.Funs

/-!
# Specifications of `Aegis.SimilarPairs.similar_pairs`

LeetCode problem `count-pairs-of-similar-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SimilarPairs

def wordAt (words : Slice (alloc.vec.Vec Std.U8)) (i : ℕ) : List Std.U8 :=
  match (words.val.drop i).head? with
  | some v => v.val
  | none => []

def byteSet (l : List Std.U8) : Finset ℕ := (l.map fun b => b.val).toFinset

def charSetAt (words : Slice (alloc.vec.Vec Std.U8)) (i : ℕ) : Finset ℕ :=
  byteSet (wordAt words i)

def similar (u v : List Std.U8) : Prop := byteSet u = byteSet v

instance instDecidableSimilar (u v : List Std.U8) : Decidable (similar u v) :=
  inferInstanceAs (Decidable (byteSet u = byteSet v))

def charSets (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).image (charSetAt words)

def charSetCount (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ) (S : Finset ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => charSetAt words i = S)).card

def similarPairCount (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ) : ℕ :=
  (((Finset.range n).product (Finset.range n)).filter
    (fun p : ℕ × ℕ => p.1 < p.2 ∧ similar (wordAt words p.1) (wordAt words p.2))).card

/-- Whenever the function returns a result r, r equals the number of pairs of indices (i, j) with 0 <= i < j < n such that words[i] and words[j] are similar, where two byte arrays u, v are similar exactly when they contain the same set of bytes, i.e. { b : b occurs in u } = { b : b occurs in v }.
  Preconditions: n = len(words); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100, and every byte b occurring in words[i] satisfies 97 <= b <= 122 (lowercase English letter). -/
theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (r : Std.I64) (hr : Aegis.SimilarPairs.similar_pairs words = ok r) :
    r.val = (similarPairCount words n : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (r : Std.I64) (hr : Aegis.SimilarPairs.similar_pairs words = ok r), r.val = (similarPairCount words n : ℤ)) := by
  sorry

/-- The function returns a result r and does not fail (no arithmetic overflow and no out-of-bounds access).
  Preconditions: n = len(words); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100, and every byte b occurring in words[i] satisfies 97 <= b <= 122. -/
theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64, Aegis.SimilarPairs.similar_pairs words = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.SimilarPairs.similar_pairs words = ok r) := by
  sorry

/-- Whenever similar_pairs(words) returns r and similar_pairs(words') returns r', we have r = r'.
  Preconditions: n = len(words); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100, and every byte b occurring in words[i] satisfies 97 <= b <= 122. Additionally, words' is any list of length n that is a permutation of words, i.e. there is a bijection pi on {0,...,n-1} with words'[i] = words[pi(i)] for every 0 <= i < n (so words' satisfies the same constraints). -/
theorem spec_3 (words words' : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (hperm : List.Perm words.val words'.val)
    (r r' : Std.I64)
    (hr : Aegis.SimilarPairs.similar_pairs words = ok r)
    (hr' : Aegis.SimilarPairs.similar_pairs words' = ok r') :
    r = r' := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (hperm : List.Perm words.val words'.val)
    (r r' : Std.I64)
    (hr : Aegis.SimilarPairs.similar_pairs words = ok r)
    (hr' : Aegis.SimilarPairs.similar_pairs words' = ok r'), r = r') := by
  sorry

/-- Whenever similar_pairs(words) returns r and similar_pairs(words') returns r', we have r' = r + m, where m is the number of indices i with 0 <= i < n such that { b : b occurs in words[i] } = { b : b occurs in w }.
  Preconditions: n = len(words); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100, and every byte b occurring in words[i] satisfies 97 <= b <= 122. Additionally n < 100, w is a byte array with 1 <= len(w) <= 100 and all bytes lowercase, and words' is the list of length n+1 obtained by appending w, i.e. words'[i] = words[i] for 0 <= i < n and words'[n] = w. -/
theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (hn100 : n < 100)
    (w : alloc.vec.Vec Std.U8)
    (hwlen : 1 ≤ w.val.length ∧ w.val.length ≤ 100)
    (hwbytes : ∀ b, b ∈ w.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (words' : Slice (alloc.vec.Vec Std.U8))
    (hwords' : words'.val = words.val ++ [w])
    (r r' : Std.I64)
    (hr : Aegis.SimilarPairs.similar_pairs words = ok r)
    (hr' : Aegis.SimilarPairs.similar_pairs words' = ok r') :
    r' = r + (charSetCount words n (byteSet w.val) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (hn100 : n < 100)
    (w : alloc.vec.Vec Std.U8)
    (hwlen : 1 ≤ w.val.length ∧ w.val.length ≤ 100)
    (hwbytes : ∀ b, b ∈ w.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (words' : Slice (alloc.vec.Vec Std.U8))
    (hwords' : words'.val = words.val ++ [w])
    (r r' : Std.I64)
    (hr : Aegis.SimilarPairs.similar_pairs words = ok r)
    (hr' : Aegis.SimilarPairs.similar_pairs words' = ok r'), r' = r + (charSetCount words n (byteSet w.val) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r >= n - k, where k = the number of distinct character sets among the words, i.e. k = the cardinality of { { b : b occurs in words[i] } : 0 <= i < n }.
  Preconditions: n = len(words); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100, and every byte b occurring in words[i] satisfies 97 <= b <= 122. -/
theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (r : Std.I64) (hr : Aegis.SimilarPairs.similar_pairs words = ok r) :
    (n : ℤ) - ((charSets words n).card : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (r : Std.I64) (hr : Aegis.SimilarPairs.similar_pairs words = ok r), (n : ℤ) - ((charSets words n).card : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for each byte set S let c(S) be the number of indices i with 0 <= i < n such that { b : b occurs in words[i] } = S. Then r = sum over all distinct character sets S occurring among the words of c(S)*(c(S)-1)/2.
  Preconditions: n = len(words); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100, and every byte b occurring in words[i] satisfies 97 <= b <= 122. -/
theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (r : Std.I64) (hr : Aegis.SimilarPairs.similar_pairs words = ok r) :
    r.val = ∑ S ∈ charSets words n,
      ((charSetCount words n S * (charSetCount words n S - 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (r : Std.I64) (hr : Aegis.SimilarPairs.similar_pairs words = ok r), r.val = ∑ S ∈ charSets words n,
      ((charSetCount words n S * (charSetCount words n S - 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if the character sets { b : b occurs in words[i] } are pairwise distinct; equivalently, no two distinct indices i < j have similar words.
  Preconditions: n = len(words); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100, and every byte b occurring in words[i] satisfies 97 <= b <= 122. -/
theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (r : Std.I64) (hr : Aegis.SimilarPairs.similar_pairs words = ok r) :
    r.val = 0 ↔ ∀ i, i < n → ∀ j, i < j → j < n → charSetAt words i ≠ charSetAt words j := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (r : Std.I64) (hr : Aegis.SimilarPairs.similar_pairs words = ok r), r.val = 0 ↔ ∀ i, i < n → ∀ j, i < j → j < n → charSetAt words i ≠ charSetAt words j) := by
  sorry

/-- Whenever the function returns a result r, r = n*(n-1)/2 if and only if all words have the same character set, i.e. there exists a byte set S such that for every 0 <= i < n, { b : b occurs in words[i] } = S.
  Preconditions: n = len(words); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100, and every byte b occurring in words[i] satisfies 97 <= b <= 122. -/
theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (r : Std.I64) (hr : Aegis.SimilarPairs.similar_pairs words = ok r) :
    r.val = ((n * (n - 1) / 2 : ℕ) : ℤ) ↔ ∃ S : Finset ℕ, ∀ i, i < n → charSetAt words i = S := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
    (hn : n = (Slice.len words).val)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hlen : ∀ i, i < n → 1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100)
    (hbytes : ∀ i, i < n → ∀ b, b ∈ wordAt words i → 97 ≤ b.val ∧ b.val ≤ 122)
    (r : Std.I64) (hr : Aegis.SimilarPairs.similar_pairs words = ok r), r.val = ((n * (n - 1) / 2 : ℕ) : ℤ) ↔ ∃ S : Finset ℕ, ∀ i, i < n → charSetAt words i = S) := by
  sorry

end AegisSpec.SimilarPairs
