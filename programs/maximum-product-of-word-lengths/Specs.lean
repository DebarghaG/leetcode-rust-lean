import Aegis.MaxProduct.Code.Funs

/-!
# Specifications of `Aegis.MaxProduct.max_product`

LeetCode problem `maximum-product-of-word-lengths`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxProduct

open Aegis.MaxProduct

def letters (w : alloc.vec.Vec Std.U8) : Set Nat := { c | ∃ b ∈ w.val, b.val = c }

def lettersDisjoint (w₁ w₂ : alloc.vec.Vec Std.U8) : Prop := letters w₁ ∩ letters w₂ = ∅

def lengths (words : Slice (alloc.vec.Vec Std.U8)) : List Nat :=
  words.val.map (fun w => w.val.length)

def TwoLargest (l : List Nat) (L1 L2 : Nat) : Prop :=
  L2 ≤ L1 ∧ (∀ x ∈ l, x ≤ L1) ∧ ∃ t : List Nat, l.Perm (L1 :: L2 :: t) ∧ ∀ x ∈ t, x ≤ L2

def ValidInput (words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  2 ≤ words.val.length ∧ words.val.length ≤ 1000 ∧
    ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 1000 ∧
        ∀ b ∈ (words.val[i]).val, 97 ≤ b.val ∧ b.val ≤ 122

/-- The function returns a result r (it does not fail). Let letters(w) be the set of bytes occurring in w. Then r is the maximum of the set {0} ∪ { len(words[i]) * len(words[j]) | 0 <= i < j < len(words) and letters(words[i]) ∩ letters(words[j]) = ∅ }. Equivalently: (a) for every i and j with 0 <= i < j < len(words) and letters(words[i]) ∩ letters(words[j]) = ∅, len(words[i]) * len(words[j]) <= r; and (b) either r = 0 and there is no such pair (i,j), or there exist i and j with 0 <= i < j < len(words), letters(words[i]) ∩ letters(words[j]) = ∅, and len(words[i]) * len(words[j]) = r.
  Preconditions: 2 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 1000 and every byte of words[i] is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words) :
    ∃ r : Std.I64,
      max_product words = Result.ok r ∧
        (∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length), i < j →
            lettersDisjoint (words.val[i]) (words.val[j]) →
              ((words.val[i]).val.length : Int) * ((words.val[j]).val.length : Int) ≤ r.val) ∧
          ((r.val = 0 ∧
              ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length), i < j →
                ¬ lettersDisjoint (words.val[i]) (words.val[j])) ∨
            ∃ (i : Nat) (hi : i < words.val.length) (j : Nat) (hj : j < words.val.length),
              i < j ∧ lettersDisjoint (words.val[i]) (words.val[j]) ∧
                ((words.val[i]).val.length : Int) * ((words.val[j]).val.length : Int) = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words), ∃ r : Std.I64,
      max_product words = Result.ok r ∧
        (∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length), i < j →
            lettersDisjoint (words.val[i]) (words.val[j]) →
              ((words.val[i]).val.length : Int) * ((words.val[j]).val.length : Int) ≤ r.val) ∧
          ((r.val = 0 ∧
              ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length), i < j →
                ¬ lettersDisjoint (words.val[i]) (words.val[j])) ∨
            ∃ (i : Nat) (hi : i < words.val.length) (j : Nat) (hj : j < words.val.length),
              i < j ∧ lettersDisjoint (words.val[i]) (words.val[j]) ∧
                ((words.val[i]).val.length : Int) * ((words.val[j]).val.length : Int) = r.val)) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: 2 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 1000 and every byte of words[i] is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words) :
    ∃ r : Std.I64, max_product words = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words), ∃ r : Std.I64, max_product words = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: 2 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 1000 and every byte of words[i] is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words) :
    ∀ (r : Std.I64), max_product words = Result.ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words), ∀ (r : Std.I64), max_product words = Result.ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= L1 * L2, where L1 and L2 are the two largest values in the multiset { len(words[i]) | 0 <= i < len(words) } counted with multiplicity (so L1 >= L2 and every other length is <= L2).
  Preconditions: 2 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 1000 and every byte of words[i] is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words) :
    ∀ (r : Std.I64) (L1 L2 : Nat), max_product words = Result.ok r →
      TwoLargest (lengths words) L1 L2 → r.val ≤ (L1 : Int) * (L2 : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words), ∀ (r : Std.I64) (L1 L2 : Nat), max_product words = Result.ok r →
      TwoLargest (lengths words) L1 L2 → r.val ≤ (L1 : Int) * (L2 : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(words) such that letters(words[i]) ∩ letters(words[j]) = ∅, we have len(words[i]) * len(words[j]) <= r; here letters(w) denotes the set of bytes occurring in w.
  Preconditions: 2 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 1000 and every byte of words[i] is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words) :
    ∀ (r : Std.I64), max_product words = Result.ok r →
      ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length), i < j →
        lettersDisjoint (words.val[i]) (words.val[j]) →
          ((words.val[i]).val.length : Int) * ((words.val[j]).val.length : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words), ∀ (r : Std.I64), max_product words = Result.ok r →
      ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length), i < j →
        lettersDisjoint (words.val[i]) (words.val[j]) →
          ((words.val[i]).val.length : Int) * ((words.val[j]).val.length : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r and 0 < r, there exist i and j with 0 <= i < j < len(words) such that letters(words[i]) ∩ letters(words[j]) = ∅ and len(words[i]) * len(words[j]) = r; here letters(w) denotes the set of bytes occurring in w.
  Preconditions: 2 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 1000 and every byte of words[i] is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words) :
    ∀ (r : Std.I64), max_product words = Result.ok r → 0 < r.val →
      ∃ (i : Nat) (hi : i < words.val.length) (j : Nat) (hj : j < words.val.length),
        i < j ∧ lettersDisjoint (words.val[i]) (words.val[j]) ∧
          ((words.val[i]).val.length : Int) * ((words.val[j]).val.length : Int) = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words), ∀ (r : Std.I64), max_product words = Result.ok r → 0 < r.val →
      ∃ (i : Nat) (hi : i < words.val.length) (j : Nat) (hj : j < words.val.length),
        i < j ∧ lettersDisjoint (words.val[i]) (words.val[j]) ∧
          ((words.val[i]).val.length : Int) * ((words.val[j]).val.length : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i and j with 0 <= i < j < len(words), letters(words[i]) ∩ letters(words[j]) ≠ ∅ (i.e., every two distinct words share at least one byte); here letters(w) denotes the set of bytes occurring in w.
  Preconditions: 2 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 1000 and every byte of words[i] is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words) :
    ∀ (r : Std.I64), max_product words = Result.ok r →
      (r.val = 0 ↔
        ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length), i < j →
          ¬ lettersDisjoint (words.val[i]) (words.val[j])) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words), ∀ (r : Std.I64), max_product words = Result.ok r →
      (r.val = 0 ↔
        ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length), i < j →
          ¬ lettersDisjoint (words.val[i]) (words.val[j]))) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: 2 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 1000 and every byte of words[i] is a lowercase English letter (97 <= byte <= 122). There exists a byte c with 97 <= c <= 122 such that for every i with 0 <= i < len(words), c ∈ letters(words[i]), where letters(w) denotes the set of bytes occurring in w. -/
theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_common : ∃ c : Nat, 97 ≤ c ∧ c ≤ 122 ∧
      ∀ (i : Nat) (hi : i < words.val.length), c ∈ letters (words.val[i])) :
    ∀ (r : Std.I64), max_product words = Result.ok r → r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_common : ∃ c : Nat, 97 ≤ c ∧ c ≤ 122 ∧
      ∀ (i : Nat) (hi : i < words.val.length), c ∈ letters (words.val[i])), ∀ (r : Std.I64), max_product words = Result.ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if letters(words[0]) ∩ letters(words[1]) = ∅ then r = len(words[0]) * len(words[1]), and otherwise r = 0; here letters(w) denotes the set of bytes occurring in w.
  Preconditions: 2 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 1000 and every byte of words[i] is a lowercase English letter (97 <= byte <= 122). len(words) = 2. -/
theorem spec_9 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_len : words.val.length = 2) :
    ∀ (r : Std.I64), max_product words = Result.ok r →
      (lettersDisjoint (words.val[0]'(by omega)) (words.val[1]'(by omega)) →
          r.val = ((words.val[0]'(by omega)).val.length : Int) *
            ((words.val[1]'(by omega)).val.length : Int)) ∧
        (¬ lettersDisjoint (words.val[0]'(by omega)) (words.val[1]'(by omega)) → r.val = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_len : words.val.length = 2), ∀ (r : Std.I64), max_product words = Result.ok r →
      (lettersDisjoint (words.val[0]'(by omega)) (words.val[1]'(by omega)) →
          r.val = ((words.val[0]'(by omega)).val.length : Int) *
            ((words.val[1]'(by omega)).val.length : Int)) ∧
        (¬ lettersDisjoint (words.val[0]'(by omega)) (words.val[1]'(by omega)) → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if there exist i and j with 0 <= i < j < len(words) and words[i][0] ≠ words[j][0]; otherwise r = 0.
  Preconditions: 2 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 1000 and every byte of words[i] is a lowercase English letter (97 <= byte <= 122). For every i with 0 <= i < len(words), len(words[i]) = 1. -/
theorem spec_10 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_len1 : ∀ (i : Nat) (hi : i < words.val.length), (words.val[i]).val.length = 1) :
    ∀ (r : Std.I64), max_product words = Result.ok r →
      ((∃ (i : Nat) (hi : i < words.val.length) (j : Nat) (hj : j < words.val.length),
          i < j ∧
            (words.val[i]).val[0]'(by have h := h_len1 i hi; omega) ≠
              (words.val[j]).val[0]'(by have h := h_len1 j hj; omega)) → r.val = 1) ∧
        (¬ (∃ (i : Nat) (hi : i < words.val.length) (j : Nat) (hj : j < words.val.length),
            i < j ∧
              (words.val[i]).val[0]'(by have h := h_len1 i hi; omega) ≠
                (words.val[j]).val[0]'(by have h := h_len1 j hj; omega)) → r.val = 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_len1 : ∀ (i : Nat) (hi : i < words.val.length), (words.val[i]).val.length = 1), ∀ (r : Std.I64), max_product words = Result.ok r →
      ((∃ (i : Nat) (hi : i < words.val.length) (j : Nat) (hj : j < words.val.length),
          i < j ∧
            (words.val[i]).val[0]'(by have h := h_len1 i hi; omega) ≠
              (words.val[j]).val[0]'(by have h := h_len1 j hj; omega)) → r.val = 1) ∧
        (¬ (∃ (i : Nat) (hi : i < words.val.length) (j : Nat) (hj : j < words.val.length),
            i < j ∧
              (words.val[i]).val[0]'(by have h := h_len1 i hi; omega) ≠
                (words.val[j]).val[0]'(by have h := h_len1 j hj; omega)) → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, r = L1 * L2, where L1 and L2 are the two largest values in the multiset { len(words[i]) | 0 <= i < len(words) } counted with multiplicity (L1 >= L2).
  Preconditions: 2 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 1000 and every byte of words[i] is a lowercase English letter (97 <= byte <= 122). For every i and j with 0 <= i < j < len(words), letters(words[i]) ∩ letters(words[j]) = ∅, where letters(w) denotes the set of bytes occurring in w. -/
theorem spec_11 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_disj : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length), i < j →
      lettersDisjoint (words.val[i]) (words.val[j])) :
    ∀ (r : Std.I64) (L1 L2 : Nat), max_product words = Result.ok r →
      TwoLargest (lengths words) L1 L2 → r.val = (L1 : Int) * (L2 : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_disj : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length), i < j →
      lettersDisjoint (words.val[i]) (words.val[j])), ∀ (r : Std.I64) (L1 L2 : Nat), max_product words = Result.ok r →
      TwoLargest (lengths words) L1 L2 → r.val = (L1 : Int) * (L2 : Int)) := by
  sorry

/-- For every such pair of inputs, if max_product(words) returns r and max_product(words') returns r', then r = r'.
  Preconditions: words and words' are two slices each satisfying: 2 <= len <= 1000; every word has length between 1 and 1000; every byte is a lowercase English letter (97..122). Additionally, len(words') = len(words) and there is a bijection π from {0,...,len(words)-1} to {0,...,len(words)-1} such that for every k with 0 <= k < len(words), words'[k] = words[π(k)]. -/
theorem spec_12 (words words' : Slice (alloc.vec.Vec Std.U8))
    (h_in : ValidInput words) (h_in' : ValidInput words')
    (h_len : words'.val.length = words.val.length)
    (π : Nat → Nat)
    (hπ_lt : ∀ (k : Nat), k < words.val.length → π k < words.val.length)
    (hπ_inj : ∀ (k₁ k₂ : Nat), k₁ < words.val.length → k₂ < words.val.length →
      π k₁ = π k₂ → k₁ = k₂)
    (hπ : ∀ (k : Nat), k < words.val.length → words'.val[k]? = words.val[π k]?) :
    ∀ (r r' : Std.I64), max_product words = Result.ok r → max_product words' = Result.ok r' →
      r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8))
    (h_in : ValidInput words) (h_in' : ValidInput words')
    (h_len : words'.val.length = words.val.length)
    (π : Nat → Nat)
    (hπ_lt : ∀ (k : Nat), k < words.val.length → π k < words.val.length)
    (hπ_inj : ∀ (k₁ k₂ : Nat), k₁ < words.val.length → k₂ < words.val.length →
      π k₁ = π k₂ → k₁ = k₂)
    (hπ : ∀ (k : Nat), k < words.val.length → words'.val[k]? = words.val[π k]?), ∀ (r r' : Std.I64), max_product words = Result.ok r → max_product words' = Result.ok r' →
      r = r') := by
  sorry

/-- Let words' be the array obtained by appending w to words. If max_product(words) returns r and max_product(words') returns r', then r' >= r.
  Preconditions: words is a slice satisfying: 2 <= len(words) <= 1000; every word has length between 1 and 1000; every byte is a lowercase English letter (97..122). Also len(words) < 1000. w is a Vec U8 with 1 <= len(w) <= 1000 and every byte of w is a lowercase English letter (97..122). -/
theorem spec_13 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_len : words.val.length < 1000)
    (w : alloc.vec.Vec Std.U8) (h_w : 1 ≤ w.val.length ∧ w.val.length ≤ 1000)
    (h_wbytes : ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (words' : Slice (alloc.vec.Vec Std.U8)) (h_words' : words'.val = words.val ++ [w]) :
    ∀ (r r' : Std.I64), max_product words = Result.ok r → max_product words' = Result.ok r' →
      r.val ≤ r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_len : words.val.length < 1000)
    (w : alloc.vec.Vec Std.U8) (h_w : 1 ≤ w.val.length ∧ w.val.length ≤ 1000)
    (h_wbytes : ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (words' : Slice (alloc.vec.Vec Std.U8)) (h_words' : words'.val = words.val ++ [w]), ∀ (r r' : Std.I64), max_product words = Result.ok r → max_product words' = Result.ok r' →
      r.val ≤ r'.val) := by
  sorry

/-- Let words' be the array obtained by appending w to words. If max_product(words) returns r and max_product(words') returns r', then r' = r.
  Preconditions: words is a slice satisfying: 2 <= len(words) <= 1000; every word has length between 1 and 1000; every byte is a lowercase English letter (97..122). Also len(words) < 1000. w is a Vec U8 equal to words[k] for some k with 0 <= k < len(words). -/
theorem spec_14 (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_len : words.val.length < 1000)
    (w : alloc.vec.Vec Std.U8) (k : Nat) (hk : k < words.val.length)
    (h_w : w = words.val[k])
    (words' : Slice (alloc.vec.Vec Std.U8)) (h_words' : words'.val = words.val ++ [w]) :
    ∀ (r r' : Std.I64), max_product words = Result.ok r → max_product words' = Result.ok r' →
      r = r' := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h_in : ValidInput words)
    (h_len : words.val.length < 1000)
    (w : alloc.vec.Vec Std.U8) (k : Nat) (hk : k < words.val.length)
    (h_w : w = words.val[k])
    (words' : Slice (alloc.vec.Vec Std.U8)) (h_words' : words'.val = words.val ++ [w]), ∀ (r r' : Std.I64), max_product words = Result.ok r → max_product words' = Result.ok r' →
      r = r') := by
  sorry

end AegisSpec.MaxProduct
