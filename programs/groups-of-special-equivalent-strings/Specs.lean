import Aegis.NumSpecialEquivGroups.Code.Funs

/-!
# Specifications of `Aegis.NumSpecialEquivGroups.num_special_equiv_groups`

LeetCode problem `groups-of-special-equivalent-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumSpecialEquivGroups

def word (words : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : List Std.U8 :=
  match words.val[i]? with
  | some w => w.val
  | none => []

def IsLowerByte (c : Nat) : Prop := 97 ≤ c ∧ c ≤ 122

def IsLower (b : Std.U8) : Prop := IsLowerByte b.val

def countParity (w : List Std.U8) (p c : Nat) : Nat :=
  (w.zipIdx.filter (fun e => e.2 % 2 == p && e.1.val == c)).length

def countEven (w : List Std.U8) (c : Nat) : Nat := countParity w 0 c

def countOdd (w : List Std.U8) (c : Nat) : Nat := countParity w 1 c

def specialEquiv (w₁ w₂ : List Std.U8) : Prop :=
  ∀ c : Nat, IsLowerByte c →
    countEven w₁ c = countEven w₂ c ∧ countOdd w₁ c = countOdd w₂ c

def signature (w : List Std.U8) : List Nat :=
  (List.range 26).map (fun k => countEven w (97 + k)) ++
    (List.range 26).map (fun k => countOdd w (97 + k))

def numClasses (words : Slice (alloc.vec.Vec Std.U8)) (n : Nat) : Nat :=
  ((List.range n).map (fun i => signature (word words i))).dedup.length

def numDistinctWords (words : Slice (alloc.vec.Vec Std.U8)) (n : Nat) : Nat :=
  ((List.range n).map (fun i => word words i)).dedup.length

def firstByte (words : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : Std.U8 :=
  (word words i).headD default

def numDistinctFirstBytes (words : Slice (alloc.vec.Vec Std.U8)) (n : Nat) : Nat :=
  ((List.range n).map (fun i => firstByte words i)).dedup.length

/-- Whenever the function returns a result r, r is the number of equivalence classes of the following relation on the index set {0,1,...,n-1}: indices i and k are related if and only if, for every lowercase letter c, the number of even positions j with 0 <= j < m and words[i][j] = c equals the corresponding number for words[k], and the number of odd positions j with 0 <= j < m and words[i][j] = c equals the corresponding number for words[k]. Equivalently, r is the number of distinct pairs (E,O), where E is the multiset of even-indexed characters of some words[i] and O is the multiset of odd-indexed characters of that same words[i].
  Preconditions: Let n = len(words) and m = len(words[0]). Assume 1 <= n <= 1000, 1 <= m <= 20, every words[i] has length m, and every byte of every words[i] is an ASCII lowercase letter 'a'..'z'. -/
theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r) :
    r.val = (numClasses words n : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r), r.val = (numClasses words n : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: Let n = len(words) and m = len(words[0]). Assume 1 <= n <= 1000, 1 <= m <= 20, every words[i] has length m, and every byte of every words[i] is an ASCII lowercase letter 'a'..'z'. -/
theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b) :
    ∃ r : Std.I64, Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b), ∃ r : Std.I64, Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r.
  Preconditions: Let n = len(words) and m = len(words[0]). Assume 1 <= n <= 1000, 1 <= m <= 20, every words[i] has length m, and every byte of every words[i] is an ASCII lowercase letter 'a'..'z'. -/
theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= D, where D is the number of distinct byte strings among words[0], words[1], ..., words[n-1].
  Preconditions: Let n = len(words) and m = len(words[0]). Assume 1 <= n <= 1000, 1 <= m <= 20, every words[i] has length m, and every byte of every words[i] is an ASCII lowercase letter 'a'..'z'. -/
theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r) :
    r.val ≤ (numDistinctWords words n : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r), r.val ≤ (numDistinctWords words n : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if every two indices i,j with 0 <= i < n and 0 <= j < n are special-equivalent; here special-equivalent means that for every lowercase letter c, the number of occurrences of c at even positions of words[i] equals that of words[j], and the number of occurrences of c at odd positions of words[i] equals that of words[j].
  Preconditions: Let n = len(words) and m = len(words[0]). Assume 1 <= n <= 1000, 1 <= m <= 20, every words[i] has length m, and every byte of every words[i] is an ASCII lowercase letter 'a'..'z'. -/
theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r) :
    r.val = 1 ↔ ∀ i j, i < n → j < n → specialEquiv (word words i) (word words j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r), r.val = 1 ↔ ∀ i j, i < n → j < n → specialEquiv (word words i) (word words j)) := by
  sorry

/-- If for every pair of distinct indices i,j with 0 <= i < j < n, words[i] and words[j] are not special-equivalent (that is, for some lowercase letter c their even-position counts differ or their odd-position counts differ), then whenever the function returns a result r, r = n.
  Preconditions: Let n = len(words) and m = len(words[0]). Assume 1 <= n <= 1000, 1 <= m <= 20, every words[i] has length m, and every byte of every words[i] is an ASCII lowercase letter 'a'..'z'. -/
theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hpair : ∀ i j, i < j → j < n → ¬ specialEquiv (word words i) (word words j))
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r) :
    r.val = (n : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hpair : ∀ i j, i < j → j < n → ¬ specialEquiv (word words i) (word words j))
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r), r.val = (n : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of distinct byte values among the characters words[0][0], words[1][0], ..., words[n-1][0].
  Preconditions: Let n = len(words) and m = len(words[0]). Assume 1 <= n <= 1000, 1 <= m <= 20, every words[i] has length m, every byte is an ASCII lowercase letter 'a'..'z', and m = 1. -/
theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hm : m = 1)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r) :
    r.val = (numDistinctFirstBytes words n : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hm : m = 1)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r), r.val = (numDistinctFirstBytes words n : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of distinct two-byte strings among words[0], words[1], ..., words[n-1], i.e. the number of distinct pairs (words[i][0], words[i][1]).
  Preconditions: Let n = len(words) and m = len(words[0]). Assume 1 <= n <= 1000, 1 <= m <= 20, every words[i] has length m, every byte is an ASCII lowercase letter 'a'..'z', and m = 2. -/
theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hm : m = 2)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r) :
    r.val = (numDistinctWords words n : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hm : m = 2)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r), r.val = (numDistinctWords words n : ℤ)) := by
  sorry

/-- Whenever the function returns r on words and r' on words', r' = r if w is special-equivalent to at least one words[i] with 0 <= i < n, and r' = r + 1 otherwise. Here special-equivalent means the even-position and odd-position letter counts of w equal those of words[i] for every lowercase letter.
  Preconditions: Let n = len(words) and m = len(words[0]). Assume 1 <= n <= 1000, 1 <= m <= 20, every words[i] has length m, every byte is an ASCII lowercase letter 'a'..'z', and n < 1000. Let w be any byte string of length m with lowercase letters, and let words' be the array of length n+1 obtained by appending w after all words. -/
theorem spec_9 (words words' : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (w : alloc.vec.Vec Std.U8) (r r' : Std.I64)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hn_lt : n < 1000)
    (hw_len : w.val.length = m)
    (hw_lower : ∀ b ∈ w.val, IsLower b)
    (hwords' : words'.val = words.val ++ [w])
    (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r)
    (hr' : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words' = ok r') :
    ((∃ i, i < n ∧ specialEquiv w.val (word words i)) → r'.val = r.val) ∧
      ((¬ ∃ i, i < n ∧ specialEquiv w.val (word words i)) → r'.val = r.val + 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (w : alloc.vec.Vec Std.U8) (r r' : Std.I64)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hn_lt : n < 1000)
    (hw_len : w.val.length = m)
    (hw_lower : ∀ b ∈ w.val, IsLower b)
    (hwords' : words'.val = words.val ++ [w])
    (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r)
    (hr' : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words' = ok r'), ((∃ i, i < n ∧ specialEquiv w.val (word words i)) → r'.val = r.val) ∧
      ((¬ ∃ i, i < n ∧ specialEquiv w.val (word words i)) → r'.val = r.val + 1)) := by
  sorry

/-- Suppose there is a bijection p on {0,1,...,n-1} such that words'[i] is byte-for-byte equal to words[p(i)] for every i < n. Whenever the function returns r on words and r' on words', r = r'.
  Preconditions: Let words and words' both satisfy the common preconditions with the same n = len(words) = len(words') and the same m = len(words[0]) = len(words'[0]): 1 <= n <= 1000, 1 <= m <= 20, all strings have length m, and all bytes are ASCII lowercase 'a'..'z'. -/
theorem spec_10 (words words' : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (r r' : Std.I64) (p : Equiv.Perm (Fin n))
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n) (hlen' : words'.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hword_len' : ∀ i, i < n → (word words' i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hlower' : ∀ i, i < n → ∀ b ∈ word words' i, IsLower b)
    (hp : ∀ i : Fin n, word words' i.val = word words (p i).val)
    (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r)
    (hr' : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (r r' : Std.I64) (p : Equiv.Perm (Fin n))
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n) (hlen' : words'.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hword_len' : ∀ i, i < n → (word words' i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hlower' : ∀ i, i < n → ∀ b ∈ word words' i, IsLower b)
    (hp : ∀ i : Fin n, word words' i.val = word words (p i).val)
    (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r)
    (hr' : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words' = ok r'), r.val = r'.val) := by
  sorry

/-- Suppose that for every i < n, words'[i] and words[i] are special-equivalent, meaning that for every lowercase letter c the number of occurrences of c at even positions of words'[i] equals that of words[i], and the number of occurrences of c at odd positions of words'[i] equals that of words[i]. Whenever the function returns r on words and r' on words', r = r'.
  Preconditions: Let words and words' both satisfy the common preconditions with the same n = len(words) = len(words') and the same m = len(words[0]) = len(words'[0]): 1 <= n <= 1000, 1 <= m <= 20, all strings have length m, and all bytes are ASCII lowercase 'a'..'z'. -/
theorem spec_11 (words words' : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (r r' : Std.I64)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n) (hlen' : words'.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hword_len' : ∀ i, i < n → (word words' i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hlower' : ∀ i, i < n → ∀ b ∈ word words' i, IsLower b)
    (hequiv : ∀ i, i < n → specialEquiv (word words' i) (word words i))
    (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r)
    (hr' : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (r r' : Std.I64)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n) (hlen' : words'.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hword_len' : ∀ i, i < n → (word words' i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (hlower' : ∀ i, i < n → ∀ b ∈ word words' i, IsLower b)
    (hequiv : ∀ i, i < n → specialEquiv (word words' i) (word words i))
    (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r)
    (hr' : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a set R of exactly r indices with 0 <= i < n such that: (1) for any two distinct indices i,k in R, words[i] and words[k] are not special-equivalent; and (2) for every index k with 0 <= k < n, there is an index i in R such that words[k] and words[i] are special-equivalent. Special-equivalent has the usual meaning: equal counts of every lowercase letter at even positions and equal counts of every lowercase letter at odd positions.
  Preconditions: Let n = len(words) and m = len(words[0]). Assume 1 <= n <= 1000, 1 <= m <= 20, every words[i] has length m, and every byte of every words[i] is an ASCII lowercase letter 'a'..'z'. -/
theorem spec_12 (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r) :
    ∃ R : Finset Nat,
      (R.card : ℤ) = r.val ∧ (∀ i ∈ R, i < n) ∧
        (∀ i ∈ R, ∀ k ∈ R, i ≠ k → ¬ specialEquiv (word words i) (word words k)) ∧
        (∀ k, k < n → ∃ i ∈ R, specialEquiv (word words k) (word words i)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (n m : Nat)
    (hn_pos : 1 ≤ n) (hn_max : n ≤ 1000) (hm_pos : 1 ≤ m) (hm_max : m ≤ 20)
    (hlen : words.val.length = n)
    (hword_len : ∀ i, i < n → (word words i).length = m)
    (hlower : ∀ i, i < n → ∀ b ∈ word words i, IsLower b)
    (r : Std.I64) (hr : Aegis.NumSpecialEquivGroups.num_special_equiv_groups words = ok r), ∃ R : Finset Nat,
      (R.card : ℤ) = r.val ∧ (∀ i ∈ R, i < n) ∧
        (∀ i ∈ R, ∀ k ∈ R, i ≠ k → ¬ specialEquiv (word words i) (word words k)) ∧
        (∀ k, k < n → ∃ i ∈ R, specialEquiv (word words k) (word words i))) := by
  sorry

end AegisSpec.NumSpecialEquivGroups
