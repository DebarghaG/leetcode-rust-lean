import Aegis.LongestStrChain.Code.Funs

/-!
# Specifications of `Aegis.LongestStrChain.longest_str_chain`

LeetCode problem `longest-string-chain`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  namespace AegisSpec.LongestStrChain

  open Aegis.LongestStrChain

  def IsValidWord (w : alloc.vec.Vec Std.U8) : Prop :=
    1 ≤ w.val.length ∧ w.val.length ≤ 16 ∧ ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122

  def IsValidInput (words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    1 ≤ words.val.length ∧ words.val.length ≤ 1000 ∧ ∀ w ∈ words.val, IsValidWord w

  def IsPredecessor (a b : List Std.U8) : Prop :=
    a.length + 1 = b.length ∧ ∃ p : Nat, p < b.length ∧ a = b.take p ++ b.drop (p + 1)

  def HasChainLen (words : Slice (alloc.vec.Vec Std.U8)) (k : Nat) : Prop :=
    ∃ idx : Fin k → Fin words.val.length, Function.Injective idx ∧
      ∀ (j : Nat) (hj : j + 1 < k),
        IsPredecessor ((words.val.get (idx ⟨j, Nat.lt_of_succ_lt hj⟩)).val)
                      ((words.val.get (idx ⟨j + 1, hj⟩)).val)

  def IsMaxChainLen (words : Slice (alloc.vec.Vec Std.U8)) (k : Nat) : Prop :=
    1 ≤ k ∧ HasChainLen words k ∧ ∀ m : Nat, 1 ≤ m → HasChainLen words m → m ≤ k

  def HasPredecessorPair (words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    ∃ i : Fin words.val.length, ∃ j : Fin words.val.length,
      i ≠ j ∧ IsPredecessor (words.val.get i).val (words.val.get j).val

  def wordLens (words : Slice (alloc.vec.Vec Std.U8)) : List Nat :=
    words.val.map (fun w => w.val.length)

  def minWordLen (words : Slice (alloc.vec.Vec Std.U8)) : Nat :=
    (wordLens words).min?.getD 0

  def maxWordLen (words : Slice (alloc.vec.Vec Std.U8)) : Nat :=
    (wordLens words).max?.getD 0

  /-- Whenever the function returns a result r, r is exactly the maximum length of a word chain from words: the largest integer k >= 1 for which there exist pairwise distinct indices i_1,...,i_k with 0 <= i_j < len(words) such that for every j with 1 <= j < k, words[i_j] is a predecessor of words[i_{j+1}]. Here a is a predecessor of b iff len(b) = len(a) + 1 and there is an index p with 0 <= p < len(b) such that for every t with 0 <= t < len(a), a[t] = b[t] when t < p, and a[t] = b[t+1] when t >= p; equivalently, b is obtained by inserting exactly one byte into a without changing the order of the other bytes.
    Preconditions: 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 16, and every byte of words[i] is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words) :
      ∀ r, longest_str_chain words = ok r →
        ∃ k : Nat, r.val = (k : Int) ∧ IsMaxChainLen words k := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words), ∀ r, longest_str_chain words = ok r →
          ∃ k : Nat, r.val = (k : Int) ∧ IsMaxChainLen words k) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow (all integer arithmetic stays within the i64 range), access memory out of bounds, or panic.
    Preconditions: 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 16, and every byte of words[i] is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words) :
      ∃ r : Std.I64, longest_str_chain words = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words), ∃ r : Std.I64, longest_str_chain words = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= len(words).
    Preconditions: 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 16, and every byte of words[i] is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words) :
      ∀ r, longest_str_chain words = ok r →
        1 ≤ r.val ∧ r.val ≤ (words.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words), ∀ r, longest_str_chain words = ok r →
          1 ≤ r.val ∧ r.val ≤ (words.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, let min_len = min_{0 <= i < len(words)} len(words[i]) and max_len = max_{0 <= i < len(words)} len(words[i]). Then r <= max_len - min_len + 1. In particular, since every word has length at most 16, r <= 16.
    Preconditions: 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 16, and every byte of words[i] is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words) :
      ∀ r, longest_str_chain words = ok r →
        r.val ≤ (maxWordLen words : Int) - (minWordLen words : Int) + 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words), ∀ r, longest_str_chain words = ok r →
          r.val ≤ (maxWordLen words : Int) - (minWordLen words : Int) + 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there do not exist indices i and j with 0 <= i < len(words), 0 <= j < len(words), and i != j such that words[i] is a predecessor of words[j]. Here a is a predecessor of b iff b can be obtained by inserting exactly one letter into a without changing the order of the other letters.
    Preconditions: 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 16, and every byte of words[i] is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words) :
      ∀ r, longest_str_chain words = ok r → (r.val = 1 ↔ ¬ HasPredecessorPair words) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words), ∀ r, longest_str_chain words = ok r → (r.val = 1 ↔ ¬ HasPredecessorPair words)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a word chain from words of length exactly r: there exist pairwise distinct indices i_1,...,i_r with 0 <= i_j < len(words) such that for every j with 1 <= j < r, words[i_j] is a predecessor of words[i_{j+1}] (predecessor as in the problem: the second word can be obtained by inserting exactly one letter into the first without changing the order of the other letters).
    Preconditions: 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 16, and every byte of words[i] is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words) :
      ∀ r, longest_str_chain words = ok r →
        ∃ k : Nat, r.val = (k : Int) ∧ HasChainLen words k := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words), ∀ r, longest_str_chain words = ok r →
          ∃ k : Nat, r.val = (k : Int) ∧ HasChainLen words k) := by
    sorry

  /-- Whenever the function returns a result r, every word chain from words has length at most r. Equivalently, there do not exist pairwise distinct indices i_1,...,i_{r+1} with 0 <= i_j < len(words) such that for every j with 1 <= j < r+1, words[i_j] is a predecessor of words[i_{j+1}] (predecessor as in the problem).
    Preconditions: 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 16, and every byte of words[i] is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words) :
      ∀ r, longest_str_chain words = ok r →
        ∀ k : Nat, HasChainLen words k → (k : Int) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words), ∀ r, longest_str_chain words = ok r →
          ∀ k : Nat, HasChainLen words k → (k : Int) ≤ r.val) := by
    sorry

  /-- If there is a bijection f from {0,...,len(words)-1} to itself such that words'[f(i)] = words[i] for every i with 0 <= i < len(words), then whenever longest_str_chain(words) returns r and longest_str_chain(words') returns r', we have r = r'.
    Preconditions: Both words and words' satisfy the common preconditions: 1 <= len(words) <= 1000, 1 <= len(words') <= 1000, every word has length 1..16, and all bytes are ASCII lowercase. Also len(words) = len(words'). -/
  theorem spec_8 (words words' : Slice (alloc.vec.Vec Std.U8))
      (h : IsValidInput words) (h' : IsValidInput words')
      (hlen : words.val.length = words'.val.length)
      (hperm : ∃ g : Fin words.val.length → Fin words'.val.length,
        Function.Bijective g ∧ ∀ i, words'.val.get (g i) = words.val.get i) :
      ∀ r r', longest_str_chain words = ok r → longest_str_chain words' = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8))
        (h : IsValidInput words) (h' : IsValidInput words')
        (hlen : words.val.length = words'.val.length)
        (hperm : ∃ g : Fin words.val.length → Fin words'.val.length,
          Function.Bijective g ∧ ∀ i, words'.val.get (g i) = words.val.get i), ∀ r r', longest_str_chain words = ok r → longest_str_chain words' = ok r' → r = r') := by
    sorry

  /-- If there is an injective function f from {0,...,len(words)-1} to {0,...,len(words')-1} such that words'[f(i)] = words[i] for every i with 0 <= i < len(words), then whenever longest_str_chain(words) returns r and longest_str_chain(words') returns r', we have r <= r'.
    Preconditions: Both words and words' satisfy the common preconditions: lengths between 1 and 1000, every word has length 1..16, and all bytes are ASCII lowercase. -/
  theorem spec_9 (words words' : Slice (alloc.vec.Vec Std.U8))
      (h : IsValidInput words) (h' : IsValidInput words')
      (hinj : ∃ g : Fin words.val.length → Fin words'.val.length,
        Function.Injective g ∧ ∀ i, words'.val.get (g i) = words.val.get i) :
      ∀ r r', longest_str_chain words = ok r → longest_str_chain words' = ok r' → r ≤ r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8))
        (h : IsValidInput words) (h' : IsValidInput words')
        (hinj : ∃ g : Fin words.val.length → Fin words'.val.length,
          Function.Injective g ∧ ∀ i, words'.val.get (g i) = words.val.get i), ∀ r r', longest_str_chain words = ok r → longest_str_chain words' = ok r' → r ≤ r') := by
    sorry

  /-- Whenever longest_str_chain(words) returns r and longest_str_chain(words') returns r', we have r = r'.
    Preconditions: Let words satisfy the common preconditions and additionally len(words) <= 999. Let q be an index with 0 <= q < len(words). Let words' be any array obtained from words by inserting one additional copy of words[q] at some position p with 0 <= p <= len(words) (so len(words') = len(words) + 1 and all other entries keep their relative order). Then words' also satisfies the problem constraints. -/
  theorem spec_10 (words words' : Slice (alloc.vec.Vec Std.U8))
      (h : IsValidInput words) (hlen : words.val.length ≤ 999)
      (p q : Nat) (hq : q < words.val.length) (hp : p ≤ words.val.length)
      (hins : words'.val = words.val.take p ++ [words.val.get ⟨q, hq⟩] ++ words.val.drop p)
      (h' : IsValidInput words') :
      ∀ r r', longest_str_chain words = ok r → longest_str_chain words' = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8))
        (h : IsValidInput words) (hlen : words.val.length ≤ 999)
        (p q : Nat) (hq : q < words.val.length) (hp : p ≤ words.val.length)
        (hins : words'.val = words.val.take p ++ [words.val.get ⟨q, hq⟩] ++ words.val.drop p)
        (h' : IsValidInput words'), ∀ r r', longest_str_chain words = ok r → longest_str_chain words' = ok r' → r = r') := by
    sorry

  /-- Whenever longest_str_chain(words) returns r and longest_str_chain(rev_words) returns r', we have r = r'.
    Preconditions: Let words satisfy the common preconditions. Let rev_words be the array of the same length such that for every i with 0 <= i < len(words), len(rev_words[i]) = len(words[i]) and rev_words[i][t] = words[i][len(words[i]) - 1 - t] for every t with 0 <= t < len(words[i]). Then rev_words also satisfies the problem constraints. -/
  theorem spec_11 (words rev_words : Slice (alloc.vec.Vec Std.U8))
      (h : IsValidInput words) (h' : IsValidInput rev_words)
      (hrev : rev_words.val.map (fun w => w.val) = words.val.map (fun w => w.val.reverse)) :
      ∀ r r', longest_str_chain words = ok r → longest_str_chain rev_words = ok r' → r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words rev_words : Slice (alloc.vec.Vec Std.U8))
        (h : IsValidInput words) (h' : IsValidInput rev_words)
        (hrev : rev_words.val.map (fun w => w.val) = words.val.map (fun w => w.val.reverse)), ∀ r r', longest_str_chain words = ok r → longest_str_chain rev_words = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r, if there exists a permutation i_1,...,i_{len(words)} of all indices 0,...,len(words)-1 (each index appears exactly once) such that for every j with 1 <= j < len(words), words[i_j] is a predecessor of words[i_{j+1}] (predecessor as in the problem), then r = len(words).
    Preconditions: 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 16, and every byte of words[i] is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_12 (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words)
      (hpath : ∃ idx : Fin words.val.length → Fin words.val.length,
        Function.Bijective idx ∧
          ∀ (j : Nat) (hj : j + 1 < words.val.length),
            IsPredecessor ((words.val.get (idx ⟨j, Nat.lt_of_succ_lt hj⟩)).val)
                          ((words.val.get (idx ⟨j + 1, hj⟩)).val)) :
      ∀ r, longest_str_chain words = ok r → r.val = (words.val.length : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (h : IsValidInput words)
        (hpath : ∃ idx : Fin words.val.length → Fin words.val.length,
          Function.Bijective idx ∧
            ∀ (j : Nat) (hj : j + 1 < words.val.length),
              IsPredecessor ((words.val.get (idx ⟨j, Nat.lt_of_succ_lt hj⟩)).val)
                            ((words.val.get (idx ⟨j + 1, hj⟩)).val)), ∀ r, longest_str_chain words = ok r → r.val = (words.val.length : Int)) := by
    sorry

  end AegisSpec.LongestStrChain
