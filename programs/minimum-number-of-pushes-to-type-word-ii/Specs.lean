import Aegis.MinimumPushes.Code.Funs

/-!
# Specifications of `Aegis.MinimumPushes.minimum_pushes`

LeetCode problem `minimum-number-of-pushes-to-type-word-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumPushes (minimum_pushes)

  namespace AegisSpec.MinimumPushes

  def lowercase : Finset ℕ := Finset.Icc 97 122

  def bytes (word : Slice Std.U8) : List ℕ := word.val.map (fun b => b.val)

  def freq (word : Slice Std.U8) (c : ℕ) : ℕ := (bytes word).count c

  def support (word : Slice Std.U8) : Finset ℕ := lowercase.filter (fun c => 0 < freq word c)

  def freqList (word : Slice Std.U8) : List ℕ :=
    (List.range 26).map (fun k => freq word (k + 97))

  def posFreqs (word : Slice Std.U8) : List ℕ :=
    (freqList word).filter (fun f => decide (0 < f))

  def descFreqs (word : Slice Std.U8) : List ℕ :=
    List.insertionSort (fun a b : ℕ => b ≤ a) (posFreqs word)

  def score (fs : List ℕ) : ℕ :=
    (fs.mapIdx (fun j f => f * (j / 8 + 1))).sum

  def IsRepeat (word word' : Slice Std.U8) (t : ℕ) : Prop :=
    word'.val = List.flatten (List.replicate t word.val)

  def IsKeyShape {D : Finset ℕ} (key : D → Fin 8) (p : D → ℕ) : Prop :=
    (∀ c, 1 ≤ p c) ∧
      ∀ k : Fin 8,
        (∀ c : D, key c ≠ k) ∨
          ∃ q : ℕ, 1 ≤ q ∧ Set.BijOn p {c : D | key c = k} (Set.Icc 1 q)

  /-- Let freq(c) be the number of indices i with 0 <= i < len(word) and word[i] = c, for each lowercase letter c with 97 <= c <= 122. Let D be the set of lowercase letters with freq(c) > 0, let m = |D|, and let f_1 >= f_2 >= ... >= f_m be the positive numbers freq(c) for c in D, listed in non-increasing order (ties may be broken arbitrarily). Whenever minimum_pushes(word) returns a result r, r = sum_{j=1}^{m} f_j * (floor((j-1)/8) + 1). Here j is 1-based and floor is integer division.
    Preconditions: 1 <= len(word) <= 100000, and for every i with 0 <= i < len(word), 97 <= word[i] <= 122 (word[i] is an ASCII lowercase English letter). -/
  theorem spec_1 (word : Slice Std.U8)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : minimum_pushes word = ok r) :
      r.val = ((score (descFreqs word) : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : minimum_pushes word = ok r), r.val = ((score (descFreqs word) : ℕ) : ℤ)) := by
    sorry

  /-- For every byte slice word satisfying the preconditions, minimum_pushes(word) returns a result r; it does not fail, overflow, panic, or run out of bounds.
    Preconditions: 1 <= len(word) <= 100000, and every byte of word is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
  theorem spec_2 (word : Slice Std.U8)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, minimum_pushes word = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, minimum_pushes word = ok r) := by
    sorry

  /-- Whenever minimum_pushes(word) returns a result r, r >= len(word).
    Preconditions: 1 <= len(word) <= 100000, and every byte of word is an ASCII lowercase English letter. -/
  theorem spec_3 (word : Slice Std.U8)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : minimum_pushes word = ok r) :
      (word.val.length : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : minimum_pushes word = ok r), (word.val.length : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever minimum_pushes(word) returns a result r, r <= len(word) * (floor((m-1)/8) + 1).
    Preconditions: 1 <= len(word) <= 100000, and every byte of word is an ASCII lowercase English letter. Let m be the number of distinct lowercase letters that occur at least once in word. -/
  theorem spec_4 (word : Slice Std.U8)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : minimum_pushes word = ok r) :
      r.val ≤ ((word.val.length * (((support word).card - 1) / 8 + 1) : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : minimum_pushes word = ok r), r.val ≤ ((word.val.length * (((support word).card - 1) / 8 + 1) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever minimum_pushes(word) returns a result r, r = len(word).
    Preconditions: 1 <= len(word) <= 100000, every byte of word is an ASCII lowercase English letter, and the number m of distinct letters occurring in word satisfies m <= 8. -/
  theorem spec_5 (word : Slice Std.U8)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hm : (support word).card ≤ 8)
      (r : Std.I64) (hr : minimum_pushes word = ok r) :
      r.val = (word.val.length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hm : (support word).card ≤ 8)
        (r : Std.I64) (hr : minimum_pushes word = ok r), r.val = (word.val.length : ℤ)) := by
    sorry

  /-- Whenever minimum_pushes(word) returns a result r, r > len(word).
    Preconditions: 1 <= len(word) <= 100000, every byte of word is an ASCII lowercase English letter, and the number m of distinct letters occurring in word satisfies m > 8. -/
  theorem spec_6 (word : Slice Std.U8)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hm : 8 < (support word).card)
      (r : Std.I64) (hr : minimum_pushes word = ok r) :
      (word.val.length : ℤ) < r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hm : 8 < (support word).card)
        (r : Std.I64) (hr : minimum_pushes word = ok r), (word.val.length : ℤ) < r.val) := by
    sorry

  /-- If for every lowercase letter c the number of indices i with word[i] = c equals the number of indices i with word'[i] = c, then whenever minimum_pushes(word) returns r and minimum_pushes(word') returns r', we have r = r'.
    Preconditions: word and word' are byte slices, each satisfying 1 <= len <= 100000 and having every byte in the ASCII lowercase range 97 through 122. -/
  theorem spec_7 (word word' : Slice Std.U8)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hlen_pos' : 1 ≤ word'.val.length) (hlen_le' : word'.val.length ≤ 100000)
      (hlower' : ∀ b ∈ word'.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hfreq : ∀ c ∈ lowercase, freq word c = freq word' c)
      (r r' : Std.I64) (hr : minimum_pushes word = ok r)
      (hr' : minimum_pushes word' = ok r') :
      r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word word' : Slice Std.U8)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hlen_pos' : 1 ≤ word'.val.length) (hlen_le' : word'.val.length ≤ 100000)
        (hlower' : ∀ b ∈ word'.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hfreq : ∀ c ∈ lowercase, freq word c = freq word' c)
        (r r' : Std.I64) (hr : minimum_pushes word = ok r)
        (hr' : minimum_pushes word' = ok r'), r = r') := by
    sorry

  /-- Whenever minimum_pushes(word) returns r and minimum_pushes(word') returns r', r' = t * r.
    Preconditions: word is a byte slice with 1 <= len(word) <= 100000 and every byte in the ASCII lowercase range 97 through 122. t is a positive integer with len(word) * t <= 100000, and word' is the byte slice of length len(word) * t defined by word'[i] = word[i mod len(word)] for all 0 <= i < len(word) * t, i.e. word' is t copies of word concatenated. -/
  theorem spec_8 (word word' : Slice Std.U8) (t : ℕ)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (ht_pos : 1 ≤ t) (ht_len : word.val.length * t ≤ 100000)
      (hrep : IsRepeat word word' t)
      (r r' : Std.I64) (hr : minimum_pushes word = ok r)
      (hr' : minimum_pushes word' = ok r') :
      r'.val = (t : ℤ) * r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word word' : Slice Std.U8) (t : ℕ)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (ht_pos : 1 ≤ t) (ht_len : word.val.length * t ≤ 100000)
        (hrep : IsRepeat word word' t)
        (r r' : Std.I64) (hr : minimum_pushes word = ok r)
        (hr' : minimum_pushes word' = ok r'), r'.val = (t : ℤ) * r.val) := by
    sorry

  /-- Whenever minimum_pushes(word) returns r and minimum_pushes(word') returns r', r = r'.
    Preconditions: word and word' are byte slices, each with 1 <= length <= 100000 and every byte in the ASCII lowercase range 97 through 122. Let pi be a bijection from the set {97,98,...,122} to itself. Assume len(word) = len(word') and word'[i] = pi(word[i]) for every 0 <= i < len(word). -/
  theorem spec_9 (word word' : Slice Std.U8) (π : ℕ → ℕ)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hlen_pos' : 1 ≤ word'.val.length) (hlen_le' : word'.val.length ≤ 100000)
      (hlower' : ∀ b ∈ word'.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hlen : word.val.length = word'.val.length)
      (hπ : Set.BijOn π (lowercase : Set ℕ) (lowercase : Set ℕ))
      (hmap : bytes word' = (bytes word).map π)
      (r r' : Std.I64) (hr : minimum_pushes word = ok r)
      (hr' : minimum_pushes word' = ok r') :
      r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word word' : Slice Std.U8) (π : ℕ → ℕ)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hlen_pos' : 1 ≤ word'.val.length) (hlen_le' : word'.val.length ≤ 100000)
        (hlower' : ∀ b ∈ word'.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hlen : word.val.length = word'.val.length)
        (hπ : Set.BijOn π (lowercase : Set ℕ) (lowercase : Set ℕ))
        (hmap : bytes word' = (bytes word).map π)
        (r r' : Std.I64) (hr : minimum_pushes word = ok r)
        (hr' : minimum_pushes word' = ok r'), r = r') := by
    sorry

  /-- Whenever minimum_pushes(word) returns r, there exist functions key: D -> {0,1,...,7} and p: D -> {1,2,...} such that: (1) for each k in {0,...,7}, if D_k = {c in D | key(c) = k}, then either D_k is empty or there exists an integer q_k >= 1 such that p restricted to D_k is a bijection onto {1,2,...,q_k}; and (2) r = sum_{c in D} freq(c) * p(c).
    Preconditions: 1 <= len(word) <= 100000, and every byte of word is an ASCII lowercase English letter (97 <= word[i] <= 122). Let D be the set of lowercase letters with positive frequency in word, and let freq(c) be the number of occurrences of c. -/
  theorem spec_10 (word : Slice Std.U8)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : minimum_pushes word = ok r) :
      ∃ (key : support word → Fin 8) (p : support word → ℕ),
        IsKeyShape key p ∧
          r.val =
            ((∑ c : support word, freq word (c : ℕ) * p c : ℕ) : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : minimum_pushes word = ok r), ∃ (key : support word → Fin 8) (p : support word → ℕ),
          IsKeyShape key p ∧
            r.val =
              ((∑ c : support word, freq word (c : ℕ) * p c : ℕ) : ℤ)) := by
    sorry

  /-- Whenever minimum_pushes(word) returns r, for every pair of functions key: D -> {0,1,...,7} and p: D -> {1,2,...} such that for each k in {0,...,7}, if D_k = {c in D | key(c) = k}, then either D_k is empty or there exists an integer q_k >= 1 such that p restricted to D_k is a bijection onto {1,2,...,q_k}, we have sum_{c in D} freq(c) * p(c) >= r.
    Preconditions: 1 <= len(word) <= 100000, and every byte of word is an ASCII lowercase English letter (97 <= word[i] <= 122). Let D be the set of lowercase letters with positive frequency in word, and let freq(c) be the number of occurrences of c. -/
  theorem spec_11 (word : Slice Std.U8)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : minimum_pushes word = ok r)
      (key : support word → Fin 8) (p : support word → ℕ)
      (hshape : IsKeyShape key p) :
      ((∑ c : support word, freq word (c : ℕ) * p c : ℕ) : ℤ) ≥ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : minimum_pushes word = ok r)
        (key : support word → Fin 8) (p : support word → ℕ)
        (hshape : IsKeyShape key p), ((∑ c : support word, freq word (c : ℕ) * p c : ℕ) : ℤ) ≥ r.val) := by
    sorry

  /-- Whenever minimum_pushes(word) returns r, r >= len(word) + sum_{j=9}^{m} f_j, where the sum is empty if m < 9.
    Preconditions: 1 <= len(word) <= 100000, and every byte of word is an ASCII lowercase English letter. Let D, m, and f_1 >= ... >= f_m be as in the main specification. -/
  theorem spec_12 (word : Slice Std.U8)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : minimum_pushes word = ok r) :
      (word.val.length : ℤ) + (((descFreqs word).drop 8).sum : ℤ) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : minimum_pushes word = ok r), (word.val.length : ℤ) + (((descFreqs word).drop 8).sum : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever minimum_pushes(word) returns r, there exist integers q_c for c in D such that: (1) 1 <= q_c <= 4 for every c in D; (2) for each k in {1,2,3,4}, the number of c in D with q_c = k is at most 8; and (3) r = sum_{c in D} freq(c) * q_c.
    Preconditions: 1 <= len(word) <= 100000, and every byte of word is an ASCII lowercase English letter. Let D be the set of lowercase letters with positive frequency in word, and let freq(c) be the number of occurrences of c. -/
  theorem spec_13 (word : Slice Std.U8)
      (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
      (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : minimum_pushes word = ok r) :
      ∃ q : support word → ℕ,
        (∀ c, 1 ≤ q c ∧ q c ≤ 4) ∧
          (∀ k : ℕ, 1 ≤ k → k ≤ 4 →
            (Finset.univ.filter (fun c : support word => q c = k)).card ≤ 8) ∧
            r.val =
              ((∑ c : support word, freq word (c : ℕ) * q c : ℕ) : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 100000)
        (hlower : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : minimum_pushes word = ok r), ∃ q : support word → ℕ,
          (∀ c, 1 ≤ q c ∧ q c ≤ 4) ∧
            (∀ k : ℕ, 1 ≤ k → k ≤ 4 →
              (Finset.univ.filter (fun c : support word => q c = k)).card ≤ 8) ∧
              r.val =
                ((∑ c : support word, freq word (c : ℕ) * q c : ℕ) : ℤ)) := by
    sorry

  end AegisSpec.MinimumPushes
