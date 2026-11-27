import Aegis.FindSubstring.Code.Funs

/-!
# Specifications of `Aegis.FindSubstring.find_substring`

LeetCode problem `substring-with-concatenation-of-all-words`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindSubstring

def IsAsciiLower (b : U8) : Prop :=
  97 ≤ b.val ∧ b.val ≤ 122

def AllAsciiLower (l : List U8) : Prop :=
  ∀ b ∈ l, IsAsciiLower b

def blockAt (s : Slice U8) (off wl : ℕ) : List U8 :=
  (s.val.drop off).take wl

def wordBlock (w : alloc.vec.Vec U8) (wl : ℕ) : List U8 :=
  w.val.take wl

def IsValidStart (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ) (i : ℤ) : Prop :=
  0 ≤ i ∧
    i + ((words.val.length * wl : ℕ) : ℤ) ≤ ((s.val.length : ℕ) : ℤ) ∧
      ∃ σ : Equiv.Perm (Fin words.val.length),
        ∀ j : Fin words.val.length,
          blockAt s (i.toNat + j.val * wl) wl
            = wordBlock (words.val[(σ j).val]'(σ j).isLt) wl

def Occurs (r : alloc.vec.Vec I64) (x : ℤ) : Prop :=
  ∃ (q : ℕ) (hq : q < r.val.length), (r.val[q]'hq).val = x

noncomputable def validStarts (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ) :
    Finset ℤ := by
  classical
  exact ((List.range (s.val.length + 1)).map (fun n => (n : ℤ))).toFinset.filter
    (fun i => IsValidStart s words wl i)

/-- Whenever the function returns a result r, the entries of r are exactly the valid starting positions, each appearing exactly once, in any order. An integer i is a valid starting position exactly when: 0 <= i; i + L <= len(s); and there exists a permutation p of the index set {0,...,m-1} (a bijection from this set to itself) such that for every j with 0 <= j < m and every k with 0 <= k < wl, s[i + j*wl + k] = words[p[j]][k]. Equivalently, the m consecutive length-wl byte blocks of s[i .. i+L) have the same multiset as the entries of words. The entries of r are exactly the integers i satisfying this definition, each exactly once, and r contains no other integers.
  Preconditions: Let m = len(words), wl = len(words[0]), and L = m*wl. Assume the problem constraints: 1 <= len(s) <= 10000; 1 <= m <= 5000; 1 <= wl <= 30; for every j with 0 <= j < m, len(words[j]) = wl; s and all words[j] are ASCII lowercase byte arrays. -/
theorem spec_1
    (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val) :
    ∀ r : alloc.vec.Vec I64,
      Aegis.FindSubstring.find_substring s words = ok r →
        r.val.Nodup ∧ ∀ i : ℤ, IsValidStart s words wl i ↔ Occurs r i := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val), ∀ r : alloc.vec.Vec I64,
      Aegis.FindSubstring.find_substring s words = ok r →
        r.val.Nodup ∧ ∀ i : ℤ, IsValidStart s words wl i ↔ Occurs r i) := by
  sorry

/-- For every s and words satisfying the preconditions, the function returns a result r; it does not fail, overflow, or panic.
  Preconditions: Let m = len(words), wl = len(words[0]), and L = m*wl. Assume the problem constraints: 1 <= len(s) <= 10000; 1 <= m <= 5000; 1 <= wl <= 30; for every j with 0 <= j < m, len(words[j]) = wl; s and all words[j] are ASCII lowercase byte arrays. -/
theorem spec_2
    (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val) :
    ∃ r : alloc.vec.Vec I64, Aegis.FindSubstring.find_substring s words = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val), ∃ r : alloc.vec.Vec I64, Aegis.FindSubstring.find_substring s words = ok r) := by
  sorry

/-- Whenever the function returns r, for every q with 0 <= q < len(r), setting i = r[q], there exists a permutation p of {0,...,m-1} such that 0 <= i, i + L <= len(s), and for every j with 0 <= j < m and every k with 0 <= k < wl, s[i + j*wl + k] = words[p[j]][k].
  Preconditions: Let m = len(words), wl = len(words[0]), and L = m*wl. Assume the problem constraints: 1 <= len(s) <= 10000; 1 <= m <= 5000; 1 <= wl <= 30; for every j with 0 <= j < m, len(words[j]) = wl; s and all words[j] are ASCII lowercase byte arrays. -/
theorem spec_3
    (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val) :
    ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        ∀ (q : ℕ) (hq : q < r.val.length), IsValidStart s words wl (r.val[q]'hq).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val), ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        ∀ (q : ℕ) (hq : q < r.val.length), IsValidStart s words wl (r.val[q]'hq).val) := by
  sorry

/-- Whenever the function returns r, for every integer i, if 0 <= i, i + L <= len(s), and there exists a permutation p of {0,...,m-1} such that for every j with 0 <= j < m and every k with 0 <= k < wl, s[i + j*wl + k] = words[p[j]][k], then there exists q with 0 <= q < len(r) and r[q] = i.
  Preconditions: Let m = len(words), wl = len(words[0]), and L = m*wl. Assume the problem constraints: 1 <= len(s) <= 10000; 1 <= m <= 5000; 1 <= wl <= 30; for every j with 0 <= j < m, len(words[j]) = wl; s and all words[j] are ASCII lowercase byte arrays. -/
theorem spec_4
    (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val) :
    ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        ∀ i : ℤ, IsValidStart s words wl i → Occurs r i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val), ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        ∀ i : ℤ, IsValidStart s words wl i → Occurs r i) := by
  sorry

/-- Whenever the function returns r, for every q and q' with 0 <= q < len(r), 0 <= q' < len(r), and q != q', we have r[q] != r[q'].
  Preconditions: Let m = len(words), wl = len(words[0]), and L = m*wl. Assume the problem constraints: 1 <= len(s) <= 10000; 1 <= m <= 5000; 1 <= wl <= 30; for every j with 0 <= j < m, len(words[j]) = wl; s and all words[j] are ASCII lowercase byte arrays. -/
theorem spec_5
    (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val) :
    ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        ∀ (q q' : ℕ) (hq : q < r.val.length) (hq' : q' < r.val.length),
          q ≠ q' → (r.val[q]'hq).val ≠ (r.val[q']'hq').val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val), ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        ∀ (q q' : ℕ) (hq : q < r.val.length) (hq' : q' < r.val.length),
          q ≠ q' → (r.val[q]'hq).val ≠ (r.val[q']'hq').val) := by
  sorry

/-- Whenever the function returns r, for every q with 0 <= q < len(r), 0 <= r[q] and r[q] + L <= len(s).
  Preconditions: Let m = len(words), wl = len(words[0]), and L = m*wl. Assume the problem constraints: 1 <= len(s) <= 10000; 1 <= m <= 5000; 1 <= wl <= 30; for every j with 0 <= j < m, len(words[j]) = wl; s and all words[j] are ASCII lowercase byte arrays. -/
theorem spec_6
    (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val) :
    ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        ∀ (q : ℕ) (hq : q < r.val.length),
          0 ≤ (r.val[q]'hq).val ∧
            (r.val[q]'hq).val + ((words.val.length * wl : ℕ) : ℤ) ≤
              ((s.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val), ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        ∀ (q : ℕ) (hq : q < r.val.length),
          0 ≤ (r.val[q]'hq).val ∧
            (r.val[q]'hq).val + ((words.val.length * wl : ℕ) : ℤ) ≤
              ((s.val.length : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns r, len(r) <= (if L <= len(s) then len(s) - L + 1 else 0).
  Preconditions: Let m = len(words), wl = len(words[0]), and L = m*wl. Assume the problem constraints: 1 <= len(s) <= 10000; 1 <= m <= 5000; 1 <= wl <= 30; for every j with 0 <= j < m, len(words[j]) = wl; s and all words[j] are ASCII lowercase byte arrays. -/
theorem spec_7
    (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val) :
    ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        r.val.length ≤
          (if words.val.length * wl ≤ s.val.length
            then s.val.length - words.val.length * wl + 1 else 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val), ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        r.val.length ≤
          (if words.val.length * wl ≤ s.val.length
            then s.val.length - words.val.length * wl + 1 else 0)) := by
  sorry

/-- For every list words' of length m that is a permutation of words (it has the same multiset of byte strings), whenever find_substring(s, words) returns r and find_substring(s, words') returns r', for every integer x, x occurs in r if and only if x occurs in r'.
  Preconditions: Let m = len(words), wl = len(words[0]), and L = m*wl. Assume the problem constraints: 1 <= len(s) <= 10000; 1 <= m <= 5000; 1 <= wl <= 30; for every j with 0 <= j < m, len(words[j]) = wl; s and all words[j] are ASCII lowercase byte arrays. -/
theorem spec_8
    (s : Slice U8) (words words' : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val)
    (hwords' : words'.val.Perm words.val) :
    ∀ (r r' : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        Aegis.FindSubstring.find_substring s words' = ok r' →
          ∀ x : ℤ, Occurs r x ↔ Occurs r' x := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (words words' : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val)
    (hwords' : words'.val.Perm words.val), ∀ (r r' : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        Aegis.FindSubstring.find_substring s words' = ok r' →
          ∀ x : ℤ, Occurs r x ↔ Occurs r' x) := by
  sorry

/-- Whenever the function returns r, len(r) equals the number of integers i satisfying: 0 <= i, i + L <= len(s), and there exists a permutation p of {0,...,m-1} with s[i + j*wl + k] = words[p[j]][k] for every j with 0 <= j < m and every k with 0 <= k < wl.
  Preconditions: Let m = len(words), wl = len(words[0]), and L = m*wl. Assume the problem constraints: 1 <= len(s) <= 10000; 1 <= m <= 5000; 1 <= wl <= 30; for every j with 0 <= j < m, len(words[j]) = wl; s and all words[j] are ASCII lowercase byte arrays. -/
theorem spec_9
    (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val) :
    ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        r.val.length = (validStarts s words wl).card := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8)) (wl : ℕ)
    (hs_len : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 10000)
    (hm_len : 1 ≤ words.val.length) (hm_len_le : words.val.length ≤ 5000)
    (hwl_words : ∀ w ∈ words.val, w.val.length = wl)
    (hwl_pos : 1 ≤ wl) (hwl_le : wl ≤ 30)
    (hs_ascii : AllAsciiLower s.val)
    (hwords_ascii : ∀ w ∈ words.val, AllAsciiLower w.val), ∀ (r : alloc.vec.Vec I64),
      Aegis.FindSubstring.find_substring s words = ok r →
        r.val.length = (validStarts s words wl).card) := by
  sorry

end AegisSpec.FindSubstring
