import Aegis.Supersequences.Code.Funs

/-!
# Specifications of `Aegis.Supersequences.supersequences`

LeetCode problem `frequencies-of-shortest-supersequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.Supersequences

  namespace AegisSpec.Supersequences

  def IsLowerByte (c : Nat) : Prop := 97 ≤ c ∧ c ≤ 122

  def IsLowerString (s : List Nat) : Prop := ∀ c ∈ s, IsLowerByte c

  def IsSubsequence (t s : List Nat) : Prop :=
    ∃ p : Fin t.length → Fin s.length,
      (∀ a b : Fin t.length, a < b → p a < p b) ∧
        ∀ k : Fin t.length, s.get (p k) = t.get k

  def IsCommonSupersequence (ws : List (List Nat)) (s : List Nat) : Prop :=
    ∀ w ∈ ws, IsSubsequence w s

  def IsSCS (ws : List (List Nat)) (s : List Nat) : Prop :=
    IsLowerString s ∧ IsCommonSupersequence ws s ∧
      ∀ s' : List Nat, IsLowerString s' → IsCommonSupersequence ws s' → s.length ≤ s'.length

  def countByte (s : List Nat) (j : Nat) : Nat := s.count (97 + j)

  def FreqVector (s : List Nat) : List Int :=
    (List.range 26).map (fun j => (countByte s j : Int))

  def rowInts (row : alloc.vec.Vec I64) : List Int := row.val.map (fun x => x.val)

  def RowIsFreq (row : alloc.vec.Vec I64) (s : List Nat) : Prop := rowInts row = FreqVector s

  def RowAt (r : alloc.vec.Vec (alloc.vec.Vec I64)) (i : Nat) (s : List Nat) : Prop :=
    ∃ h : i < r.val.length, RowIsFreq (r.val.get ⟨i, h⟩) s

  def entry (row : alloc.vec.Vec I64) (j : Nat) : Int := (rowInts row).getD j 0

  def wordBytes (w : alloc.vec.Vec U8) : List Nat := w.val.map (fun c => c.val)

  def wordsList (words : Slice (alloc.vec.Vec U8)) : List (List Nat) := words.val.map wordBytes

  def occurringBytes (words : Slice (alloc.vec.Vec U8)) : Finset Nat :=
    (wordsList words).flatten.toFinset

  /-- Let a string mean a finite sequence of bytes in the lowercase range 97..122. A string t is a subsequence of a string s if there are indices 0 <= p_0 < ... < p_{len(t)-1} < len(s) with s[p_k] = t[k]. A common supersequence of words is a string s such that every words[i] is a subsequence of s. Let M be the minimum length of a common supersequence (it exists, for example the concatenation of all words). An SCS is a common supersequence of length M. For any string s and any j with 0 <= j < 26, let F_s[j] be the number of indices p with 0 <= p < len(s) and s[p] = 97+j. The function returns a result r (it does not fail). The rows of r are exactly the set { F_s | s is an SCS }, with no repetitions: for every k with 0 <= k < len(r), r[k] = F_s for some SCS s; and for every SCS s there is exactly one k with r[k] = F_s. The order of the rows is unrestricted.
    Preconditions: words is a slice of byte vectors. Let n = len(words). 1 <= n <= 256. For every i with 0 <= i < n, len(words[i]) = 2, and for every j with 0 <= j < 2, 97 <= words[i][j] <= 122. For every i,k with 0 <= i < k < n, words[i] != words[k] as byte sequences. The set of bytes occurring in any word, { words[i][j] | 0 <= i < n and 0 <= j < 2 }, has at most 16 elements. -/
  theorem spec_1
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
        supersequences words = Result.ok r ∧
          (∀ (i : Nat) (hi : i < r.val.length), ∃ s : List Nat,
            IsLowerString s ∧ IsSCS (wordsList words) s ∧
              RowIsFreq (r.val.get ⟨i, hi⟩) s) ∧
          (∀ s : List Nat, IsLowerString s → IsSCS (wordsList words) s →
            ∃ i : Nat, RowAt r i s ∧ ∀ k : Nat, RowAt r k s → k = i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
          supersequences words = Result.ok r ∧
            (∀ (i : Nat) (hi : i < r.val.length), ∃ s : List Nat,
              IsLowerString s ∧ IsSCS (wordsList words) s ∧
                RowIsFreq (r.val.get ⟨i, hi⟩) s) ∧
            (∀ s : List Nat, IsLowerString s → IsSCS (wordsList words) s →
              ∃ i : Nat, RowAt r i s ∧ ∀ k : Nat, RowAt r k s → k = i)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result (it does not panic, overflow, or otherwise fail).
    Preconditions: words is a slice of byte vectors. Let n = len(words). 1 <= n <= 256. For every i with 0 <= i < n, len(words[i]) = 2, and for every j with 0 <= j < 2, 97 <= words[i][j] <= 122. For every i,k with 0 <= i < k < n, words[i] != words[k] as byte sequences. The set of bytes occurring in any word, { words[i][j] | 0 <= i < n and 0 <= j < 2 }, has at most 16 elements. -/
  theorem spec_2
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec I64), supersequences words = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64), supersequences words = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), len(r[i]) = 26.
    Preconditions: words is a slice of byte vectors. Let n = len(words). 1 <= n <= 256. For every i with 0 <= i < n, len(words[i]) = 2, and for every j with 0 <= j < 2, 97 <= words[i][j] <= 122. For every i,k with 0 <= i < k < n, words[i] != words[k] as byte sequences. The set of bytes occurring in any word, { words[i][j] | 0 <= i < n and 0 <= j < 2 }, has at most 16 elements. -/
  theorem spec_3
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16)
      (r : alloc.vec.Vec (alloc.vec.Vec I64))
      (hr : supersequences words = Result.ok r) :
      ∀ (i : Nat) (hi : i < r.val.length), (r.val.get ⟨i, hi⟩).val.length = 26 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16)
        (r : alloc.vec.Vec (alloc.vec.Vec I64))
        (hr : supersequences words = Result.ok r), ∀ (i : Nat) (hi : i < r.val.length), (r.val.get ⟨i, hi⟩).val.length = 26) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and every j with 0 <= j < 26, 0 <= r[i][j].
    Preconditions: words is a slice of byte vectors. Let n = len(words). 1 <= n <= 256. For every i with 0 <= i < n, len(words[i]) = 2, and for every j with 0 <= j < 2, 97 <= words[i][j] <= 122. For every i,k with 0 <= i < k < n, words[i] != words[k] as byte sequences. The set of bytes occurring in any word, { words[i][j] | 0 <= i < n and 0 <= j < 2 }, has at most 16 elements. -/
  theorem spec_4
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16)
      (r : alloc.vec.Vec (alloc.vec.Vec I64))
      (hr : supersequences words = Result.ok r) :
      ∀ (i : Nat) (hi : i < r.val.length) (j : Nat), j < 26 → 0 ≤ entry (r.val.get ⟨i, hi⟩) j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16)
        (r : alloc.vec.Vec (alloc.vec.Vec I64))
        (hr : supersequences words = Result.ok r), ∀ (i : Nat) (hi : i < r.val.length) (j : Nat), j < 26 → 0 ≤ entry (r.val.get ⟨i, hi⟩) j) := by
    sorry

  /-- Let M be the least length of a common supersequence of words, where a common supersequence is a string over bytes 97..122 that contains each words[q] as a subsequence (there are indices 0 <= p_0 < ... < p_{len(words[q])-1} < len(s) with s[p_k] = words[q][k]). Whenever the function returns a result r, for every i with 0 <= i < len(r), sum_{j=0}^{25} r[i][j] = M.
    Preconditions: words is a slice of byte vectors. Let n = len(words). 1 <= n <= 256. For every i with 0 <= i < n, len(words[i]) = 2, and for every j with 0 <= j < 2, 97 <= words[i][j] <= 122. For every i,k with 0 <= i < k < n, words[i] != words[k] as byte sequences. The set of bytes occurring in any word, { words[i][j] | 0 <= i < n and 0 <= j < 2 }, has at most 16 elements. -/
  theorem spec_5
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16)
      (r : alloc.vec.Vec (alloc.vec.Vec I64))
      (hr : supersequences words = Result.ok r) :
      ∃ M : Nat,
        (∃ s : List Nat,
          IsLowerString s ∧ IsCommonSupersequence (wordsList words) s ∧ s.length = M) ∧
          (∀ s : List Nat,
            IsLowerString s → IsCommonSupersequence (wordsList words) s → M ≤ s.length) ∧
          ∀ (i : Nat) (hi : i < r.val.length),
            (rowInts (r.val.get ⟨i, hi⟩)).sum = (M : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16)
        (r : alloc.vec.Vec (alloc.vec.Vec I64))
        (hr : supersequences words = Result.ok r), ∃ M : Nat,
          (∃ s : List Nat,
            IsLowerString s ∧ IsCommonSupersequence (wordsList words) s ∧ s.length = M) ∧
            (∀ s : List Nat,
              IsLowerString s → IsCommonSupersequence (wordsList words) s → M ≤ s.length) ∧
            ∀ (i : Nat) (hi : i < r.val.length),
              (rowInts (r.val.get ⟨i, hi⟩)).sum = (M : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), there exists a string s over bytes 97..122 such that: (a) s is a common supersequence of all words; (b) len(s) is the minimum possible length M of a common supersequence; (c) for every j with 0 <= j < 26, r[i][j] equals the number of indices p with 0 <= p < len(s) and s[p] = 97+j.
    Preconditions: words is a slice of byte vectors. Let n = len(words). 1 <= n <= 256. For every i with 0 <= i < n, len(words[i]) = 2, and for every j with 0 <= j < 2, 97 <= words[i][j] <= 122. For every i,k with 0 <= i < k < n, words[i] != words[k] as byte sequences. The set of bytes occurring in any word, { words[i][j] | 0 <= i < n and 0 <= j < 2 }, has at most 16 elements. -/
  theorem spec_6
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16)
      (r : alloc.vec.Vec (alloc.vec.Vec I64))
      (hr : supersequences words = Result.ok r) :
      ∀ (i : Nat) (hi : i < r.val.length), ∃ s : List Nat,
        IsLowerString s ∧
          IsCommonSupersequence (wordsList words) s ∧
            (∀ s' : List Nat,
              IsLowerString s' → IsCommonSupersequence (wordsList words) s' → s.length ≤ s'.length) ∧
            RowIsFreq (r.val.get ⟨i, hi⟩) s := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16)
        (r : alloc.vec.Vec (alloc.vec.Vec I64))
        (hr : supersequences words = Result.ok r), ∀ (i : Nat) (hi : i < r.val.length), ∃ s : List Nat,
          IsLowerString s ∧
            IsCommonSupersequence (wordsList words) s ∧
              (∀ s' : List Nat,
                IsLowerString s' → IsCommonSupersequence (wordsList words) s' → s.length ≤ s'.length) ∧
              RowIsFreq (r.val.get ⟨i, hi⟩) s) := by
    sorry

  /-- Whenever the function returns a result r, for every string s over bytes 97..122 that is a shortest common supersequence of words (i.e. s contains every words[q] as a subsequence and len(s) is the minimum possible such length M), there exists i with 0 <= i < len(r) such that for every j with 0 <= j < 26, r[i][j] equals the number of occurrences of byte 97+j in s.
    Preconditions: words is a slice of byte vectors. Let n = len(words). 1 <= n <= 256. For every i with 0 <= i < n, len(words[i]) = 2, and for every j with 0 <= j < 2, 97 <= words[i][j] <= 122. For every i,k with 0 <= i < k < n, words[i] != words[k] as byte sequences. The set of bytes occurring in any word, { words[i][j] | 0 <= i < n and 0 <= j < 2 }, has at most 16 elements. -/
  theorem spec_7
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16)
      (r : alloc.vec.Vec (alloc.vec.Vec I64))
      (hr : supersequences words = Result.ok r) :
      ∀ s : List Nat, IsLowerString s → IsSCS (wordsList words) s → ∃ i : Nat, RowAt r i s := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16)
        (r : alloc.vec.Vec (alloc.vec.Vec I64))
        (hr : supersequences words = Result.ok r), ∀ s : List Nat, IsLowerString s → IsSCS (wordsList words) s → ∃ i : Nat, RowAt r i s) := by
    sorry

  /-- Whenever the function returns a result r, for every i,k with 0 <= i < k < len(r), the rows r[i] and r[k] are different: there exists j with 0 <= j < 26 such that r[i][j] != r[k][j].
    Preconditions: words is a slice of byte vectors. Let n = len(words). 1 <= n <= 256. For every i with 0 <= i < n, len(words[i]) = 2, and for every j with 0 <= j < 2, 97 <= words[i][j] <= 122. For every i,k with 0 <= i < k < n, words[i] != words[k] as byte sequences. The set of bytes occurring in any word, { words[i][j] | 0 <= i < n and 0 <= j < 2 }, has at most 16 elements. -/
  theorem spec_8
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16)
      (r : alloc.vec.Vec (alloc.vec.Vec I64))
      (hr : supersequences words = Result.ok r) :
      ∀ (i k : Nat) (hi : i < r.val.length) (hk : k < r.val.length), i < k →
        ∃ j : Nat, j < 26 ∧ entry (r.val.get ⟨i, hi⟩) j ≠ entry (r.val.get ⟨k, hk⟩) j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16)
        (r : alloc.vec.Vec (alloc.vec.Vec I64))
        (hr : supersequences words = Result.ok r), ∀ (i k : Nat) (hi : i < r.val.length) (hk : k < r.val.length), i < k →
          ∃ j : Nat, j < 26 ∧ entry (r.val.get ⟨i, hi⟩) j ≠ entry (r.val.get ⟨k, hk⟩) j) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), every j with 0 <= j < 26, and every q with 0 <= q < len(words), r[i][j] >= C_j(words[q]), where C_j(w) is the number of indices p with 0 <= p < len(w) and w[p] = 97+j.
    Preconditions: words is a slice of byte vectors. Let n = len(words). 1 <= n <= 256. For every i with 0 <= i < n, len(words[i]) = 2, and for every j with 0 <= j < 2, 97 <= words[i][j] <= 122. For every i,k with 0 <= i < k < n, words[i] != words[k] as byte sequences. The set of bytes occurring in any word, { words[i][j] | 0 <= i < n and 0 <= j < 2 }, has at most 16 elements. -/
  theorem spec_9
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16)
      (r : alloc.vec.Vec (alloc.vec.Vec I64))
      (hr : supersequences words = Result.ok r) :
      ∀ (i : Nat) (hi : i < r.val.length) (j : Nat), j < 26 →
        ∀ (q : Nat) (hq : q < words.val.length),
          (countByte (wordBytes (words.val.get ⟨q, hq⟩)) j : Int) ≤ entry (r.val.get ⟨i, hi⟩) j := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16)
        (r : alloc.vec.Vec (alloc.vec.Vec I64))
        (hr : supersequences words = Result.ok r), ∀ (i : Nat) (hi : i < r.val.length) (j : Nat), j < 26 →
          ∀ (q : Nat) (hq : q < words.val.length),
            (countByte (wordBytes (words.val.get ⟨q, hq⟩)) j : Int) ≤ entry (r.val.get ⟨i, hi⟩) j) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < 26, if for every q with 0 <= q < len(words) and every p with 0 <= p < len(words[q]) we have words[q][p] != 97+j, then for every i with 0 <= i < len(r), r[i][j] = 0.
    Preconditions: words is a slice of byte vectors. Let n = len(words). 1 <= n <= 256. For every i with 0 <= i < n, len(words[i]) = 2, and for every j with 0 <= j < 2, 97 <= words[i][j] <= 122. For every i,k with 0 <= i < k < n, words[i] != words[k] as byte sequences. The set of bytes occurring in any word, { words[i][j] | 0 <= i < n and 0 <= j < 2 }, has at most 16 elements. -/
  theorem spec_10
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16)
      (r : alloc.vec.Vec (alloc.vec.Vec I64))
      (hr : supersequences words = Result.ok r) :
      ∀ j : Nat, j < 26 →
        (∀ w ∈ wordsList words, ∀ c ∈ w, c ≠ 97 + j) →
          ∀ (i : Nat) (hi : i < r.val.length), entry (r.val.get ⟨i, hi⟩) j = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16)
        (r : alloc.vec.Vec (alloc.vec.Vec I64))
        (hr : supersequences words = Result.ok r), ∀ j : Nat, j < 26 →
          (∀ w ∈ wordsList words, ∀ c ∈ w, c ≠ 97 + j) →
            ∀ (i : Nat) (hi : i < r.val.length), entry (r.val.get ⟨i, hi⟩) j = 0) := by
    sorry

  /-- Whenever the function returns a result r, len(r) >= 1.
    Preconditions: words is a slice of byte vectors. Let n = len(words). 1 <= n <= 256. For every i with 0 <= i < n, len(words[i]) = 2, and for every j with 0 <= j < 2, 97 <= words[i][j] <= 122. For every i,k with 0 <= i < k < n, words[i] != words[k] as byte sequences. The set of bytes occurring in any word, { words[i][j] | 0 <= i < n and 0 <= j < 2 }, has at most 16 elements. -/
  theorem spec_11
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16)
      (r : alloc.vec.Vec (alloc.vec.Vec I64))
      (hr : supersequences words = Result.ok r) :
      1 ≤ r.val.length := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16)
        (r : alloc.vec.Vec (alloc.vec.Vec I64))
        (hr : supersequences words = Result.ok r), 1 ≤ r.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and every j with 0 <= j < 26, r[i][j] <= sum_{q=0}^{len(words)-1} C_j(words[q]). (Each letter occurrence in a shortest common supersequence is needed by at least one word embedding, and a single word supplies at most C_j(words[q]) occurrences of letter j.)
    Preconditions: words is a slice of byte vectors with 1 <= n <= 256, each len(words[i]) = 2 with bytes in 97..122, words pairwise distinct, and at most 16 distinct bytes overall; C_j(w) = number of p with w[p] = 97+j. -/
  theorem spec_12
      (words : Slice (alloc.vec.Vec U8))
      (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
      (hlen : ∀ w ∈ words.val, w.val.length = 2)
      (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
      (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
        i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
      (hcard : (occurringBytes words).card ≤ 16)
      (r : alloc.vec.Vec (alloc.vec.Vec I64))
      (hr : supersequences words = Result.ok r) :
      ∀ (i : Nat) (hi : i < r.val.length) (j : Nat), j < 26 →
        entry (r.val.get ⟨i, hi⟩) j ≤
          (((wordsList words).map (fun w => countByte w j)).sum : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hn1 : 1 ≤ words.val.length) (hn256 : words.val.length ≤ 256)
        (hlen : ∀ w ∈ words.val, w.val.length = 2)
        (hbyte : ∀ w ∈ words.val, ∀ c ∈ w.val, IsLowerByte c.val)
        (hdistinct : ∀ (i k : Nat) (hi : i < words.val.length) (hk : k < words.val.length),
          i < k → words.val.get ⟨i, hi⟩ ≠ words.val.get ⟨k, hk⟩)
        (hcard : (occurringBytes words).card ≤ 16)
        (r : alloc.vec.Vec (alloc.vec.Vec I64))
        (hr : supersequences words = Result.ok r), ∀ (i : Nat) (hi : i < r.val.length) (j : Nat), j < 26 →
          entry (r.val.get ⟨i, hi⟩) j ≤
            (((wordsList words).map (fun w => countByte w j)).sum : Int)) := by
    sorry

  end AegisSpec.Supersequences
