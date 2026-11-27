import Aegis.PossibleStringCount.Code.Funs

/-!
# Specifications of `Aegis.PossibleStringCount.possible_string_count`

LeetCode problem `find-the-original-typed-string-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PossibleStringCount

  open Aeneas.Std Aeneas.Std.Result Aegis.PossibleStringCount

  def allLowerBytes (l : List Std.U8) : Prop := ∀ b ∈ l, 97 ≤ b.val ∧ b.val ≤ 122

  def allBytesEqual (l : List Std.U8) : Prop :=
    ∀ (i j : ℕ), i < l.length → j < l.length → l[i]? = l[j]?

  def runStarts (l : List Std.U8) : ℕ :=
    (List.range l.length).countP (fun i => if i = 0 then true else decide (l[i]? ≠ l[i - 1]?))

  def adjEqualCount (l : List Std.U8) : ℕ :=
    (List.range (l.length - 1)).countP (fun i => decide (l[i]? = l[i + 1]?))

  def noAdjacentRepeat (l : List Std.U8) : Prop := ∀ i, i < l.length - 1 → l[i]? ≠ l[i + 1]?

  def deleteAt (l : List Std.U8) (i : ℕ) : List Std.U8 := l.take i ++ l.drop (i + 1)

  def IsPossibleOriginal (s w : List Std.U8) : Prop :=
    s = w ∨
      ∃ (a L k : ℕ) (b : Std.U8),
        a + L ≤ w.length ∧ 0 < k ∧ k < L ∧
          (∀ j, j < L → w[a + j]? = some b) ∧
            s = w.take a ++ List.replicate k b ++ w.drop (a + L)

  /-- The function returns a result r and r = 1 + sum over all maximal contiguous runs of equal bytes in word of (length of that run - 1). Equivalently, if R is the number of maximal contiguous runs of equal bytes (the count of indices i with 0 <= i < len(word) such that i = 0 or word[i] != word[i-1]), then r = 1 + len(word) - R. This r is the number of distinct strings Alice could have intended: either she made no mistake and the intended string is word itself, or she made exactly one overlong key press, in which case the intended string is obtained by choosing one maximal run of word and shortening it to any positive length strictly smaller than its length in word.
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, and for every i with 0 <= i < len(word), 97 <= word[i] <= 122 (word consists only of lowercase English letters). -/
  theorem spec_1 (word : Slice Std.U8)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val) :
      ∃ r, possible_string_count word = ok r ∧
        r.val = 1 + (word.val.length : ℤ) - (runStarts word.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val), ∃ r, possible_string_count word = ok r ∧
          r.val = 1 + (word.val.length : ℤ) - (runStarts word.val : ℤ)) := by
    sorry

  /-- For every word satisfying the preconditions, the function returns a result r; in particular, no arithmetic overflow, out-of-bounds access, or panic occurs.
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, and for every i with 0 <= i < len(word), 97 <= word[i] <= 122. -/
  theorem spec_2 (word : Slice Std.U8)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val) :
      ∃ r, possible_string_count word = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val), ∃ r, possible_string_count word = ok r) := by
    sorry

  /-- The function returns a result r and r >= 1.
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, and for every i with 0 <= i < len(word), 97 <= word[i] <= 122. -/
  theorem spec_3 (word : Slice Std.U8)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val) :
      ∃ r, possible_string_count word = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val), ∃ r, possible_string_count word = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= len(word).
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, and for every i with 0 <= i < len(word), 97 <= word[i] <= 122. -/
  theorem spec_4 (word : Slice Std.U8)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val) :
      ∃ r, possible_string_count word = ok r ∧ r.val ≤ (word.val.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val), ∃ r, possible_string_count word = ok r ∧ r.val ≤ (word.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: word is a slice of bytes (Std.U8) with len(word) = 1, and 97 <= word[0] <= 122. -/
  theorem spec_5 (word : Slice Std.U8)
      (hlen : word.val.length = 1)
      (hbytes : allLowerBytes word.val) :
      ∃ r, possible_string_count word = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen : word.val.length = 1)
        (hbytes : allLowerBytes word.val), ∃ r, possible_string_count word = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r and r = len(word).
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, for every i with 0 <= i < len(word), 97 <= word[i] <= 122, and for every i and j with 0 <= i < len(word) and 0 <= j < len(word), word[i] = word[j] (all bytes of word are equal). -/
  theorem spec_6 (word : Slice Std.U8)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val) (hconst : allBytesEqual word.val) :
      ∃ r, possible_string_count word = ok r ∧ r.val = (word.val.length : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val) (hconst : allBytesEqual word.val), ∃ r, possible_string_count word = ok r ∧ r.val = (word.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r and: r = 2 if word[0] = word[1], and r = 1 if word[0] != word[1].
    Preconditions: word is a slice of bytes (Std.U8) with len(word) = 2, and 97 <= word[0] <= 122 and 97 <= word[1] <= 122. -/
  theorem spec_7 (word : Slice Std.U8) (b₀ b₁ : Std.U8)
      (hword : word.val = [b₀, b₁])
      (hb₀ : 97 ≤ b₀.val ∧ b₀.val ≤ 122) (hb₁ : 97 ≤ b₁.val ∧ b₁.val ≤ 122) :
      ∃ r, possible_string_count word = ok r ∧
        (b₀ = b₁ → r.val = 2) ∧ (b₀ ≠ b₁ → r.val = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word : Slice Std.U8) (b₀ b₁ : Std.U8)
        (hword : word.val = [b₀, b₁])
        (hb₀ : 97 ≤ b₀.val ∧ b₀.val ≤ 122) (hb₁ : 97 ≤ b₁.val ∧ b₁.val ≤ 122), ∃ r, possible_string_count word = ok r ∧
          (b₀ = b₁ → r.val = 2) ∧ (b₀ ≠ b₁ → r.val = 1)) := by
    sorry

  /-- The function returns a result r and r = 1 + |{ i | 0 <= i < len(word) - 1 and word[i] = word[i+1] }|, where |...| denotes the number of such indices i.
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, and for every i with 0 <= i < len(word), 97 <= word[i] <= 122. -/
  theorem spec_8 (word : Slice Std.U8)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val) :
      ∃ r, possible_string_count word = ok r ∧
        r.val = 1 + (adjEqualCount word.val : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val), ∃ r, possible_string_count word = ok r ∧
          r.val = 1 + (adjEqualCount word.val : ℤ)) := by
    sorry

  /-- The function returns a result r and r = 1 if and only if for every i with 0 <= i < len(word) - 1, word[i] != word[i+1].
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, and for every i with 0 <= i < len(word), 97 <= word[i] <= 122. -/
  theorem spec_9 (word : Slice Std.U8)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val) :
      ∃ r, possible_string_count word = ok r ∧ (r.val = 1 ↔ noAdjacentRepeat word.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val), ∃ r, possible_string_count word = ok r ∧ (r.val = 1 ↔ noAdjacentRepeat word.val)) := by
    sorry

  /-- For every word satisfying the preconditions, if possible_string_count(word) returns r and possible_string_count(rev(word)) returns r', then r = r'.
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, and for every i with 0 <= i < len(word), 97 <= word[i] <= 122. Let rev(word) be the slice of length len(word) with rev(word)[i] = word[len(word)-1-i] for 0 <= i < len(word). -/
  theorem spec_10 (word word' : Slice Std.U8) (r r' : Std.I64)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val)
      (hrev : word'.val = word.val.reverse)
      (hr : possible_string_count word = ok r)
      (hr' : possible_string_count word' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word word' : Slice Std.U8) (r r' : Std.I64)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val)
        (hrev : word'.val = word.val.reverse)
        (hr : possible_string_count word = ok r)
        (hr' : possible_string_count word' = ok r'), r.val = r'.val) := by
    sorry

  /-- For every such word1 and word2, if len(word1) = len(word2) and R(word1) = R(word2), then whenever possible_string_count(word1) returns r1 and possible_string_count(word2) returns r2, we have r1 = r2.
    Preconditions: word1 and word2 are byte slices, each with length between 1 and 100 inclusive, and all bytes in 97..122. Let R(w) be the number of maximal contiguous runs of equal bytes in w (the count of indices i with 0 <= i < len(w) such that i = 0 or w[i] != w[i-1]). -/
  theorem spec_11 (word1 word2 : Slice Std.U8) (r1 r2 : Std.I64)
      (hlen1₁ : 1 ≤ word1.val.length) (hlen1₂ : word1.val.length ≤ 100)
      (hbytes1 : allLowerBytes word1.val)
      (hlen2₁ : 1 ≤ word2.val.length) (hlen2₂ : word2.val.length ≤ 100)
      (hbytes2 : allLowerBytes word2.val)
      (hlen : word1.val.length = word2.val.length)
      (hruns : runStarts word1.val = runStarts word2.val)
      (hr1 : possible_string_count word1 = ok r1)
      (hr2 : possible_string_count word2 = ok r2) :
      r1.val = r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (r1 r2 : Std.I64)
        (hlen1₁ : 1 ≤ word1.val.length) (hlen1₂ : word1.val.length ≤ 100)
        (hbytes1 : allLowerBytes word1.val)
        (hlen2₁ : 1 ≤ word2.val.length) (hlen2₂ : word2.val.length ≤ 100)
        (hbytes2 : allLowerBytes word2.val)
        (hlen : word1.val.length = word2.val.length)
        (hruns : runStarts word1.val = runStarts word2.val)
        (hr1 : possible_string_count word1 = ok r1)
        (hr2 : possible_string_count word2 = ok r2), r1.val = r2.val) := by
    sorry

  /-- The function returns a result r and r = len(word) if and only if all bytes of word are equal (i.e., word has exactly one maximal run).
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, and for every i with 0 <= i < len(word), 97 <= word[i] <= 122. -/
  theorem spec_12 (word : Slice Std.U8)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val) :
      ∃ r, possible_string_count word = ok r ∧
        (r.val = (word.val.length : ℤ) ↔ allBytesEqual word.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val), ∃ r, possible_string_count word = ok r ∧
          (r.val = (word.val.length : ℤ) ↔ allBytesEqual word.val)) := by
    sorry

  /-- If possible_string_count(word) returns r and possible_string_count(word') returns r', then r' = r.
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, all bytes in 97..122, and len(word) < 100. Let c be a byte with 97 <= c <= 122 and c != word[len(word)-1]. Let word' be the slice obtained by appending c to word. -/
  theorem spec_13 (word word' : Slice Std.U8) (c : Std.U8) (r r' : Std.I64)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val) (hlen_lt : word.val.length < 100)
      (hc : 97 ≤ c.val ∧ c.val ≤ 122)
      (hc_ne : word.val.getLast? ≠ some c)
      (happend : word'.val = word.val ++ [c])
      (hr : possible_string_count word = ok r)
      (hr' : possible_string_count word' = ok r') :
      r'.val = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (word word' : Slice Std.U8) (c : Std.U8) (r r' : Std.I64)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val) (hlen_lt : word.val.length < 100)
        (hc : 97 ≤ c.val ∧ c.val ≤ 122)
        (hc_ne : word.val.getLast? ≠ some c)
        (happend : word'.val = word.val ++ [c])
        (hr : possible_string_count word = ok r)
        (hr' : possible_string_count word' = ok r'), r'.val = r.val) := by
    sorry

  /-- If possible_string_count(word) returns r and possible_string_count(word') returns r', then r' = r + 1.
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, all bytes in 97..122, and len(word) < 100. Let c = word[len(word)-1]. Let word' be the slice obtained by appending c to word. -/
  theorem spec_14 (word word' : Slice Std.U8) (c : Std.U8) (r r' : Std.I64)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val) (hlen_lt : word.val.length < 100)
      (hc : 97 ≤ c.val ∧ c.val ≤ 122) (hlast : word.val.getLast? = some c)
      (happend : word'.val = word.val ++ [c])
      (hr : possible_string_count word = ok r)
      (hr' : possible_string_count word' = ok r') :
      r'.val = r.val + 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (word word' : Slice Std.U8) (c : Std.U8) (r r' : Std.I64)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val) (hlen_lt : word.val.length < 100)
        (hc : 97 ≤ c.val ∧ c.val ≤ 122) (hlast : word.val.getLast? = some c)
        (happend : word'.val = word.val ++ [c])
        (hr : possible_string_count word = ok r)
        (hr' : possible_string_count word' = ok r'), r'.val = r.val + 1) := by
    sorry

  /-- For every index i with 0 <= i < len(word) - 1 and word[i] = word[i+1], let s be the byte slice of length len(word)-1 obtained by deleting position i from word (s[j] = word[j] for j < i, and s[j] = word[j+1] for i <= j < len(word)-1). Then s is a possible original string: Alice could have typed s and produced word by pressing the key for that repeated character one extra time. Consequently, if there exists at least one such index i, then whenever the function returns r, r >= 2.
    Preconditions: word is a slice of bytes (Std.U8) with 1 <= len(word) <= 100, and for every i with 0 <= i < len(word), 97 <= word[i] <= 122. -/
  theorem spec_15 (word : Slice Std.U8)
      (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
      (hbytes : allLowerBytes word.val) :
      (∀ i, i < word.val.length - 1 → word.val[i]? = word.val[i + 1]? →
        IsPossibleOriginal (deleteAt word.val i) word.val) ∧
      ((∃ i, i < word.val.length - 1 ∧ word.val[i]? = word.val[i + 1]?) →
        ∀ r, possible_string_count word = ok r → 2 ≤ r.val) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 100)
        (hbytes : allLowerBytes word.val), (∀ i, i < word.val.length - 1 → word.val[i]? = word.val[i + 1]? →
          IsPossibleOriginal (deleteAt word.val i) word.val) ∧
        ((∃ i, i < word.val.length - 1 ∧ word.val[i]? = word.val[i + 1]?) →
          ∀ r, possible_string_count word = ok r → 2 ≤ r.val)) := by
    sorry

  end AegisSpec.PossibleStringCount
