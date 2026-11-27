import Aegis.MinExtraChar.Code.Funs

/-!
# Specifications of `Aegis.MinExtraChar.min_extra_char`

LeetCode problem `extra-characters-in-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinExtraChar

  def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def AllLower (l : List Std.U8) : Prop := ∀ b ∈ l, IsLowerByte b

  def dictWords (dictionary : Slice (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
    dictionary.val.map (fun d => d.val)

  def dictBytes (dictionary : Slice (alloc.vec.Vec Std.U8)) : List Std.U8 :=
    (dictWords dictionary).flatten

  def firstBytes (dictionary : Slice (alloc.vec.Vec Std.U8)) : List Std.U8 :=
    (dictWords dictionary).filterMap (fun w => w.head?)

  def substr (l : List Std.U8) (i j : Nat) : List Std.U8 := (l.drop i).take (j - i)

  def IsDictionaryInterval (l : List Std.U8) (words : List (List Std.U8)) (i j : Nat) : Prop :=
    i < j ∧ j ≤ l.length ∧ ∃ w ∈ words, substr l i j = w

  def IsSelection (l : List Std.U8) (words : List (List Std.U8)) (sel : List (Nat × Nat)) : Prop :=
    sel.Pairwise (fun p q => p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
    ∀ p ∈ sel, IsDictionaryInterval l words p.1 p.2

  def coveredLength (sel : List (Nat × Nat)) : Nat := (sel.map (fun p => p.2 - p.1)).sum

  def IsMaxCovered (l : List Std.U8) (words : List (List Std.U8)) (m : Nat) : Prop :=
    (∃ sel : List (Nat × Nat), IsSelection l words sel ∧ coveredLength sel = m) ∧
    ∀ sel : List (Nat × Nat), IsSelection l words sel → coveredLength sel ≤ m

  def StrOk (s : Slice Std.U8) : Prop :=
    1 ≤ s.val.length ∧ s.val.length ≤ 50 ∧ AllLower s.val

  def DictOk (dictionary : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    1 ≤ dictionary.val.length ∧ dictionary.val.length ≤ 50 ∧
    (∀ d ∈ dictionary.val, 1 ≤ d.val.length ∧ d.val.length ≤ 50 ∧ AllLower d.val) ∧
    (dictWords dictionary).Nodup

  def InputOk (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    StrOk s ∧ DictOk dictionary

  /-- Let n = len(s). Call a selection a finite list of intervals (i_1,j_1),...,(i_t,j_t) with t >= 0 such that for each l, 0 <= i_l < j_l <= n, the contiguous substring s[i_l..j_l) (bytes s[i_l],...,s[j_l-1]) is equal to some word in dictionary, and the intervals are pairwise non-overlapping (for any two distinct l,l', either j_l <= i_{l'} or j_{l'} <= i_l). Let M be the maximum, over all selections, of the covered length sum_{l=1}^t (j_l - i_l), with M = 0 for the empty selection. The function returns a result r and r = n - M.
    Preconditions: 1 <= len(s) <= 50; 1 <= len(dictionary) <= 50; for every word d in dictionary, 1 <= len(d) <= 50; every byte of s and of every word in dictionary is an ASCII code of a lowercase English letter ('a' through 'z'); the words in dictionary are pairwise distinct. -/
  theorem spec_1 (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
      (h : InputOk s dictionary) :
      ∃ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r ∧
        ∃ m : Nat, IsMaxCovered s.val (dictWords dictionary) m ∧
          r.val = (s.val.length : Int) - (m : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
        (h : InputOk s dictionary), ∃ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r ∧
          ∃ m : Nat, IsMaxCovered s.val (dictWords dictionary) m ∧
            r.val = (s.val.length : Int) - (m : Int)) := by
    sorry

  /-- The function returns a result r (a successful I64 value); it never fails, panics, overflows, or accesses an out-of-bounds index on any input satisfying the preconditions.
    Preconditions: 1 <= len(s) <= 50; 1 <= len(dictionary) <= 50; for every word d in dictionary, 1 <= len(d) <= 50; every byte of s and of every word in dictionary is an ASCII code of a lowercase English letter ('a' through 'z'); the words in dictionary are pairwise distinct. -/
  theorem spec_2 (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
      (h : InputOk s dictionary) :
      ∃ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
        (h : InputOk s dictionary), ∃ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(s).
    Preconditions: 1 <= len(s) <= 50; 1 <= len(dictionary) <= 50; for every word d in dictionary, 1 <= len(d) <= 50; every byte of s and of every word in dictionary is an ASCII code of a lowercase English letter ('a' through 'z'); the words in dictionary are pairwise distinct. -/
  theorem spec_3 (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
      (h : InputOk s dictionary) :
      ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
        0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
        (h : InputOk s dictionary), ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
          0 ≤ r.val ∧ r.val ≤ (s.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a selection (a finite set of pairwise non-overlapping intervals in s, each equal to a dictionary word) whose covered length is exactly len(s) - r.
    Preconditions: 1 <= len(s) <= 50; 1 <= len(dictionary) <= 50; for every word d in dictionary, 1 <= len(d) <= 50; every byte of s and of every word in dictionary is an ASCII code of a lowercase English letter ('a' through 'z'); the words in dictionary are pairwise distinct. -/
  theorem spec_4 (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
      (h : InputOk s dictionary) :
      ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
        ∃ sel : List (Nat × Nat),
          IsSelection s.val (dictWords dictionary) sel ∧
            (coveredLength sel : Int) = (s.val.length : Int) - r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
        (h : InputOk s dictionary), ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
          ∃ sel : List (Nat × Nat),
            IsSelection s.val (dictWords dictionary) sel ∧
              (coveredLength sel : Int) = (s.val.length : Int) - r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every selection (a finite set of pairwise non-overlapping intervals in s, each equal to a dictionary word) the covered length of that selection is at most len(s) - r.
    Preconditions: 1 <= len(s) <= 50; 1 <= len(dictionary) <= 50; for every word d in dictionary, 1 <= len(d) <= 50; every byte of s and of every word in dictionary is an ASCII code of a lowercase English letter ('a' through 'z'); the words in dictionary are pairwise distinct. -/
  theorem spec_5 (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
      (h : InputOk s dictionary) :
      ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
        ∀ sel : List (Nat × Nat), IsSelection s.val (dictWords dictionary) sel →
          (coveredLength sel : Int) ≤ (s.val.length : Int) - r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
        (h : InputOk s dictionary), ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
          ∀ sel : List (Nat × Nat), IsSelection s.val (dictWords dictionary) sel →
            (coveredLength sel : Int) ≤ (s.val.length : Int) - r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there exists a selection whose covered length is len(s) (equivalently, s is the concatenation of one or more words from dictionary).
    Preconditions: 1 <= len(s) <= 50; 1 <= len(dictionary) <= 50; for every word d in dictionary, 1 <= len(d) <= 50; every byte of s and of every word in dictionary is an ASCII code of a lowercase English letter ('a' through 'z'); the words in dictionary are pairwise distinct. -/
  theorem spec_6 (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
      (h : InputOk s dictionary) :
      ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
        (r.val = 0 ↔
          ∃ sel : List (Nat × Nat),
            IsSelection s.val (dictWords dictionary) sel ∧
              coveredLength sel = s.val.length) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
        (h : InputOk s dictionary), ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
          (r.val = 0 ↔
            ∃ sel : List (Nat × Nat),
              IsSelection s.val (dictWords dictionary) sel ∧
                coveredLength sel = s.val.length)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(s) if and only if for every pair of indices i,j with 0 <= i < j <= len(s), the contiguous substring s[i..j) is not equal to any word in dictionary.
    Preconditions: 1 <= len(s) <= 50; 1 <= len(dictionary) <= 50; for every word d in dictionary, 1 <= len(d) <= 50; every byte of s and of every word in dictionary is an ASCII code of a lowercase English letter ('a' through 'z'); the words in dictionary are pairwise distinct. -/
  theorem spec_7 (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
      (h : InputOk s dictionary) :
      ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
        (r.val = (s.val.length : Int) ↔
          ∀ i j : Nat, i < j → j ≤ s.val.length →
            ¬ IsDictionaryInterval s.val (dictWords dictionary) i j) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
        (h : InputOk s dictionary), ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
          (r.val = (s.val.length : Int) ↔
            ∀ i j : Nat, i < j → j ≤ s.val.length →
              ¬ IsDictionaryInterval s.val (dictWords dictionary) i j)) := by
    sorry

  /-- Whenever the function returns r1 on input (s, dictionary1) and r2 on input (s, dictionary2), it holds r2 <= r1.
    Preconditions: s satisfies the constraints (1 <= len(s) <= 50 and all bytes are lowercase English letters); dictionary1 and dictionary2 each satisfy the constraints (1 <= number of entries <= 50, each word length 1..50, all lowercase English letters, pairwise distinct words); every word of dictionary1 is also a word of dictionary2. -/
  theorem spec_8 (s : Slice Std.U8)
      (dictionary1 dictionary2 : Slice (alloc.vec.Vec Std.U8))
      (hs : StrOk s) (h1 : DictOk dictionary1) (h2 : DictOk dictionary2)
      (hsub : ∀ w ∈ dictWords dictionary1, w ∈ dictWords dictionary2) :
      ∀ r1 r2 : I64,
        Aegis.MinExtraChar.min_extra_char s dictionary1 = ok r1 →
        Aegis.MinExtraChar.min_extra_char s dictionary2 = ok r2 → r2.val ≤ r1.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (dictionary1 dictionary2 : Slice (alloc.vec.Vec Std.U8))
        (hs : StrOk s) (h1 : DictOk dictionary1) (h2 : DictOk dictionary2)
        (hsub : ∀ w ∈ dictWords dictionary1, w ∈ dictWords dictionary2), ∀ r1 r2 : I64,
          Aegis.MinExtraChar.min_extra_char s dictionary1 = ok r1 →
          Aegis.MinExtraChar.min_extra_char s dictionary2 = ok r2 → r2.val ≤ r1.val) := by
    sorry

  /-- Whenever the function returns r on input (s, dictionary) and r' on input (s, the dictionary obtained by removing w), it holds r = r'.
    Preconditions: The pair (s, dictionary) satisfies the constraints; len(dictionary) >= 2; w is a word in dictionary; w is not equal to s[i..j) for any 0 <= i < j <= len(s); the dictionary obtained by removing w from dictionary also satisfies the constraints. -/
  theorem spec_9 (s : Slice Std.U8)
      (dictionary dictionary' : Slice (alloc.vec.Vec Std.U8)) (w : List Std.U8)
      (hs : StrOk s) (hd : DictOk dictionary) (hd' : DictOk dictionary')
      (hlen : 2 ≤ dictionary.val.length) (hw : w ∈ dictWords dictionary)
      (habsent : ∀ i j : Nat, i < j → j ≤ s.val.length → substr s.val i j ≠ w)
      (hdiff : ∀ x, x ∈ dictWords dictionary' ↔ x ∈ dictWords dictionary ∧ x ≠ w) :
      ∀ r r' : I64,
        Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
        Aegis.MinExtraChar.min_extra_char s dictionary' = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (dictionary dictionary' : Slice (alloc.vec.Vec Std.U8)) (w : List Std.U8)
        (hs : StrOk s) (hd : DictOk dictionary) (hd' : DictOk dictionary')
        (hlen : 2 ≤ dictionary.val.length) (hw : w ∈ dictWords dictionary)
        (habsent : ∀ i j : Nat, i < j → j ≤ s.val.length → substr s.val i j ≠ w)
        (hdiff : ∀ x, x ∈ dictWords dictionary' ↔ x ∈ dictWords dictionary ∧ x ≠ w), ∀ r r' : I64,
          Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
          Aegis.MinExtraChar.min_extra_char s dictionary' = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns r on input (s, dictionary) and r' on input (s, dictionary'), it holds r = r'.
    Preconditions: The pair (s, dictionary) satisfies the constraints; dictionary' is a permutation (reordering) of the entries of dictionary, so it also satisfies the constraints. -/
  theorem spec_10 (s : Slice Std.U8)
      (dictionary dictionary' : Slice (alloc.vec.Vec Std.U8))
      (hs : StrOk s) (hd : DictOk dictionary) (hd' : DictOk dictionary')
      (hperm : (dictWords dictionary').Perm (dictWords dictionary)) :
      ∀ r r' : I64,
        Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
        Aegis.MinExtraChar.min_extra_char s dictionary' = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (dictionary dictionary' : Slice (alloc.vec.Vec Std.U8))
        (hs : StrOk s) (hd : DictOk dictionary) (hd' : DictOk dictionary')
        (hperm : (dictWords dictionary').Perm (dictWords dictionary)), ∀ r r' : I64,
          Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
          Aegis.MinExtraChar.min_extra_char s dictionary' = ok r' → r = r') := by
    sorry

  /-- Let W = { dictionary[k][0] : 0 <= k < len(dictionary) }. Whenever the function returns a result r, r = len(s) - |{ i : 0 <= i < len(s) and s[i] in W }|; equivalently, r is the number of indices i with 0 <= i < len(s) and s[i] not in W.
    Preconditions: 1 <= len(s) <= 50; 1 <= len(dictionary) <= 50; every word in dictionary has length 1; every byte of s and of every word in dictionary is an ASCII code of a lowercase English letter ('a' through 'z'); the words in dictionary are pairwise distinct. -/
  theorem spec_11 (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
      (hs : StrOk s) (hd : DictOk dictionary)
      (hw : ∀ d ∈ dictionary.val, d.val.length = 1) :
      ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
        r.val = (s.val.length : Int) -
          ((s.val.filter (fun b => b ∈ firstBytes dictionary)).length : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
        (hs : StrOk s) (hd : DictOk dictionary)
        (hw : ∀ d ∈ dictionary.val, d.val.length = 1), ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
          r.val = (s.val.length : Int) -
            ((s.val.filter (fun b => b ∈ firstBytes dictionary)).length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if there exists a word d in dictionary with len(d) = 1 and d[0] = s[0], and r = 1 otherwise.
    Preconditions: 1 <= len(s) <= 50; len(s) = 1; 1 <= len(dictionary) <= 50; for every word d in dictionary, 1 <= len(d) <= 50; every byte of s and of every word in dictionary is an ASCII code of a lowercase English letter ('a' through 'z'); the words in dictionary are pairwise distinct. -/
  theorem spec_12 (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
      (h : InputOk s dictionary) (hlen : s.val.length = 1) :
      ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
        ((∃ d ∈ dictionary.val, d.val.length = 1 ∧ d.val[0]? = s.val[0]?) → r.val = 0) ∧
        ((¬ ∃ d ∈ dictionary.val, d.val.length = 1 ∧ d.val[0]? = s.val[0]?) → r.val = 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
        (h : InputOk s dictionary) (hlen : s.val.length = 1), ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
          ((∃ d ∈ dictionary.val, d.val.length = 1 ∧ d.val[0]? = s.val[0]?) → r.val = 0) ∧
          ((¬ ∃ d ∈ dictionary.val, d.val.length = 1 ∧ d.val[0]? = s.val[0]?) → r.val = 1)) := by
    sorry

  /-- Let V be the set of all bytes b such that b occurs at some position k of some word d in dictionary (0 <= k < len(d)). Whenever the function returns a result r, r >= |{ i : 0 <= i < len(s) and s[i] not in V }|.
    Preconditions: 1 <= len(s) <= 50; 1 <= len(dictionary) <= 50; for every word d in dictionary, 1 <= len(d) <= 50; every byte of s and of every word in dictionary is an ASCII code of a lowercase English letter ('a' through 'z'); the words in dictionary are pairwise distinct. -/
  theorem spec_13 (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
      (h : InputOk s dictionary) :
      ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
        ((s.val.filter (fun b => b ∉ dictBytes dictionary)).length : Int) ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8) (dictionary : Slice (alloc.vec.Vec Std.U8))
        (h : InputOk s dictionary), ∀ r : I64, Aegis.MinExtraChar.min_extra_char s dictionary = ok r →
          ((s.val.filter (fun b => b ∉ dictBytes dictionary)).length : Int) ≤ r.val) := by
    sorry

  end AegisSpec.MinExtraChar
