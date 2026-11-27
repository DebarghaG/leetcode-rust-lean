import Aegis.IsItPossible.Code.Funs

/-!
# Specifications of `Aegis.IsItPossible.is_it_possible`

LeetCode problem `make-number-of-distinct-characters-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsItPossible

  abbrev Byte : Type := Aeneas.Std.U8

  abbrev ByteSlice : Type := Aeneas.Std.Slice Aeneas.Std.U8

  def isLowerByte (b : Byte) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def allLower (s : List Byte) : Prop := ∀ b ∈ s, isLowerByte b

  def distinctCount (s : List Byte) : Nat := (s.map fun b => b.val).dedup.length

  def freq (s : List Byte) (c : Nat) : Nat := (s.filter fun b => b.val = c).length

  def occurs (s : List Byte) (c : Nat) : Prop := 1 ≤ freq s c

  def occDisjoint (s t : List Byte) : Prop := ∀ c : Nat, ¬ (occurs s c ∧ occurs t c)

  def setAt (s : List Byte) (i : Nat) (b : Byte) : List Byte :=
    s.take i ++ [b] ++ s.drop (i + 1)

  def countNe (s : List Byte) (a : Byte) : Nat := (s.filter fun b => b.val ≠ a.val).length

  def hasSingleton (s : List Byte) : Prop := ∃ c : Nat, freq s c = 1

  def hasRepeat (s : List Byte) : Prop := ∃ c : Nat, 2 ≤ freq s c

  def singletonsAndRepeats (s t : List Byte) : Prop :=
    distinctCount t < distinctCount s ∧ hasSingleton s ∧ hasRepeat t ∨
      distinctCount s < distinctCount t ∧ hasSingleton t ∧ hasRepeat s

  /-- The function returns a Boolean r and does not fail. Let D(s) be the number of distinct bytes occurring in a slice s. For 0 <= i < len(word1) and 0 <= j < len(word2), let swap1(i,j) be word1 with position i replaced by word2[j], and let swap2(i,j) be word2 with position j replaced by word1[i]. Then r = true if and only if there exist such i,j with D(swap1(i,j)) = D(swap2(i,j)). Equivalently, r is true exactly when some single swap of one character of word1 with one character of word2 makes the two resulting strings have the same number of distinct characters.
    Preconditions: word1 and word2 are nonempty byte slices with 1 <= len(word1), len(word2) <= 100000, and every byte of both is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_1 (word1 word2 : ByteSlice)
      (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
      (h1lo : allLower word1.val)
      (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
      (h2lo : allLower word2.val) :
      ∃ r : Bool,
        Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
          (r = true ↔
            ∃ (i : Nat) (_hi : i < word1.val.length) (j : Nat) (_hj : j < word2.val.length),
              distinctCount (setAt word1.val i (word2.val[j]'_hj)) =
                distinctCount (setAt word2.val j (word1.val[i]'_hi))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word1 word2 : ByteSlice)
        (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
        (h1lo : allLower word1.val)
        (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
        (h2lo : allLower word2.val), ∃ r : Bool,
          Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
            (r = true ↔
              ∃ (i : Nat) (_hi : i < word1.val.length) (j : Nat) (_hj : j < word2.val.length),
                distinctCount (setAt word1.val i (word2.val[j]'_hj)) =
                  distinctCount (setAt word2.val j (word1.val[i]'_hi)))) := by
    sorry

  /-- There exists a Boolean r such that is_it_possible(word1, word2) = Result.ok r; that is, on every input satisfying the preconditions the function never fails, panics, performs an out-of-bounds access, or overflows.
    Preconditions: word1 and word2 are nonempty byte slices with 1 <= len(word1), len(word2) <= 100000, and every byte of both is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_2 (word1 word2 : ByteSlice)
      (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
      (h1lo : allLower word1.val)
      (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
      (h2lo : allLower word2.val) :
      ∃ r : Bool, Aegis.IsItPossible.is_it_possible word1 word2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word1 word2 : ByteSlice)
        (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
        (h1lo : allLower word1.val)
        (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
        (h2lo : allLower word2.val), ∃ r : Bool, Aegis.IsItPossible.is_it_possible word1 word2 = ok r) := by
    sorry

  /-- Both calls is_it_possible(word1, word2) and is_it_possible(word2, word1) return Boolean values, and those two Boolean values are equal.
    Preconditions: word1 and word2 are nonempty byte slices with 1 <= len(word1), len(word2) <= 100000, and every byte of both is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_3 (word1 word2 : ByteSlice)
      (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
      (h1lo : allLower word1.val)
      (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
      (h2lo : allLower word2.val) :
      ∃ r r' : Bool,
        Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
          Aegis.IsItPossible.is_it_possible word2 word1 = ok r' ∧ r = r' := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word1 word2 : ByteSlice)
        (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
        (h1lo : allLower word1.val)
        (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
        (h2lo : allLower word2.val), ∃ r r' : Bool,
          Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
            Aegis.IsItPossible.is_it_possible word2 word1 = ok r' ∧ r = r') := by
    sorry

  /-- Both is_it_possible(word1, word2) and is_it_possible(word1', word2') return Boolean values, and those values are equal.
    Preconditions: word1, word2, word1', word2' are nonempty byte slices with lengths at most 100000 and lowercase English letters; word1' is a permutation of word1 (same length and, for every byte c, freq_{word1'}(c) = freq_{word1}(c)) and word2' is a permutation of word2. -/
  theorem spec_4 (word1 word2 word1' word2' : ByteSlice)
      (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
      (h1lo : allLower word1.val)
      (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
      (h2lo : allLower word2.val)
      (h1'ne : 1 ≤ word1'.val.length) (h1'le : word1'.val.length ≤ 100000)
      (h1'lo : allLower word1'.val)
      (h2'ne : 1 ≤ word2'.val.length) (h2'le : word2'.val.length ≤ 100000)
      (h2'lo : allLower word2'.val)
      (hperm1 : word1'.val.length = word1.val.length)
      (hperm1freq : ∀ c : Nat, freq word1'.val c = freq word1.val c)
      (hperm2 : word2'.val.length = word2.val.length)
      (hperm2freq : ∀ c : Nat, freq word2'.val c = freq word2.val c) :
      ∃ r r' : Bool,
        Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
          Aegis.IsItPossible.is_it_possible word1' word2' = ok r' ∧ r = r' := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word1 word2 word1' word2' : ByteSlice)
        (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
        (h1lo : allLower word1.val)
        (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
        (h2lo : allLower word2.val)
        (h1'ne : 1 ≤ word1'.val.length) (h1'le : word1'.val.length ≤ 100000)
        (h1'lo : allLower word1'.val)
        (h2'ne : 1 ≤ word2'.val.length) (h2'le : word2'.val.length ≤ 100000)
        (h2'lo : allLower word2'.val)
        (hperm1 : word1'.val.length = word1.val.length)
        (hperm1freq : ∀ c : Nat, freq word1'.val c = freq word1.val c)
        (hperm2 : word2'.val.length = word2.val.length)
        (hperm2freq : ∀ c : Nat, freq word2'.val c = freq word2.val c), ∃ r r' : Bool,
          Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
            Aegis.IsItPossible.is_it_possible word1' word2' = ok r' ∧ r = r') := by
    sorry

  /-- The function returns a Boolean r with r = false.
    Preconditions: word1 and word2 are nonempty byte slices with 1 <= len(word1), len(word2) <= 100000, and every byte of both is an ASCII lowercase English letter. Let D(s) be the number of distinct bytes in s. Then |D(word1) - D(word2)| >= 3. -/
  theorem spec_5 (word1 word2 : ByteSlice)
      (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
      (h1lo : allLower word1.val)
      (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
      (h2lo : allLower word2.val)
      (hgap : 3 ≤ max (distinctCount word1.val) (distinctCount word2.val) -
        min (distinctCount word1.val) (distinctCount word2.val)) :
      ∃ r : Bool,
        Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧ r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word1 word2 : ByteSlice)
        (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
        (h1lo : allLower word1.val)
        (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
        (h2lo : allLower word2.val)
        (hgap : 3 ≤ max (distinctCount word1.val) (distinctCount word2.val) -
          min (distinctCount word1.val) (distinctCount word2.val)), ∃ r : Bool,
          Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧ r = false) := by
    sorry

  /-- The function returns a Boolean r with r = true.
    Preconditions: word1 and word2 are nonempty byte slices with 1 <= len(word1), len(word2) <= 100000, and every byte of both is an ASCII lowercase English letter. Let D(s) be the number of distinct bytes in s. Assume D(word1) = D(word2), and there exist indices i,j with 0 <= i < len(word1), 0 <= j < len(word2), and word1[i] = word2[j]. -/
  theorem spec_6 (word1 word2 : ByteSlice)
      (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
      (h1lo : allLower word1.val)
      (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
      (h2lo : allLower word2.val)
      (hD : distinctCount word1.val = distinctCount word2.val)
      (hwit : ∃ (i : Nat) (_hi : i < word1.val.length)
        (j : Nat) (_hj : j < word2.val.length), word1.val[i]'_hi = word2.val[j]'_hj) :
      ∃ r : Bool,
        Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧ r = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word1 word2 : ByteSlice)
        (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
        (h1lo : allLower word1.val)
        (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
        (h2lo : allLower word2.val)
        (hD : distinctCount word1.val = distinctCount word2.val)
        (hwit : ∃ (i : Nat) (_hi : i < word1.val.length)
          (j : Nat) (_hj : j < word2.val.length), word1.val[i]'_hi = word2.val[j]'_hj), ∃ r : Bool,
          Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧ r = true) := by
    sorry

  /-- The function returns a Boolean r with r = true if and only if at least one of these two conditions holds: (a) there is a byte c with freq_{word1}(c) = 1 and a byte d with freq_{word2}(d) = 1; (b) there is a byte c with freq_{word1}(c) >= 2 and a byte d with freq_{word2}(d) >= 2.
    Preconditions: word1 and word2 are nonempty byte slices with 1 <= len(word1), len(word2) <= 100000, and every byte of both is an ASCII lowercase English letter. Let D(s) be the number of distinct bytes in s, and let C(s) be the set of bytes occurring in s. Assume C(word1) and C(word2) are disjoint, and D(word1) = D(word2). -/
  theorem spec_7 (word1 word2 : ByteSlice)
      (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
      (h1lo : allLower word1.val)
      (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
      (h2lo : allLower word2.val)
      (hdisj : occDisjoint word1.val word2.val)
      (hD : distinctCount word1.val = distinctCount word2.val) :
      ∃ r : Bool,
        Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
          (r = true ↔
            (hasSingleton word1.val ∧ hasSingleton word2.val) ∨
              (hasRepeat word1.val ∧ hasRepeat word2.val)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word1 word2 : ByteSlice)
        (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
        (h1lo : allLower word1.val)
        (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
        (h2lo : allLower word2.val)
        (hdisj : occDisjoint word1.val word2.val)
        (hD : distinctCount word1.val = distinctCount word2.val), ∃ r : Bool,
          Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
            (r = true ↔
              (hasSingleton word1.val ∧ hasSingleton word2.val) ∨
                (hasRepeat word1.val ∧ hasRepeat word2.val))) := by
    sorry

  /-- The function returns a Boolean r with r = true if and only if there is at most one index j with 0 <= j < len(word2) and word2[j] != a.
    Preconditions: word1 and word2 are nonempty byte slices with 1 <= len(word1), len(word2) <= 100000, and every byte of both is an ASCII lowercase English letter. Assume len(word1) = 1, and let a = word1[0]. -/
  theorem spec_8 (word1 word2 : ByteSlice) (a : Byte)
      (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
      (h1lo : allLower word1.val)
      (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
      (h2lo : allLower word2.val)
      (hlen : word1.val = [a]) :
      ∃ r : Bool,
        Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
          (r = true ↔ countNe word2.val a ≤ 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word1 word2 : ByteSlice) (a : Byte)
        (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
        (h1lo : allLower word1.val)
        (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
        (h2lo : allLower word2.val)
        (hlen : word1.val = [a]), ∃ r : Bool,
          Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
            (r = true ↔ countNe word2.val a ≤ 1)) := by
    sorry

  /-- The function returns a Boolean r with r = true if and only if x = y, or (len(word1) = 1 and len(word2) = 1), or (len(word1) >= 2 and len(word2) >= 2).
    Preconditions: word1 and word2 are nonempty byte slices with 1 <= len(word1), len(word2) <= 100000, and every byte of both is an ASCII lowercase English letter. Assume there exist bytes x and y such that word1[k] = x for every 0 <= k < len(word1), and word2[k] = y for every 0 <= k < len(word2). -/
  theorem spec_9 (word1 word2 : ByteSlice) (x y : Byte)
      (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
      (h1lo : allLower word1.val)
      (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
      (h2lo : allLower word2.val)
      (h1const : ∀ b ∈ word1.val, b = x)
      (h2const : ∀ b ∈ word2.val, b = y) :
      ∃ r : Bool,
        Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
          (r = true ↔
            x = y ∨
              (word1.val.length = 1 ∧ word2.val.length = 1) ∨
                (2 ≤ word1.val.length ∧ 2 ≤ word2.val.length)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word1 word2 : ByteSlice) (x y : Byte)
        (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
        (h1lo : allLower word1.val)
        (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
        (h2lo : allLower word2.val)
        (h1const : ∀ b ∈ word1.val, b = x)
        (h2const : ∀ b ∈ word2.val, b = y), ∃ r : Bool,
          Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
            (r = true ↔
              x = y ∨
                (word1.val.length = 1 ∧ word2.val.length = 1) ∨
                  (2 ≤ word1.val.length ∧ 2 ≤ word2.val.length))) := by
    sorry

  /-- The function returns a Boolean r; if r = true, then the string among word1 and word2 with the larger distinct count contains a character whose frequency in that string is exactly 1, and the other string (with the smaller distinct count) contains a character whose frequency in that string is at least 2.
    Preconditions: word1 and word2 are nonempty byte slices with 1 <= len(word1), len(word2) <= 100000, and every byte of both is an ASCII lowercase English letter. Let D(s) be the number of distinct bytes in s. Assume |D(word1) - D(word2)| = 2. -/
  theorem spec_10 (word1 word2 : ByteSlice)
      (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
      (h1lo : allLower word1.val)
      (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
      (h2lo : allLower word2.val)
      (hgap : max (distinctCount word1.val) (distinctCount word2.val) -
        min (distinctCount word1.val) (distinctCount word2.val) = 2) :
      ∃ r : Bool,
        Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
          (r = true →
            (distinctCount word2.val < distinctCount word1.val ∧
                hasSingleton word1.val ∧ hasRepeat word2.val) ∨
              (distinctCount word1.val < distinctCount word2.val ∧
                hasSingleton word2.val ∧ hasRepeat word1.val)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word1 word2 : ByteSlice)
        (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
        (h1lo : allLower word1.val)
        (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
        (h2lo : allLower word2.val)
        (hgap : max (distinctCount word1.val) (distinctCount word2.val) -
          min (distinctCount word1.val) (distinctCount word2.val) = 2), ∃ r : Bool,
          Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
            (r = true →
              (distinctCount word2.val < distinctCount word1.val ∧
                  hasSingleton word1.val ∧ hasRepeat word2.val) ∨
                (distinctCount word1.val < distinctCount word2.val ∧
                  hasSingleton word2.val ∧ hasRepeat word1.val))) := by
    sorry

  /-- The function returns a Boolean r with r = true if and only if A has a byte c with freq_A(c) = 1 and B has a byte d with freq_B(d) >= 2.
    Preconditions: word1 and word2 are nonempty byte slices with 1 <= len(word1), len(word2) <= 100000, and every byte of both is an ASCII lowercase English letter. Let D(s) be the number of distinct bytes in s, C(s) the set of bytes occurring in s, and freq_s(c) the frequency of byte c in s. Assume C(word1) and C(word2) are disjoint and |D(word1) - D(word2)| = 1. Let A be the one of word1 and word2 with larger D, and B the other. -/
  theorem spec_11 (word1 word2 : ByteSlice)
      (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
      (h1lo : allLower word1.val)
      (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
      (h2lo : allLower word2.val)
      (hdisj : occDisjoint word1.val word2.val)
      (hgap : max (distinctCount word1.val) (distinctCount word2.val) -
        min (distinctCount word1.val) (distinctCount word2.val) = 1) :
      ∃ r : Bool,
        Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
          (r = true ↔ singletonsAndRepeats word1.val word2.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word1 word2 : ByteSlice)
        (h1ne : 1 ≤ word1.val.length) (h1le : word1.val.length ≤ 100000)
        (h1lo : allLower word1.val)
        (h2ne : 1 ≤ word2.val.length) (h2le : word2.val.length ≤ 100000)
        (h2lo : allLower word2.val)
        (hdisj : occDisjoint word1.val word2.val)
        (hgap : max (distinctCount word1.val) (distinctCount word2.val) -
          min (distinctCount word1.val) (distinctCount word2.val) = 1), ∃ r : Bool,
          Aegis.IsItPossible.is_it_possible word1 word2 = ok r ∧
            (r = true ↔ singletonsAndRepeats word1.val word2.val)) := by
    sorry

  end AegisSpec.IsItPossible
