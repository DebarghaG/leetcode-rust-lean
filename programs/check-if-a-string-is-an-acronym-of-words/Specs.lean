import Aegis.IsAcronym.Code.Funs

/-!
# Specifications of `Aegis.IsAcronym.is_acronym`

LeetCode problem `check-if-a-string-is-an-acronym-of-words`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsAcronym

def byteAt? (s : Slice Std.U8) (i : Nat) : Option Nat :=
  (s.val[i]?).map (fun b => b.val)

def firstByte? (w : alloc.vec.Vec Std.U8) : Option Nat :=
  (w.val.head?).map (fun b => b.val)

def firstByteAt? (words : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : Option Nat :=
  (words.val[i]?).bind firstByte?

def headByte (w : alloc.vec.Vec Std.U8) (h : 0 < w.val.length) : Std.U8 :=
  w.val.get ⟨0, h⟩

def initialsMatch (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) : Prop :=
  ∀ i, i < words.val.length → byteAt? s i = firstByteAt? words i

def allLower (s : Slice Std.U8) : Prop :=
  ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122

def WordsIn (words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  1 ≤ words.val.length ∧ words.val.length ≤ 100 ∧
    (∀ w, w ∈ words.val → 1 ≤ w.val.length ∧ w.val.length ≤ 10) ∧
    (∀ w, w ∈ words.val → allLower w.slice)

def BytesIn (s : Slice Std.U8) : Prop :=
  1 ≤ s.val.length ∧ s.val.length ≤ 100 ∧ allLower s

def Pre (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) : Prop :=
  WordsIn words ∧ BytesIn s

def firstn (s : Slice α) (j : Nat) : Slice α :=
  Slice.from (s.val.take j) (by
    have h1 : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
    have h2 : (s.val.take j).length ≤ s.val.length := by
      rw [List.length_take]
      omega
    have h3 : s.leng ≤ Usize.max := s.bound
    omega)

def snoc (s : Slice α) (x : α) (h : (s.val ++ [x]).length ≤ Usize.max) : Slice α :=
  Slice.from (s.val ++ [x]) h

/-- The function returns a result r, and r = true if and only if len(s) = len(words) and, for every i with 0 <= i < len(words), s[i] = words[i][0] (the first byte of words[i]).
  Preconditions: 1 <= len(words) <= 100; 1 <= len(s) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; every byte of every words[i] and of s lies in the inclusive range 97..122 (ASCII lowercase letters). -/
theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s) :
    ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (r = true ↔ s.val.length = words.val.length ∧ initialsMatch words s) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s), ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (r = true ↔ s.val.length = words.val.length ∧ initialsMatch words s)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access memory out of bounds.
  Preconditions: Same as spec_1. -/
theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s) :
    ∃ r, Aegis.IsAcronym.is_acronym words s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s), ∃ r, Aegis.IsAcronym.is_acronym words s = ok r) := by
  sorry

/-- The function returns a result r, and if r = true then len(s) = len(words).
  Preconditions: Same as spec_1. -/
theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s) :
    ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (r = true → s.val.length = words.val.length) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s), ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (r = true → s.val.length = words.val.length)) := by
  sorry

/-- The function returns a result r, and if r = true then, for every i with 0 <= i < len(words), s[i] = words[i][0].
  Preconditions: Same as spec_1. -/
theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s) :
    ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (r = true → initialsMatch words s) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s), ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (r = true → initialsMatch words s)) := by
  sorry

/-- The function returns a result r, and if len(s) = len(words) and, for every i with 0 <= i < len(words), s[i] = words[i][0], then r = true.
  Preconditions: Same as spec_1. -/
theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s) :
    ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (s.val.length = words.val.length → initialsMatch words s → r = true) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s), ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (s.val.length = words.val.length → initialsMatch words s → r = true)) := by
  sorry

/-- The function returns a result r, and if len(s) != len(words) then r = false.
  Preconditions: Same as spec_1. -/
theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s) :
    ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (s.val.length ≠ words.val.length → r = false) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s), ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (s.val.length ≠ words.val.length → r = false)) := by
  sorry

/-- For every byte string s satisfying the preconditions, if for every i with 0 <= i < len(words), words[i] and words'[i] are nonempty and words[i][0] = words'[i][0], then is_acronym(words, s) and is_acronym(words', s) return the same Boolean value.
  Preconditions: Same as spec_1, and additionally words' is a slice of Vec U8 also satisfying the preconditions with len(words') = len(words). -/
theorem spec_7 (words words' : Slice (alloc.vec.Vec Std.U8))
    (hw : WordsIn words) (hw' : WordsIn words')
    (hlen : words.val.length = words'.val.length)
    (hagree : ∀ i, i < words.val.length → firstByteAt? words i = firstByteAt? words' i) :
    ∀ s, BytesIn s →
      ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
        Aegis.IsAcronym.is_acronym words' s = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8))
    (hw : WordsIn words) (hw' : WordsIn words')
    (hlen : words.val.length = words'.val.length)
    (hagree : ∀ i, i < words.val.length → firstByteAt? words i = firstByteAt? words' i), ∀ s, BytesIn s →
      ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
        Aegis.IsAcronym.is_acronym words' s = ok r) := by
  sorry

/-- The function returns a result r, and if r = true, then the call is_acronym(words ++ [w], s ++ [w[0]]) returns true, where w[0] is the first byte of w and words ++ [w] extends the word list by one word.
  Preconditions: Same as spec_1, and additionally w is a Vec U8 with 1 <= len(w) <= 10 whose bytes all lie in 97..122, and len(words) + 1 <= 100 and len(s) + 1 <= 100. -/
theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s)
    (w : alloc.vec.Vec Std.U8)
    (hw1 : 1 ≤ w.val.length) (hw2 : w.val.length ≤ 10)
    (hwb : ∀ b, b ∈ w.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwl : words.val.length + 1 ≤ 100) (hsl : s.val.length + 1 ≤ 100)
    (hwu : (words.val ++ [w]).length ≤ Usize.max)
    (hsu : (s.val ++ [headByte w (by omega)]).length ≤ Usize.max) :
    ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (r = true →
        Aegis.IsAcronym.is_acronym (snoc words w hwu)
          (snoc s (headByte w (by omega)) hsu) = ok true) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s)
    (w : alloc.vec.Vec Std.U8)
    (hw1 : 1 ≤ w.val.length) (hw2 : w.val.length ≤ 10)
    (hwb : ∀ b, b ∈ w.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwl : words.val.length + 1 ≤ 100) (hsl : s.val.length + 1 ≤ 100)
    (hwu : (words.val ++ [w]).length ≤ Usize.max)
    (hsu : (s.val ++ [headByte w (by omega)]).length ≤ Usize.max), ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (r = true →
        Aegis.IsAcronym.is_acronym (snoc words w hwu)
          (snoc s (headByte w (by omega)) hsu) = ok true)) := by
  sorry

/-- The function returns a result r, and if r = true, then the call is_acronym(words, s ++ [c]) returns false, where s ++ [c] is the byte string obtained by appending c to s.
  Preconditions: Same as spec_1, and additionally c is a byte with 97 <= c <= 122 and len(s) + 1 <= 100. -/
theorem spec_9 (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s)
    (c : Std.U8) (hc1 : 97 ≤ c.val) (hc2 : c.val ≤ 122)
    (hsl : s.val.length + 1 ≤ 100)
    (hsu : (s.val ++ [c]).length ≤ Usize.max) :
    ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (r = true → Aegis.IsAcronym.is_acronym words (snoc s c hsu) = ok false) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s)
    (c : Std.U8) (hc1 : 97 ≤ c.val) (hc2 : c.val ≤ 122)
    (hsl : s.val.length + 1 ≤ 100)
    (hsu : (s.val ++ [c]).length ≤ Usize.max), ∃ r, Aegis.IsAcronym.is_acronym words s = ok r ∧
      (r = true → Aegis.IsAcronym.is_acronym words (snoc s c hsu) = ok false)) := by
  sorry

/-- If the call is_acronym(words ++ [w], t) returns true, then the call is_acronym(words, t[0:len(words)]) returns true, where t[0:len(words)] denotes the slice consisting of the first len(words) bytes of t (this slice is well-defined because a true result forces len(t) = len(words) + 1).
  Preconditions: words and t satisfy the preconditions, w is a Vec U8 with 1 <= len(w) <= 10 whose bytes all lie in 97..122, and len(words) + 1 <= 100. -/
theorem spec_10 (words : Slice (alloc.vec.Vec Std.U8)) (t : Slice Std.U8)
    (h : Pre words t)
    (w : alloc.vec.Vec Std.U8)
    (hw1 : 1 ≤ w.val.length) (hw2 : w.val.length ≤ 10)
    (hwb : ∀ b, b ∈ w.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwl : words.val.length + 1 ≤ 100)
    (hwu : (words.val ++ [w]).length ≤ Usize.max) :
    Aegis.IsAcronym.is_acronym (snoc words w hwu) t = ok true →
      Aegis.IsAcronym.is_acronym words (firstn t words.val.length) = ok true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (t : Slice Std.U8)
    (h : Pre words t)
    (w : alloc.vec.Vec Std.U8)
    (hw1 : 1 ≤ w.val.length) (hw2 : w.val.length ≤ 10)
    (hwb : ∀ b, b ∈ w.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwl : words.val.length + 1 ≤ 100)
    (hwu : (words.val ++ [w]).length ≤ Usize.max), Aegis.IsAcronym.is_acronym (snoc words w hwu) t = ok true →
      Aegis.IsAcronym.is_acronym words (firstn t words.val.length) = ok true) := by
  sorry

/-- If the call is_acronym(words, s) returns true, then for every j with 1 <= j <= len(words), the call is_acronym(words[0:j], s[0:j]) returns true, where words[0:j] is the slice of the first j words and s[0:j] is the slice of the first j bytes of s.
  Preconditions: Same as spec_1. -/
theorem spec_11 (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s) :
    Aegis.IsAcronym.is_acronym words s = ok true →
      ∀ j, 1 ≤ j → j ≤ words.val.length →
        Aegis.IsAcronym.is_acronym (firstn words j) (firstn s j) = ok true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (h : Pre words s), Aegis.IsAcronym.is_acronym words s = ok true →
      ∀ j, 1 ≤ j → j ≤ words.val.length →
        Aegis.IsAcronym.is_acronym (firstn words j) (firstn s j) = ok true) := by
  sorry

end AegisSpec.IsAcronym
