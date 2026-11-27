import Aegis.UncommonFromSentences.Code.Funs

/-!
# Specifications of `Aegis.UncommonFromSentences.uncommon_from_sentences`

LeetCode problem `uncommon-words-from-two-sentences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.UncommonFromSentences

  open Aegis.UncommonFromSentences (uncommon_from_sentences)

  def IsSpace (b : Std.U8) : Prop := b.val = 32

  def IsLower (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def AllLowerOrSpace (l : List Std.U8) : Prop := ∀ b ∈ l, IsLower b ∨ IsSpace b

  def NoLeadingSpace (l : List Std.U8) : Prop := ∀ b, l.head? = some b → ¬ IsSpace b

  def NoTrailingSpace (l : List Std.U8) : Prop := ∀ b, l.getLast? = some b → ¬ IsSpace b

  def NoDoubleSpace (l : List Std.U8) : Prop :=
    ∀ (p : List Std.U8) (a b : Std.U8) (q : List Std.U8),
      l = p ++ a :: b :: q → ¬ (IsSpace a ∧ IsSpace b)

  def IsSentence (l : List Std.U8) : Prop :=
    1 ≤ l.length ∧ l.length ≤ 200 ∧ AllLowerOrSpace l ∧
      NoLeadingSpace l ∧ NoTrailingSpace l ∧ NoDoubleSpace l

  def splitWordsAux :
      List Std.U8 → List Std.U8 → List (List Std.U8) → List (List Std.U8)
    | [], cur, acc => if cur.isEmpty then acc.reverse else (cur.reverse :: acc).reverse
    | b :: rest, cur, acc =>
      if b.val = 32 then
        if cur.isEmpty then splitWordsAux rest [] acc
        else splitWordsAux rest [] (cur.reverse :: acc)
      else splitWordsAux rest (b :: cur) acc

  def Words (l : List Std.U8) : List (List Std.U8) := splitWordsAux l [] []

  def countOcc (ws : List (List Std.U8)) (w : List Std.U8) : ℕ :=
    ws.countP (fun v => decide (v = w))

  def IsUncommon (s1 s2 : List Std.U8) (w : List Std.U8) : Prop :=
    (countOcc (Words s1) w = 1 ∧ countOcc (Words s2) w = 0) ∨
      (countOcc (Words s1) w = 0 ∧ countOcc (Words s2) w = 1)

  def countInResult (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (w : List Std.U8) : ℕ :=
    r.val.countP (fun v => decide (v.val = w))

  /-- Let words(s) be the list of maximal contiguous non-space blocks of the byte slice s. For a byte sequence w, let count_s(w) be the number of indices j with 0 <= j < len(words(s)) and words(s)[j] = w. Say w is uncommon for (s1,s2) if (count_s1(w) = 1 and count_s2(w) = 0) or (count_s1(w) = 0 and count_s2(w) = 1). Whenever uncommon_from_sentences(s1,s2) returns a result r, for every byte sequence w, the number of indices i with 0 <= i < len(r) and r[i] = w is 1 if w is uncommon, and 0 otherwise. Thus r lists every uncommon word exactly once, in arbitrary order, and no other byte sequence.
    Preconditions: s1 and s2 are byte slices (Slice Std.U8) satisfying the problem constraints: 1 <= len(s1), len(s2) <= 200; every byte of s1 and s2 is an ASCII lowercase letter (byte value 97 through 122) or a space (byte value 32); s1 and s2 have no leading or trailing space; and consecutive words are separated by exactly one space. -/
  theorem spec_1 (s1 s2 : Slice Std.U8) (h1 : IsSentence s1.val) (h2 : IsSentence s2.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (hr : uncommon_from_sentences s1 s2 = ok r) :
      ∀ w : List Std.U8,
        (IsUncommon s1.val s2.val w → countInResult r w = 1) ∧
          (¬ IsUncommon s1.val s2.val w → countInResult r w = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8) (h1 : IsSentence s1.val) (h2 : IsSentence s2.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
        (hr : uncommon_from_sentences s1 s2 = ok r), ∀ w : List Std.U8,
          (IsUncommon s1.val s2.val w → countInResult r w = 1) ∧
            (¬ IsUncommon s1.val s2.val w → countInResult r w = 0)) := by
    sorry

  /-- For every s1 and s2 satisfying the preconditions, uncommon_from_sentences(s1,s2) returns a result r; the call does not fail (no arithmetic overflow, out-of-bounds access, or panic).
    Preconditions: s1 and s2 are byte slices (Slice Std.U8) satisfying the problem constraints: 1 <= len(s1), len(s2) <= 200; every byte of s1 and s2 is an ASCII lowercase letter (byte value 97 through 122) or a space (byte value 32); s1 and s2 have no leading or trailing space; and consecutive words are separated by exactly one space. -/
  theorem spec_2 (s1 s2 : Slice Std.U8) (h1 : IsSentence s1.val) (h2 : IsSentence s2.val) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        uncommon_from_sentences s1 s2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8) (h1 : IsSentence s1.val) (h2 : IsSentence s2.val), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          uncommon_from_sentences s1 s2 = ok r) := by
    sorry

  end AegisSpec.UncommonFromSentences
