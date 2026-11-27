import Aegis.BackspaceCompare.Code.Funs

/-!
# Specifications of `Aegis.BackspaceCompare.backspace_compare`

LeetCode problem `backspace-string-compare`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.BackspaceCompare

  namespace AegisSpec.BackspaceCompare

  def hashByte : Std.U8 := 35#u8

  def isLetter (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def isAdmissibleByte (b : Std.U8) : Prop := isLetter b ∨ b = hashByte

  def admissible (s : Slice Std.U8) : Prop :=
    (∀ b, b ∈ s.val → isAdmissibleByte b) ∧ s.val.length ≤ 200

  def allHash (s : Slice Std.U8) : Prop := ∀ b, b ∈ s.val → b = hashByte

  def noHash (s : Slice Std.U8) : Prop := ∀ b, b ∈ s.val → b ≠ hashByte

  def hashes (k : Nat) : List Std.U8 := List.replicate k hashByte

  def redStep (st : List Std.U8) (c : Std.U8) : List Std.U8 :=
    if c = hashByte then st.dropLast else st ++ [c]

  def redAux : List Std.U8 → List Std.U8 → List Std.U8
    | st, [] => st
    | st, c :: cs => redAux (redStep st c) cs

  def redList (l : List Std.U8) : List Std.U8 := redAux [] l

  theorem redStep_length_le (st : List Std.U8) (c : Std.U8) :
      (redStep st c).length ≤ st.length + 1 := by
    unfold redStep
    split
    · rw [List.length_dropLast]
      omega
    · rw [List.length_append, List.length_singleton]

  theorem redAux_length_le (l : List Std.U8) :
      ∀ st : List Std.U8, (redAux st l).length ≤ st.length + l.length := by
    induction l with
    | nil => intro st; simp [redAux]
    | cons c cs ih =>
      intro st
      have h₁ := ih (redStep st c)
      have h₂ := redStep_length_le st c
      simp only [redAux, List.length_cons]
      omega

  theorem redList_length_le (l : List Std.U8) : (redList l).length ≤ l.length := by
    have h := redAux_length_le l []
    simpa [redList] using h

  def red (s : Slice Std.U8) : Slice Std.U8 :=
    Slice.from (redList s.val) (le_trans (redList_length_le s.val) (Slice.property s))

  def countHash (l : List Std.U8) : Nat := (l.filter fun b => decide (b = hashByte)).length

  def isLetterBool (b : Std.U8) : Bool := decide (97 ≤ b.val) && decide (b.val ≤ 122)

  def countLetter (l : List Std.U8) : Nat := (l.filter isLetterBool).length

  def suffixBalanced (l : List Std.U8) : Prop :=
    ∀ i, i ≤ l.length → countLetter (l.drop i) ≤ countHash (l.drop i)

  /-- Whenever `backspace_compare s t` returns a result `r`, `r = true` if and only if `red(s) = red(t)`, where `red(x)` is the byte sequence obtained by scanning x from left to right with an initially empty stack: for each byte c, append c if c != '#'; if c = '#', delete the last byte of the stack when the stack is nonempty and do nothing when it is empty. Byte-sequence equality means equal length and equal byte at every index. Equivalently, whenever a result is returned, it is `false` exactly when `red(s)` and `red(t)` differ.
    Preconditions: s and t are byte slices such that every byte of s and t is either a lowercase ASCII letter 'a'..'z' or the byte '#'. Their lengths are at most 200, the problem's upper bound; empty slices are allowed, as in the provided examples. -/
  theorem spec_1 (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t) :
      ∀ r : Bool, backspace_compare s t = ok r → (r = true ↔ (red s).val = (red t).val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t), ∀ r : Bool, backspace_compare s t = ok r → (r = true ↔ (red s).val = (red t).val)) := by
    sorry

  /-- For every admissible s and t, `backspace_compare s t` returns a result, either `Bool.true` or `Bool.false`. It does not fail, panic, or go out of bounds, including when s or t is empty, consists only of '#', or has length 200.
    Preconditions: s and t are byte slices such that every byte of s and t is either a lowercase ASCII letter 'a'..'z' or the byte '#'. Their lengths are at most 200; empty slices are allowed. -/
  theorem spec_2 (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t) :
      ∃ r : Bool, backspace_compare s t = ok r ∧ (r = true ∨ r = false) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t), ∃ r : Bool, backspace_compare s t = ok r ∧ (r = true ∨ r = false)) := by
    sorry

  /-- For every admissible s and t, if `backspace_compare s t` returns r and `backspace_compare t s` returns r', then r = r'. That is, the comparison is symmetric in its two arguments.
    Preconditions: s and t are admissible: all bytes are lowercase ASCII letters or '#', and their lengths are at most 200. -/
  theorem spec_3 (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t) :
      ∀ r r' : Bool, backspace_compare s t = ok r → backspace_compare t s = ok r' → r = r' := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t), ∀ r r' : Bool, backspace_compare s t = ok r → backspace_compare t s = ok r' → r = r') := by
    sorry

  /-- Whenever `backspace_compare s t` returns r and `backspace_compare red(s) red(t)` returns r', we have r = r'. Replacing either input text by its fully backspace-reduced text does not change the Boolean answer.
    Preconditions: s and t are admissible; `red(s)` and `red(t)` are the byte slices obtained by backspace reduction as defined in spec_1. These reduced slices contain only lowercase letters. -/
  theorem spec_4 (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t) :
      ∀ r r' : Bool,
        backspace_compare s t = ok r → backspace_compare (red s) (red t) = ok r' → r = r' := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t), ∀ r r' : Bool,
          backspace_compare s t = ok r → backspace_compare (red s) (red t) = ok r' → r = r') := by
    sorry

  /-- For every such k, whenever `backspace_compare s t` returns r and `backspace_compare ('#'^k ++ s) t` returns r', we have r = r'. The analogous equality holds when t is replaced by `'#'^k ++ t`. Leading '#' characters, which backspace an empty text, do not affect the answer.
    Preconditions: s and t are admissible, and k is a nonnegative integer such that the constructed slices still have length at most 200. Let `#'^k ++ s` mean k copies of the byte '#' followed by s. -/
  theorem spec_5 (s t s' t' : Slice Std.U8) (k : Nat)
      (hs : admissible s) (ht : admissible t)
      (hs' : s'.val = hashes k ++ s.val) (ht' : t'.val = hashes k ++ t.val)
      (hs'len : s'.val.length ≤ 200) (ht'len : t'.val.length ≤ 200) :
      (∀ r r' : Bool,
          backspace_compare s t = ok r → backspace_compare s' t = ok r' → r = r') ∧
      (∀ r r' : Bool,
          backspace_compare s t = ok r → backspace_compare s t' = ok r' → r = r') := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s t s' t' : Slice Std.U8) (k : Nat)
        (hs : admissible s) (ht : admissible t)
        (hs' : s'.val = hashes k ++ s.val) (ht' : t'.val = hashes k ++ t.val)
        (hs'len : s'.val.length ≤ 200) (ht'len : t'.val.length ≤ 200), (∀ r r' : Bool,
            backspace_compare s t = ok r → backspace_compare s' t = ok r' → r = r') ∧
        (∀ r r' : Bool,
            backspace_compare s t = ok r → backspace_compare s t' = ok r' → r = r')) := by
    sorry

  /-- For every admissible s, `backspace_compare s s` returns true.
    Preconditions: s is an admissible byte slice with every byte either a lowercase ASCII letter or '#', and len(s) <= 200. -/
  theorem spec_6 (s : Slice Std.U8) (hs : admissible s) :
      ∃ r : Bool, backspace_compare s s = ok r ∧ r = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (hs : admissible s), ∃ r : Bool, backspace_compare s s = ok r ∧ r = true) := by
    sorry

  /-- If `backspace_compare s t` returns true and `backspace_compare t u` returns true, then `backspace_compare s u` returns true.
    Preconditions: s, t, and u are admissible byte slices; every byte is a lowercase ASCII letter or '#', and every length is at most 200. -/
  theorem spec_7 (s t u : Slice Std.U8) (hs : admissible s) (ht : admissible t)
      (hu : admissible u) :
      (∃ r : Bool, backspace_compare s t = ok r ∧ r = true) →
        (∃ r : Bool, backspace_compare t u = ok r ∧ r = true) →
          ∃ r : Bool, backspace_compare s u = ok r ∧ r = true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s t u : Slice Std.U8) (hs : admissible s) (ht : admissible t)
        (hu : admissible u), (∃ r : Bool, backspace_compare s t = ok r ∧ r = true) →
          (∃ r : Bool, backspace_compare t u = ok r ∧ r = true) →
            ∃ r : Bool, backspace_compare s u = ok r ∧ r = true) := by
    sorry

  /-- `backspace_compare s t` returns true.
    Preconditions: s and t are admissible, and every byte of s and every byte of t is '#'. Empty slices qualify vacuously. -/
  theorem spec_8 (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t)
      (hsh : allHash s) (hth : allHash t) :
      ∃ r : Bool, backspace_compare s t = ok r ∧ r = true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t)
        (hsh : allHash s) (hth : allHash t), ∃ r : Bool, backspace_compare s t = ok r ∧ r = true) := by
    sorry

  /-- `backspace_compare s t` returns true if and only if len(s) = len(t) and for every i with 0 <= i < len(s), s[i] = t[i].
    Preconditions: s and t are admissible, and neither s nor t contains the byte '#'. -/
  theorem spec_9 (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t)
      (hsh : noHash s) (hth : noHash t) :
      ∀ r : Bool,
        backspace_compare s t = ok r →
          (r = true ↔
            (s.val.length = t.val.length ∧
              ∀ i, i < s.val.length → s.val[i]? = t.val[i]?)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t)
        (hsh : noHash s) (hth : noHash t), ∀ r : Bool,
          backspace_compare s t = ok r →
            (r = true ↔
              (s.val.length = t.val.length ∧
                ∀ i, i < s.val.length → s.val[i]? = t.val[i]?))) := by
    sorry

  /-- Whenever `backspace_compare s t` returns r, r = true if and only if `red(t) = s` as byte sequences.
    Preconditions: s and t are admissible, and s contains no byte '#'. Let `red(t)` be the backspace reduction of t as defined in spec_1. -/
  theorem spec_10 (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t)
      (hsh : noHash s) :
      ∀ r : Bool, backspace_compare s t = ok r → (r = true ↔ (red t).val = s.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t)
        (hsh : noHash s), ∀ r : Bool, backspace_compare s t = ok r → (r = true ↔ (red t).val = s.val)) := by
    sorry

  /-- `backspace_compare s t` returns true if and only if for every suffix s[i..len(s)-1] with 0 <= i <= len(s), the number of '#' bytes in that suffix is at least the number of lowercase-letter bytes in that suffix. The empty suffix at i = len(s) has both counts zero.
    Preconditions: s and t are admissible, and `red(t)` is the empty byte sequence. For example, t may be the empty slice or a slice consisting only of '#' bytes. -/
  theorem spec_11 (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t)
      (htred : (red t).val = []) :
      ∀ r : Bool, backspace_compare s t = ok r → (r = true ↔ suffixBalanced s.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t)
        (htred : (red t).val = []), ∀ r : Bool, backspace_compare s t = ok r → (r = true ↔ suffixBalanced s.val)) := by
    sorry

  /-- Whenever `backspace_compare s t` returns r, r = true if and only if `red(t)` equals the byte slice obtained from u by deleting its last min(k, len(u)) bytes, i.e. the prefix of u of length max(0, len(u) - k).
    Preconditions: u is a byte slice consisting only of lowercase ASCII letters, k is a nonnegative integer, and s = u followed by k copies of '#' has length at most 200. t is any admissible slice. -/
  theorem spec_12 (u s t : Slice Std.U8) (k : Nat)
      (hu : ∀ b, b ∈ u.val → isLetter b)
      (hs : s.val = u.val ++ hashes k) (hsu : s.val.length ≤ 200)
      (ht : admissible t) :
      ∀ r : Bool,
        backspace_compare s t = ok r → (r = true ↔ (red t).val = u.val.take (u.val.length - k)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (u s t : Slice Std.U8) (k : Nat)
        (hu : ∀ b, b ∈ u.val → isLetter b)
        (hs : s.val = u.val ++ hashes k) (hsu : s.val.length ≤ 200)
        (ht : admissible t), ∀ r : Bool,
          backspace_compare s t = ok r → (r = true ↔ (red t).val = u.val.take (u.val.length - k))) := by
    sorry

  /-- `backspace_compare s t` returns false.
    Preconditions: u is any admissible byte slice, c is a lowercase ASCII letter byte, s = u followed by c, and t = u followed by c and then '#'. Both constructed slices have length at most 200. -/
  theorem spec_13 (u s t : Slice Std.U8) (c : Std.U8)
      (hu : admissible u) (hc : isLetter c)
      (hs : s.val = u.val ++ [c]) (ht : t.val = u.val ++ [c, hashByte])
      (hslen : s.val.length ≤ 200) (htlen : t.val.length ≤ 200) :
      ∃ r : Bool, backspace_compare s t = ok r ∧ r = false := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (u s t : Slice Std.U8) (c : Std.U8)
        (hu : admissible u) (hc : isLetter c)
        (hs : s.val = u.val ++ [c]) (ht : t.val = u.val ++ [c, hashByte])
        (hslen : s.val.length ≤ 200) (htlen : t.val.length ≤ 200), ∃ r : Bool, backspace_compare s t = ok r ∧ r = false) := by
    sorry

  /-- If `backspace_compare s t` returns true, then there exists an integer m such that 0 <= m <= len(s), 0 <= m <= len(t), len(red(s)) = m, and len(red(t)) = m. In particular, the two surviving texts have equal length.
    Preconditions: s and t are admissible byte slices, each of length at most 200. -/
  theorem spec_14 (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t) :
      ∀ r : Bool,
        backspace_compare s t = ok r → r = true →
          ∃ m : Nat,
            m ≤ s.val.length ∧ m ≤ t.val.length ∧
              (red s).val.length = m ∧ (red t).val.length = m := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s t : Slice Std.U8) (hs : admissible s) (ht : admissible t), ∀ r : Bool,
          backspace_compare s t = ok r → r = true →
            ∃ m : Nat,
              m ≤ s.val.length ∧ m ≤ t.val.length ∧
                (red s).val.length = m ∧ (red t).val.length = m) := by
    sorry

  end AegisSpec.BackspaceCompare
