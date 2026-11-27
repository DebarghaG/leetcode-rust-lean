import Aegis.AmbiguousCoordinates.Code.Funs

/-!
# Specifications of `Aegis.AmbiguousCoordinates.ambiguous_coordinates`

LeetCode problem `ambiguous-coordinates`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AmbiguousCoordinates

def IsDigitByte (b : Std.U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

def DeleteDelims (l : List Std.U8) : List Std.U8 :=
  l.filter (fun b => b.val != 44 && b.val != 46 && b.val != 32)

def DeleteDots (l : List Std.U8) : List Std.U8 :=
  l.filter (fun b => b.val != 46)

def DotCount (l : List Std.U8) : Nat := (l.filter (fun b => b.val == 46)).length

def IntPartOK (p : List Std.U8) : Prop :=
  p ≠ [] ∧ (∀ b, b ∈ p → IsDigitByte b) ∧
    (p = [48#u8] ∨
      ∃ (d : Std.U8) (rest : List Std.U8), p = d :: rest ∧ 49 ≤ d.val ∧ d.val ≤ 57)

def FracPartOK (f : List Std.U8) : Prop :=
  f ≠ [] ∧ (∀ b, b ∈ f → IsDigitByte b) ∧
    ∃ (init : List Std.U8) (last : Std.U8), f = init ++ [last] ∧ last.val ≠ 48

def ValidNumber (l : List Std.U8) : Prop :=
  IntPartOK l ∨
    ∃ (ip fp : List Std.U8), l = ip ++ [46#u8] ++ fp ∧ IntPartOK ip ∧ FracPartOK fp

def InputDigits (s : Slice Std.U8) : List Std.U8 := (s.val.drop 1).dropLast

def InputDigitLen (s : Slice Std.U8) : Nat := s.val.length - 2

def Occurs (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (T : List Std.U8) : Prop :=
  ∃ (j : Nat) (t : alloc.vec.Vec Std.U8), r.val[j]? = some t ∧ t.val = T

def XBytes (t : List Std.U8) : List Std.U8 :=
  (t.drop 1).takeWhile (fun b => b.val != 44)

def YBytes (t : List Std.U8) : List Std.U8 :=
  ((t.dropWhile (fun b => b.val != 32)).drop 1).dropLast

def Admissible (s : Slice Std.U8) (T : List Std.U8) : Prop :=
  ∃ (X Y : List Std.U8),
    T = [40#u8] ++ X ++ [44#u8, 32#u8] ++ Y ++ [41#u8] ∧
      ValidNumber X ∧ ValidNumber Y ∧ DeleteDelims T = s.val

def HasDelimiterShape (t : List Std.U8) : Prop :=
  ∃ (p q : List Std.U8),
    t = [40#u8] ++ p ++ [44#u8, 32#u8] ++ q ++ [41#u8] ∧
      (∀ b, b ∈ p → b.val ≠ 40 ∧ b.val ≠ 41 ∧ b.val ≠ 44 ∧ b.val ≠ 32) ∧
      (∀ b, b ∈ q → b.val ≠ 40 ∧ b.val ≠ 41 ∧ b.val ≠ 44 ∧ b.val ≠ 32)

def IsCoordChar (b : Std.U8) : Prop :=
  IsDigitByte b ∨ b.val = 40 ∨ b.val = 41 ∨ b.val = 44 ∨ b.val = 46 ∨ b.val = 32

/-- Whenever the function returns a result r, for every byte sequence T, T occurs as an element of r (there is j with 0 <= j < len(r) and r[j] = T byte-for-byte) if and only if T is an admissible original coordinate for s. T is admissible exactly when T = '(' + X + ', ' + Y + ')' for some nonempty byte strings X and Y such that: (1) X and Y are valid number representations, where a valid number representation is a nonempty string of ASCII digits with at most one '.', whose integer part is either exactly the one-byte string '0' or begins with a digit '1'..'9', which has at least one digit on each side of any '.', and whose fractional part (if a '.' is present) does not end with '0'; and (2) deleting from T every byte equal to ',' , '.' or ' ' gives exactly s (equivalently, the digit bytes of X followed by the digit bytes of Y are exactly D). Each such T occurs exactly once in r (no duplicates). The order of elements in r is unrestricted.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. Let D be the byte sequence s[1], s[2], ..., s[len(s)-2], and let L = len(s)-2. -/
theorem spec_1 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        (∀ T : List Std.U8, Occurs r T ↔ Admissible s T) ∧
          (∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length),
            r.val[i].val = r.val[j].val → i = j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        (∀ T : List Std.U8, Occurs r T ↔ Admissible s T) ∧
          (∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length),
            r.val[i].val = r.val[j].val → i = j)) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r and does not fail (no panic, overflow, or out-of-bounds failure).
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. -/
theorem spec_2 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), the element t = r[i] has exactly the delimiter shape: its first byte is '(', its last byte is ')', it contains exactly one ',' byte and exactly one ' ' byte, that ' ' byte occurs immediately after that ',' byte, and it contains no other ',' , ' ' , '(' or ')' bytes.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. -/
theorem spec_3 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), HasDelimiterShape (r.val[i]).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), HasDelimiterShape (r.val[i]).val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), if t = r[i], then deleting from t every byte equal to ',' , '.' or ' ' yields the byte sequence s exactly.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. -/
theorem spec_4 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), DeleteDelims (r.val[i]).val = s.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), DeleteDelims (r.val[i]).val = s.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), let t = r[i] and let X be the byte sequence of t strictly between its first byte '(' and its unique ',' byte. Then X is a valid number representation: it is nonempty, consists only of ASCII digits and at most one '.', its integer part is either exactly '0' or begins with a digit '1'..'9', any '.' has at least one digit before and after it, and if a '.' is present its fractional part does not end in '0'.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. -/
theorem spec_5 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), ValidNumber (XBytes (r.val[i]).val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), ValidNumber (XBytes (r.val[i]).val)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), let t = r[i] and let Y be the byte sequence of t strictly between its unique ' ' byte after the comma and its last byte ')'. Then Y is a valid number representation: it is nonempty, consists only of ASCII digits and at most one '.', its integer part is either exactly '0' or begins with a digit '1'..'9', any '.' has at least one digit before and after it, and if a '.' is present its fractional part does not end in '0'.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. -/
theorem spec_6 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), ValidNumber (YBytes (r.val[i]).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), ValidNumber (YBytes (r.val[i]).val)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), let t = r[i], let X be the coordinate before the comma, and let Y be the coordinate after the space; let digits(X) and digits(Y) be obtained by deleting '.' from X and Y. Then there exists an integer k with 1 <= k < L such that digits(X) = D[0..k] (the first k bytes of D) and digits(Y) = D[k..L] (the remaining L-k bytes of D).
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. Let D be the byte sequence s[1], s[2], ..., s[len(s)-2], and let L = len(s)-2. -/
theorem spec_7 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          ∃ k : Nat, 1 ≤ k ∧ k < InputDigitLen s ∧
            DeleteDots (XBytes (r.val[i]).val) = (InputDigits s).take k ∧
            DeleteDots (YBytes (r.val[i]).val) = (InputDigits s).drop k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          ∃ k : Nat, 1 ≤ k ∧ k < InputDigitLen s ∧
            DeleteDots (XBytes (r.val[i]).val) = (InputDigits s).take k ∧
            DeleteDots (YBytes (r.val[i]).val) = (InputDigits s).drop k) := by
  sorry

/-- Whenever the function returns a result r, for every byte sequence T of the form '(' + X + ', ' + Y + ')' where X and Y are valid number representations (nonempty digit strings with at most one '.', integer part exactly '0' or starting with '1'..'9', at least one digit on each side of any '.', and no trailing '0' in a fractional part) and deleting ',' , '.' and ' ' from T gives exactly s, there exists an index j with 0 <= j < len(r) such that r[j] = T.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. -/
theorem spec_8 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ T : List Std.U8, Admissible s T → Occurs r T := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ T : List Std.U8, Admissible s T → Occurs r T) := by
  sorry

/-- Whenever the function returns a result r, for all i and j with 0 <= i < len(r) and 0 <= j < len(r), if r[i] = r[j] byte-for-byte then i = j.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. -/
theorem spec_9 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length),
          r.val[i].val = r.val[j].val → i = j := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length),
          r.val[i].val = r.val[j].val → i = j) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 0 if and only if there is no byte sequence T of the form '(' + X + ', ' + Y + ')' with X and Y valid number representations (nonempty digit strings with at most one '.', integer part exactly '0' or starting with '1'..'9', at least one digit on each side of any '.', and no trailing '0' in a fractional part) such that the digit bytes of X followed by the digit bytes of Y are exactly D.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. Let D be the byte sequence s[1], s[2], ..., s[len(s)-2]. -/
theorem spec_10 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        (r.val.length = 0 ↔
          ¬ ∃ (X Y : List Std.U8),
            ValidNumber X ∧ ValidNumber Y ∧
              DeleteDots X ++ DeleteDots Y = InputDigits s) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        (r.val.length = 0 ↔
          ¬ ∃ (X Y : List Std.U8),
            ValidNumber X ∧ ValidNumber Y ∧
              DeleteDots X ++ DeleteDots Y = InputDigits s)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), let t = r[i] and let d be the number of '.' bytes in t; then len(t) = len(s) + 2 + d. Consequently len(t) is len(s)+2, len(s)+3, or len(s)+4.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. -/
theorem spec_11 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          (r.val[i]).val.length = s.val.length + 2 + DotCount (r.val[i]).val ∧
            ((r.val[i]).val.length = s.val.length + 2 ∨
              (r.val[i]).val.length = s.val.length + 3 ∨
              (r.val[i]).val.length = s.val.length + 4) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          (r.val[i]).val.length = s.val.length + 2 + DotCount (r.val[i]).val ∧
            ((r.val[i]).val.length = s.val.length + 2 ∨
              (r.val[i]).val.length = s.val.length + 3 ∨
              (r.val[i]).val.length = s.val.length + 4)) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= L*(L-1)*(L+1)/6, and in particular len(r) <= 165.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. Let L = len(s)-2. -/
theorem spec_12 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        r.val.length ≤
            InputDigitLen s * (InputDigitLen s - 1) * (InputDigitLen s + 1) / 6 ∧
          r.val.length ≤ 165 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        r.val.length ≤
            InputDigitLen s * (InputDigitLen s - 1) * (InputDigitLen s + 1) / 6 ∧
          r.val.length ≤ 165) := by
  sorry

/-- Whenever the function returns a result r, if len(s) = 4, then len(r) = 1 and the unique element r[0] is the byte string '(' + s[1] + ', ' + s[2] + ')'.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. -/
theorem spec_13 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        s.val.length = 4 →
          r.val.length = 1 ∧
            ∃ (t : alloc.vec.Vec Std.U8) (x y : Std.U8),
              r.val[0]? = some t ∧ s.val[1]? = some x ∧ s.val[2]? = some y ∧
                t.val = [40#u8] ++ [x] ++ [44#u8, 32#u8] ++ [y] ++ [41#u8] := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        s.val.length = 4 →
          r.val.length = 1 ∧
            ∃ (t : alloc.vec.Vec Std.U8) (x y : Std.U8),
              r.val[0]? = some t ∧ s.val[1]? = some x ∧ s.val[2]? = some y ∧
                t.val = [40#u8] ++ [x] ++ [44#u8, 32#u8] ++ [y] ++ [41#u8]) := by
  sorry

/-- Whenever the function returns a result r, every byte of every element of r is one of the following: an ASCII digit '0'..'9', '(', ')', ',', '.', or ' '.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. -/
theorem spec_14 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), ∀ b, b ∈ (r.val[i]).val → IsCoordChar b := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), ∀ b, b ∈ (r.val[i]).val → IsCoordChar b) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), the element t = r[i] contains at most two '.' bytes, and each of its two coordinate substrings (the part before the comma and the part after the space) contains at most one '.' byte.
  Preconditions: len(s) is between 4 and 12 inclusive; s[0] is the byte '('; s[len(s)-1] is the byte ')'; for every i with 1 <= i < len(s)-1, s[i] is an ASCII digit byte '0'..'9'. -/
theorem spec_15 (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          DotCount (r.val[i]).val ≤ 2 ∧
            DotCount (XBytes (r.val[i]).val) ≤ 1 ∧
              DotCount (YBytes (r.val[i]).val) ≤ 1 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : 4 ≤ s.val.length ∧ s.val.length ≤ 12)
    (h_first : s.val[0]? = some (40#u8))
    (h_last : s.val[s.val.length - 1]? = some (41#u8))
    (h_digits : ∀ (i : Nat), 1 ≤ i → i < s.val.length - 1 →
      ∀ b, s.val[i]? = some b → IsDigitByte b), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.AmbiguousCoordinates.ambiguous_coordinates s = ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          DotCount (r.val[i]).val ≤ 2 ∧
            DotCount (XBytes (r.val[i]).val) ≤ 1 ∧
              DotCount (YBytes (r.val[i]).val) ≤ 1) := by
  sorry

end AegisSpec.AmbiguousCoordinates
