import Aegis.ValidPalindrome.Code.Funs

/-!
# Specifications of `Aegis.ValidPalindrome.valid_palindrome`

LeetCode problem `valid-palindrome-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ValidPalindrome

def byteAt (l : List Std.U8) (i : Nat) : Nat := ((l[i]?).map (fun b => b.val)).getD 0

def IsPal (l : List Std.U8) : Prop :=
  ∀ j : Nat, j < l.length → byteAt l j = byteAt l (l.length - 1 - j)

def del (l : List Std.U8) (i : Nat) : List Std.U8 := l.take i ++ l.drop (i + 1)

def inner (l : List Std.U8) : List Std.U8 := (l.drop 1).take (l.length - 2)

def PalOrOneDeletion (l : List Std.U8) : Prop :=
  IsPal l ∨ ∃ i : Nat, i < l.length ∧ IsPal (del l i)

def DeletionsToPalindrome (l : List Std.U8) (d : Nat) : Prop :=
  ∃ u : List Std.U8, u <+: l ∧ u.length + d = l.length ∧ IsPal u

def IsMinDeletions (l : List Std.U8) (d0 : Nat) : Prop :=
  DeletionsToPalindrome l d0 ∧ ∀ d : Nat, DeletionsToPalindrome l d → d0 ≤ d

/-- A byte sequence t is called a palindrome iff for every integer j with 0 <= j < len(t), t[j] = t[len(t)-1-j]. For 0 <= i < len(s), let del(s,i) be the byte sequence of length len(s)-1 defined by del(s,i)[j] = s[j] for 0 <= j < i and del(s,i)[j] = s[j+1] for i <= j < len(s)-1. The function returns a result r and r = true iff either s is a palindrome or there exists an integer i with 0 <= i < len(s) such that del(s,i) is a palindrome.
  Preconditions: 1 <= len(s) <= 100000 and for every integer i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty string of lowercase ASCII letters). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122) :
    ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r ∧
      (r = true ↔ PalOrOneDeletion s.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122), ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r ∧
      (r = true ↔ PalOrOneDeletion s.val)) := by
  sorry

/-- The function returns a result r (it does not fail or panic) for every input satisfying the preconditions; r is a Boolean value.
  Preconditions: 1 <= len(s) <= 100000 and for every integer i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122) :
    ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122), ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = false iff s is not a palindrome and for every integer i with 0 <= i < len(s), del(s,i) is not a palindrome, where del(s,i) is s with position i removed.
  Preconditions: 1 <= len(s) <= 100000 and for every integer i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122) :
    ∀ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r →
      (r = false ↔ ¬ IsPal s.val ∧ ∀ i : Nat, i < s.val.length → ¬ IsPal (del s.val i)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122), ∀ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r →
      (r = false ↔ ¬ IsPal s.val ∧ ∀ i : Nat, i < s.val.length → ¬ IsPal (del s.val i))) := by
  sorry

/-- The function returns a result r and r = true.
  Preconditions: 1 <= len(s) <= 100000, for every integer i with 0 <= i < len(s), 97 <= s[i] <= 122, and len(s) = 2. -/
theorem spec_4 (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_two : s.val.length = 2) :
    ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r ∧ r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_two : s.val.length = 2), ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r ∧ r = true) := by
  sorry

/-- The function returns a result r and r = true iff (s[0] = s[1] or s[1] = s[2] or s[0] = s[2]).
  Preconditions: 1 <= len(s) <= 100000, for every integer i with 0 <= i < len(s), 97 <= s[i] <= 122, and len(s) = 3. -/
theorem spec_5 (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_three : s.val.length = 3) :
    ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r ∧
      (r = true ↔ (byteAt s.val 0 = byteAt s.val 1 ∨ byteAt s.val 1 = byteAt s.val 2 ∨
        byteAt s.val 0 = byteAt s.val 2)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_three : s.val.length = 3), ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r ∧
      (r = true ↔ (byteAt s.val 0 = byteAt s.val 1 ∨ byteAt s.val 1 = byteAt s.val 2 ∨
        byteAt s.val 0 = byteAt s.val 2))) := by
  sorry

/-- If valid_palindrome(s) returns r and valid_palindrome(t) returns r', then r = r'.
  Preconditions: 1 <= len(s) <= 100000 and for every integer i with 0 <= i < len(s), 97 <= s[i] <= 122. Also t is a byte slice with len(t) = len(s) and for every j with 0 <= j < len(t), t[j] = s[len(s)-1-j]. -/
theorem spec_6 (s t : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_t : t.val.length = s.val.length)
    (hrev : ∀ j : Nat, j < t.val.length → byteAt t.val j = byteAt s.val (s.val.length - 1 - j)) :
    ∀ (r r' : Bool), Aegis.ValidPalindrome.valid_palindrome s = ok r →
      Aegis.ValidPalindrome.valid_palindrome t = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_t : t.val.length = s.val.length)
    (hrev : ∀ j : Nat, j < t.val.length → byteAt t.val j = byteAt s.val (s.val.length - 1 - j)), ∀ (r r' : Bool), Aegis.ValidPalindrome.valid_palindrome s = ok r →
      Aegis.ValidPalindrome.valid_palindrome t = ok r' → r = r') := by
  sorry

/-- Let d0 be the least integer d with 0 <= d <= len(s) such that some byte sequence u obtained from s by deleting exactly d positions, preserving order, is a palindrome; such a d exists because deleting all characters gives the empty palindrome. The function returns a result r and r = true iff d0 <= 1.
  Preconditions: 1 <= len(s) <= 100000 and for every integer i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_7 (s : Slice Std.U8) (d0 : Nat)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hd0 : IsMinDeletions s.val d0) :
    ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r ∧ (r = true ↔ d0 ≤ 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (d0 : Nat)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hd0 : IsMinDeletions s.val d0), ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r ∧ (r = true ↔ d0 ≤ 1)) := by
  sorry

/-- Whenever the function returns a result r, r = true iff del(s,0) is a palindrome or del(s,len(s)-1) is a palindrome, where del(s,i) is s with position i removed.
  Preconditions: 1 <= len(s) <= 100000, for every integer i with 0 <= i < len(s), 97 <= s[i] <= 122, len(s) >= 2, and s[0] != s[len(s)-1]. -/
theorem spec_8 (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_two : 2 ≤ s.val.length)
    (hends_ne : byteAt s.val 0 ≠ byteAt s.val (s.val.length - 1)) :
    ∀ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r →
      (r = true ↔ IsPal (del s.val 0) ∨ IsPal (del s.val (s.val.length - 1))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_two : 2 ≤ s.val.length)
    (hends_ne : byteAt s.val 0 ≠ byteAt s.val (s.val.length - 1)), ∀ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r →
      (r = true ↔ IsPal (del s.val 0) ∨ IsPal (del s.val (s.val.length - 1)))) := by
  sorry

/-- If valid_palindrome(s) returns r and r = true, then inner is a palindrome or there exists an integer i with 0 <= i < len(inner) such that del(inner,i) is a palindrome.
  Preconditions: 1 <= len(s) <= 100000, for every integer i with 0 <= i < len(s), 97 <= s[i] <= 122, len(s) >= 2, and s[0] = s[len(s)-1]. Define inner to be the byte slice of length len(s)-2 with inner[j] = s[j+1] for 0 <= j < len(s)-2. -/
theorem spec_9 (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_two : 2 ≤ s.val.length)
    (hends_eq : byteAt s.val 0 = byteAt s.val (s.val.length - 1)) :
    ∀ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r → r = true →
      PalOrOneDeletion (inner s.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_two : 2 ≤ s.val.length)
    (hends_eq : byteAt s.val 0 = byteAt s.val (s.val.length - 1)), ∀ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r → r = true →
      PalOrOneDeletion (inner s.val)) := by
  sorry

/-- The function returns a result r and r = true iff inner is a palindrome or there exists an integer i with 0 <= i < len(inner) such that del(inner,i) is a palindrome, where del(t,i) is t with position i removed. This completes S12 by adding the converse: an at-most-one-deletion solution for inner can be lifted to s by keeping the equal endpoints.
  Preconditions: 1 <= len(s) <= 100000, for every integer i with 0 <= i < len(s), 97 <= s[i] <= 122, len(s) >= 2, and s[0] = s[len(s)-1]. Define inner to be the byte slice of length len(s)-2 with inner[j] = s[j+1] for 0 <= j < len(s)-2. -/
theorem spec_10 (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_two : 2 ≤ s.val.length)
    (hends_eq : byteAt s.val 0 = byteAt s.val (s.val.length - 1)) :
    ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r ∧
      (r = true ↔ PalOrOneDeletion (inner s.val)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hletter_lower : ∀ i : Nat, i < s.val.length → 97 ≤ byteAt s.val i)
    (hletter_upper : ∀ i : Nat, i < s.val.length → byteAt s.val i ≤ 122)
    (hlen_two : 2 ≤ s.val.length)
    (hends_eq : byteAt s.val 0 = byteAt s.val (s.val.length - 1)), ∃ r : Bool, Aegis.ValidPalindrome.valid_palindrome s = ok r ∧
      (r = true ↔ PalOrOneDeletion (inner s.val))) := by
  sorry

end AegisSpec.ValidPalindrome
