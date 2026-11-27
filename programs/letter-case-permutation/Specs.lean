import Aegis.LetterCasePermutation.Code.Funs

/-!
# Specifications of `Aegis.LetterCasePermutation.letter_case_permutation`

LeetCode problem `letter-case-permutation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LetterCasePermutation

open Aegis.LetterCasePermutation

def IsAsciiLower (c : Nat) : Prop := 97 ≤ c ∧ c ≤ 122

def IsAsciiUpper (c : Nat) : Prop := 65 ≤ c ∧ c ≤ 90

def IsAsciiLetter (c : Nat) : Prop := IsAsciiLower c ∨ IsAsciiUpper c

instance : DecidablePred IsAsciiLetter := fun c => by
  unfold IsAsciiLetter IsAsciiLower IsAsciiUpper; infer_instance

def IsAsciiDigit (c : Nat) : Prop := 48 ≤ c ∧ c ≤ 57

def IsInputByte (c : Nat) : Prop := IsAsciiLower c ∨ IsAsciiUpper c ∨ IsAsciiDigit c

def sBytes (s : Slice Std.U8) : List Nat := s.val.map fun c => c.val

def vBytes (v : alloc.vec.Vec Std.U8) : List Nat := v.val.map fun c => c.val

def rBytes (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) : List (List Nat) :=
  r.val.map vBytes

def numLetters (l : List Nat) : Nat := l.countP fun c => decide (IsAsciiLetter c)

def IsCasePermutation (s : Slice Std.U8) (t : List Nat) : Prop :=
  t.length = (sBytes s).length ∧
    ∀ (j : Nat) (hj : j < (sBytes s).length),
      (IsAsciiDigit ((sBytes s).get ⟨j, hj⟩) → t[j]? = some ((sBytes s).get ⟨j, hj⟩)) ∧
      (IsAsciiLetter ((sBytes s).get ⟨j, hj⟩) →
        t[j]? = some ((sBytes s).get ⟨j, hj⟩) ∨
        t[j]? = some (((sBytes s).get ⟨j, hj⟩) ^^^ 32))

def casePermutations : List Nat → List (List Nat)
  | [] => [[]]
  | c :: cs =>
    (casePermutations cs).map (fun t => c :: t) ++
      (if IsAsciiLetter c then (casePermutations cs).map (fun t => (c ^^^ 32) :: t) else [])

/-- Let L be the set of all byte sequences t such that len(t) = len(s) and for every j with 0 <= j < len(s): if s[j] is a digit then t[j] = s[j]; if s[j] is a letter then t[j] = s[j] or t[j] = s[j] XOR 32 (i.e., t[j] is either the lowercase or the uppercase version of s[j]). Whenever the function returns a result r, r is a list of length |L| that contains every element of L exactly once (equivalently, r is a permutation of the elements of L).
  Preconditions: 0 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter (97..122), an ASCII uppercase letter (65..90), or an ASCII digit (48..57). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r) :
    (rBytes r).Perm (casePermutations (sBytes s)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r), (rBytes r).Perm (casePermutations (sBytes s))) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, panic, or overflow) for every s satisfying the preconditions.
  Preconditions: 0 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter (97..122), an ASCII uppercase letter (65..90), or an ASCII digit (48..57). -/
theorem spec_2 (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c) :
    ∃ r, letter_case_permutation s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c), ∃ r, letter_case_permutation s = ok r) := by
  sorry

/-- Let k be the number of indices j with 0 <= j < len(s) such that s[j] is an ASCII letter. Whenever the function returns a result r, len(r) = 2^k.
  Preconditions: 0 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter (97..122), an ASCII uppercase letter (65..90), or an ASCII digit (48..57). -/
theorem spec_3 (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r) :
    (rBytes r).length = 2 ^ (numLetters (sBytes s)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r), (rBytes r).length = 2 ^ (numLetters (sBytes s))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), len(r[i]) = len(s).
  Preconditions: 0 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter (97..122), an ASCII uppercase letter (65..90), or an ASCII digit (48..57). -/
theorem spec_4 (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r) :
    ∀ (i : Nat) (hi : i < r.val.length), (vBytes (r.val.get ⟨i, hi⟩)).length = (sBytes s).length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r), ∀ (i : Nat) (hi : i < r.val.length), (vBytes (r.val.get ⟨i, hi⟩)).length = (sBytes s).length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and every j with 0 <= j < len(s), if s[j] is an ASCII digit and j < len(r[i]), then r[i][j] = s[j].
  Preconditions: 0 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter (97..122), an ASCII uppercase letter (65..90), or an ASCII digit (48..57). -/
theorem spec_5 (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r) :
    ∀ (i : Nat) (hi : i < r.val.length) (j : Nat) (hj : j < (sBytes s).length),
      IsAsciiDigit ((sBytes s).get ⟨j, hj⟩) →
        j < (vBytes (r.val.get ⟨i, hi⟩)).length →
        (vBytes (r.val.get ⟨i, hi⟩))[j]? = some ((sBytes s).get ⟨j, hj⟩) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r), ∀ (i : Nat) (hi : i < r.val.length) (j : Nat) (hj : j < (sBytes s).length),
      IsAsciiDigit ((sBytes s).get ⟨j, hj⟩) →
        j < (vBytes (r.val.get ⟨i, hi⟩)).length →
        (vBytes (r.val.get ⟨i, hi⟩))[j]? = some ((sBytes s).get ⟨j, hj⟩)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and every j with 0 <= j < len(s), if s[j] is an ASCII letter and j < len(r[i]), then r[i][j] = s[j] or r[i][j] = s[j] XOR 32.
  Preconditions: 0 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter (97..122), an ASCII uppercase letter (65..90), or an ASCII digit (48..57). -/
theorem spec_6 (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r) :
    ∀ (i : Nat) (hi : i < r.val.length) (j : Nat) (hj : j < (sBytes s).length),
      IsAsciiLetter ((sBytes s).get ⟨j, hj⟩) →
        j < (vBytes (r.val.get ⟨i, hi⟩)).length →
        (vBytes (r.val.get ⟨i, hi⟩))[j]? = some ((sBytes s).get ⟨j, hj⟩) ∨
        (vBytes (r.val.get ⟨i, hi⟩))[j]? = some (((sBytes s).get ⟨j, hj⟩) ^^^ 32) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r), ∀ (i : Nat) (hi : i < r.val.length) (j : Nat) (hj : j < (sBytes s).length),
      IsAsciiLetter ((sBytes s).get ⟨j, hj⟩) →
        j < (vBytes (r.val.get ⟨i, hi⟩)).length →
        (vBytes (r.val.get ⟨i, hi⟩))[j]? = some ((sBytes s).get ⟨j, hj⟩) ∨
        (vBytes (r.val.get ⟨i, hi⟩))[j]? = some (((sBytes s).get ⟨j, hj⟩) ^^^ 32)) := by
  sorry

/-- Whenever the function returns a result r, for every byte sequence t with len(t) = len(s) and with the property that for every j with 0 <= j < len(s): if s[j] is a digit then t[j] = s[j]; if s[j] is a letter then t[j] = s[j] or t[j] = s[j] XOR 32; there exists an index i with 0 <= i < len(r) such that r[i] = t.
  Preconditions: 0 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter (97..122), an ASCII uppercase letter (65..90), or an ASCII digit (48..57). -/
theorem spec_7 (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r) :
    ∀ t : List Nat, IsCasePermutation s t →
      ∃ (i : Nat) (hi : i < r.val.length), vBytes (r.val.get ⟨i, hi⟩) = t := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r), ∀ t : List Nat, IsCasePermutation s t →
      ∃ (i : Nat) (hi : i < r.val.length), vBytes (r.val.get ⟨i, hi⟩) = t) := by
  sorry

/-- Whenever the function returns a result r, for every i, j with 0 <= i < len(r) and 0 <= j < len(r), if r[i] = r[j] then i = j.
  Preconditions: 0 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter (97..122), an ASCII uppercase letter (65..90), or an ASCII digit (48..57). -/
theorem spec_8 (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r) :
    ∀ (i : Nat) (hi : i < r.val.length) (j : Nat) (hj : j < r.val.length),
      vBytes (r.val.get ⟨i, hi⟩) = vBytes (r.val.get ⟨j, hj⟩) → i = j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : (sBytes s).length ≤ 12)
    (hbytes : ∀ c ∈ sBytes s, IsInputByte c)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : letter_case_permutation s = ok r), ∀ (i : Nat) (hi : i < r.val.length) (j : Nat) (hj : j < r.val.length),
      vBytes (r.val.get ⟨i, hi⟩) = vBytes (r.val.get ⟨j, hj⟩) → i = j) := by
  sorry

end AegisSpec.LetterCasePermutation
