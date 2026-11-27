import Aegis.CompareVersion.Code.Funs

/-!
# Specifications of `Aegis.CompareVersion.compare_version`

LeetCode problem `compare-version-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CompareVersion

  def bytes (s : Slice U8) : List Nat := s.val.map (fun b => b.val)

  def isAsciiDigitB (n : Nat) : Bool := 48 ≤ n && n ≤ 57

  def isAsciiDigit (n : Nat) : Prop := isAsciiDigitB n = true

  def isDot (n : Nat) : Prop := n = 46

  def splitFrom (acc : List Nat) (bs : List Nat) : List (List Nat) :=
    match bs with
    | [] => if acc.isEmpty then [] else [acc.reverse]
    | b :: rest =>
      if isAsciiDigitB b then
        splitFrom (b :: acc) rest
      else if acc.isEmpty then
        splitFrom [] rest
      else
        acc.reverse :: splitFrom [] rest

  def split (s : Slice U8) : List (List Nat) := splitFrom [] (bytes s)

  def numVal (r : List Nat) : Nat := r.foldl (fun acc d => acc * 10 + (d - 48)) 0

  def revs (s : Slice U8) : List Nat := (split s).map numVal

  def rev (s : Slice U8) (i : Nat) : Nat := (revs s).getD i 0

  def WellFormed (s : Slice U8) : Prop :=
    1 ≤ s.val.length ∧
    s.val.length ≤ 500 ∧
    (∀ n ∈ bytes s, isAsciiDigit n ∨ isDot n) ∧
    (∀ (b : U8) (t : List U8), s.val = b :: t → ¬ isDot b.val) ∧
    (∀ (t : List U8) (b : U8), s.val = t ++ [b] → ¬ isDot b.val) ∧
    (∀ (t : List U8) (a b : U8) (u : List U8),
      s.val = t ++ a :: b :: u → ¬ (isDot a.val ∧ isDot b.val))

  def RevsFit (s : Slice U8) : Prop := ∀ r ∈ split s, numVal r ≤ 2 ^ 31 - 1

  def ValidVersion (s : Slice U8) : Prop := WellFormed s ∧ RevsFit s

  def dotZero : List U8 := [46#u8, 48#u8]

  /-- Whenever the function returns a result r, r is the unique integer in {-1, 0, 1} satisfying: if rev(version1,i) = rev(version2,i) for every i >= 0, then r = 0; otherwise, for the smallest i >= 0 with rev(version1,i) != rev(version2,i), r = -1 if rev(version1,i) < rev(version2,i), and r = 1 if rev(version1,i) > rev(version2,i).
    Preconditions: version1 and version2 are byte strings representing valid version numbers: 1 <= len(version1), len(version2) <= 500; every byte is either an ASCII digit (48..57) or the dot byte (46); neither string begins or ends with '.'; and no two consecutive bytes are both '.'. Let split(s) be the list of maximal nonempty digit runs separated by dots, and n(s) = len(split(s)). For a digit string r, val(r) is its base-10 integer value (leading zeros allowed, so val('01') = 1). For i >= 0, define rev(s,i) = val(split(s)[i]) if i < n(s), and rev(s,i) = 0 otherwise. For every revision r in split(version1) or split(version2), val(r) <= 2^31 - 1 (so it fits in a 32-bit signed integer). -/
  theorem spec_1 (version1 version2 : Slice U8)
      (h1 : ValidVersion version1) (h2 : ValidVersion version2)
      (r : I64)
      (hr : Aegis.CompareVersion.compare_version version1 version2 = ok r) :
      (r.val = -1 ∨ r.val = 0 ∨ r.val = 1) ∧
      ((∀ i : Nat, rev version1 i = rev version2 i) → r.val = 0) ∧
      (∀ i : Nat, (∀ j : Nat, j < i → rev version1 j = rev version2 j) →
        rev version1 i ≠ rev version2 i →
        (rev version1 i < rev version2 i → r.val = -1) ∧
        (rev version2 i < rev version1 i → r.val = 1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (version1 version2 : Slice U8)
        (h1 : ValidVersion version1) (h2 : ValidVersion version2)
        (r : I64)
        (hr : Aegis.CompareVersion.compare_version version1 version2 = ok r), (r.val = -1 ∨ r.val = 0 ∨ r.val = 1) ∧
        ((∀ i : Nat, rev version1 i = rev version2 i) → r.val = 0) ∧
        (∀ i : Nat, (∀ j : Nat, j < i → rev version1 j = rev version2 j) →
          rev version1 i ≠ rev version2 i →
          (rev version1 i < rev version2 i → r.val = -1) ∧
          (rev version2 i < rev version1 i → r.val = 1))) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail (no panic, overflow, or out-of-bounds).
    Preconditions: version1 and version2 are byte strings representing valid version numbers: 1 <= len(version1), len(version2) <= 500; every byte is either an ASCII digit (48..57) or the dot byte (46); neither string begins or ends with '.'; and no two consecutive bytes are both '.'. Let split(s) be the list of maximal nonempty digit runs separated by dots, and n(s) = len(split(s)). For a digit string r, val(r) is its base-10 integer value (leading zeros allowed, so val('01') = 1). For i >= 0, define rev(s,i) = val(split(s)[i]) if i < n(s), and rev(s,i) = 0 otherwise. For every revision r in split(version1) or split(version2), val(r) <= 2^31 - 1 (so it fits in a 32-bit signed integer). -/
  theorem spec_2 (version1 version2 : Slice U8)
      (h1 : ValidVersion version1) (h2 : ValidVersion version2) :
      ∃ r : I64, Aegis.CompareVersion.compare_version version1 version2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (version1 version2 : Slice U8)
        (h1 : ValidVersion version1) (h2 : ValidVersion version2), ∃ r : I64, Aegis.CompareVersion.compare_version version1 version2 = ok r) := by
    sorry

  /-- If the function returns r on (version1, version2) and r' on (version1', version2'), then r = r'.
    Preconditions: version1 and version2 are byte strings representing valid version numbers: 1 <= len(version1), len(version2) <= 500; every byte is either an ASCII digit (48..57) or the dot byte (46); neither string begins or ends with '.'; and no two consecutive bytes are both '.'. Let split(s) be the list of maximal nonempty digit runs separated by dots, and n(s) = len(split(s)). For a digit string r, val(r) is its base-10 integer value (leading zeros allowed, so val('01') = 1). For i >= 0, define rev(s,i) = val(split(s)[i]) if i < n(s), and rev(s,i) = 0 otherwise. For every revision r in split(version1) or split(version2), val(r) <= 2^31 - 1 (so it fits in a 32-bit signed integer). Let version1' and version2' be byte strings satisfying the same validity constraints, with n(version1') = n(version1), n(version2') = n(version2), and for every i < n(version1), rev(version1',i) = rev(version1,i); for every i < n(version2), rev(version2',i) = rev(version2,i). -/
  theorem spec_3 (version1 version2 version1' version2' : Slice U8)
      (h1 : ValidVersion version1) (h2 : ValidVersion version2)
      (h1' : ValidVersion version1') (h2' : ValidVersion version2')
      (hn1 : (split version1').length = (split version1).length)
      (hn2 : (split version2').length = (split version2).length)
      (hi1 : ∀ i : Nat, i < (split version1).length → rev version1' i = rev version1 i)
      (hi2 : ∀ i : Nat, i < (split version2).length → rev version2' i = rev version2 i)
      (r r' : I64)
      (hr : Aegis.CompareVersion.compare_version version1 version2 = ok r)
      (hr' : Aegis.CompareVersion.compare_version version1' version2' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (version1 version2 version1' version2' : Slice U8)
        (h1 : ValidVersion version1) (h2 : ValidVersion version2)
        (h1' : ValidVersion version1') (h2' : ValidVersion version2')
        (hn1 : (split version1').length = (split version1).length)
        (hn2 : (split version2').length = (split version2).length)
        (hi1 : ∀ i : Nat, i < (split version1).length → rev version1' i = rev version1 i)
        (hi2 : ∀ i : Nat, i < (split version2).length → rev version2' i = rev version2 i)
        (r r' : I64)
        (hr : Aegis.CompareVersion.compare_version version1 version2 = ok r)
        (hr' : Aegis.CompareVersion.compare_version version1' version2' = ok r'), r.val = r'.val) := by
    sorry

  /-- If the function returns r on (version1, version2) and r' on (version1, version2'), then r = r'.
    Preconditions: version1 and version2 are byte strings representing valid version numbers: 1 <= len(version1), len(version2) <= 500; every byte is either an ASCII digit (48..57) or the dot byte (46); neither string begins or ends with '.'; and no two consecutive bytes are both '.'. Let split(s) be the list of maximal nonempty digit runs separated by dots, and n(s) = len(split(s)). For a digit string r, val(r) is its base-10 integer value (leading zeros allowed, so val('01') = 1). For i >= 0, define rev(s,i) = val(split(s)[i]) if i < n(s), and rev(s,i) = 0 otherwise. For every revision r in split(version1) or split(version2), val(r) <= 2^31 - 1 (so it fits in a 32-bit signed integer). Let k >= 0 be any integer such that len(version2) + 2k <= 500. Let version2' be the byte string obtained by appending k copies of the two-byte sequence [46, 48] ('.' and '0') to version2. -/
  theorem spec_4 (version1 version2 version2' : Slice U8) (k : Nat)
      (h1 : ValidVersion version1) (h2 : ValidVersion version2)
      (hk : version2.val.length + 2 * k ≤ 500)
      (h2' : version2'.val = version2.val ++ (List.replicate k dotZero).flatten)
      (r r' : I64)
      (hr : Aegis.CompareVersion.compare_version version1 version2 = ok r)
      (hr' : Aegis.CompareVersion.compare_version version1 version2' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (version1 version2 version2' : Slice U8) (k : Nat)
        (h1 : ValidVersion version1) (h2 : ValidVersion version2)
        (hk : version2.val.length + 2 * k ≤ 500)
        (h2' : version2'.val = version2.val ++ (List.replicate k dotZero).flatten)
        (r r' : I64)
        (hr : Aegis.CompareVersion.compare_version version1 version2 = ok r)
        (hr' : Aegis.CompareVersion.compare_version version1 version2' = ok r'), r.val = r'.val) := by
    sorry

  /-- If the function returns r on (version1, version2) and r' on (version2, version1), then r' = -r.
    Preconditions: version1 and version2 are byte strings representing valid version numbers: 1 <= len(version1), len(version2) <= 500; every byte is either an ASCII digit (48..57) or the dot byte (46); neither string begins or ends with '.'; and no two consecutive bytes are both '.'. Let split(s) be the list of maximal nonempty digit runs separated by dots, and n(s) = len(split(s)). For a digit string r, val(r) is its base-10 integer value (leading zeros allowed, so val('01') = 1). For i >= 0, define rev(s,i) = val(split(s)[i]) if i < n(s), and rev(s,i) = 0 otherwise. For every revision r in split(version1) or split(version2), val(r) <= 2^31 - 1 (so it fits in a 32-bit signed integer). -/
  theorem spec_5 (version1 version2 : Slice U8)
      (h1 : ValidVersion version1) (h2 : ValidVersion version2)
      (r r' : I64)
      (hr : Aegis.CompareVersion.compare_version version1 version2 = ok r)
      (hr' : Aegis.CompareVersion.compare_version version2 version1 = ok r') :
      r'.val = -r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (version1 version2 : Slice U8)
        (h1 : ValidVersion version1) (h2 : ValidVersion version2)
        (r r' : I64)
        (hr : Aegis.CompareVersion.compare_version version1 version2 = ok r)
        (hr' : Aegis.CompareVersion.compare_version version2 version1 = ok r'), r'.val = -r.val) := by
    sorry

  end AegisSpec.CompareVersion
