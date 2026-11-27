import Aegis.NumberOfSpecialSubstrings.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSpecialSubstrings.number_of_special_substrings`

LeetCode problem `count-substrings-without-repeating-character`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NumberOfSpecialSubstrings

  namespace AegisSpec.NumberOfSpecialSubstrings

  def IsLowerBytes (s : Slice U8) : Prop :=
    ∀ (i : Nat) (h : i < s.val.length), 97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122

  abbrev NodupSeg (l : List U8) (i j : Nat) : Prop := ((l.drop i).take (j + 1 - i)).Nodup

  def specialPairs (l : List U8) : Finset (Nat × Nat) :=
    ((Finset.range l.length).product (Finset.range l.length)).filter
      (fun p => p.1 ≤ p.2 ∧ NodupSeg l p.1 p.2)

  def numSpecial (l : List U8) : Nat := (specialPairs l).card

  def lastOcc (l : List U8) (j : Nat) : Int :=
    match (List.range j).reverse.find? (fun p => l[p]? == l[j]?) with
    | some p => (p : Int)
    | none => -1

  def L (l : List U8) : Nat → Int
    | 0 => 0
    | j + 1 => max (L l j) (lastOcc l (j + 1) + 1)

  /-- Whenever number_of_special_substrings(s) returns a result r, r interpreted as an integer equals the number of pairs of integers (i, j) such that 0 <= i <= j < len(s) and, for all a and b with i <= a < b <= j, s[a] != s[b]. Equivalently, r is the number of non-empty contiguous substrings s[i..j] of s that contain no repeated byte; these are exactly the special substrings counted by the problem.
    Preconditions: s is a byte slice; 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_1 (s : Slice U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
      (hletters : IsLowerBytes s) :
      ∃ r : I64, number_of_special_substrings s = ok r ∧ r.val = (numSpecial s.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
        (hletters : IsLowerBytes s), ∃ r : I64, number_of_special_substrings s = ok r ∧ r.val = (numSpecial s.val : Int)) := by
    sorry

  /-- The call number_of_special_substrings(s) returns a successful result; it does not fail, panic, overflow, or go out of bounds.
    Preconditions: s is a byte slice; 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_2 (s : Slice U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
      (hletters : IsLowerBytes s) :
      ∃ r : I64, number_of_special_substrings s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
        (hletters : IsLowerBytes s), ∃ r : I64, number_of_special_substrings s = ok r) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r, we have r >= len(s). In particular, each of the len(s) one-character substrings s[i..i] is a special substring, so the answer is at least the number of such substrings.
    Preconditions: s is a byte slice; 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_3 (s : Slice U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
      (hletters : IsLowerBytes s) :
      ∃ r : I64, number_of_special_substrings s = ok r ∧
        (s.val.length : Int) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
        (hletters : IsLowerBytes s), ∃ r : I64, number_of_special_substrings s = ok r ∧
          (s.val.length : Int) ≤ r.val) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r, we have r <= len(s)*(len(s)+1)/2, which is the total number of non-empty contiguous substrings of s.
    Preconditions: s is a byte slice; 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_4 (s : Slice U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
      (hletters : IsLowerBytes s) :
      ∃ r : I64, number_of_special_substrings s = ok r ∧
        r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
        (hletters : IsLowerBytes s), ∃ r : I64, number_of_special_substrings s = ok r ∧
          r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r, we have r <= 26*len(s) - 325.
    Preconditions: s is a byte slice; 26 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_5 (s : Slice U8)
      (hlen : 26 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
      (hletters : IsLowerBytes s) :
      ∃ r : I64, number_of_special_substrings s = ok r ∧
        r.val ≤ 26 * (s.val.length : Int) - 325 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8)
        (hlen : 26 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
        (hletters : IsLowerBytes s), ∃ r : I64, number_of_special_substrings s = ok r ∧
          r.val ≤ 26 * (s.val.length : Int) - 325) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r, we have r = 1.
    Preconditions: s is a byte slice; len(s) = 1; s[0] is the ASCII code of a lowercase English letter. -/
  theorem spec_6 (s : Slice U8)
      (hlen : s.val.length = 1)
      (hletters : IsLowerBytes s) :
      ∃ r : I64, number_of_special_substrings s = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8)
        (hlen : s.val.length = 1)
        (hletters : IsLowerBytes s), ∃ r : I64, number_of_special_substrings s = ok r ∧ r.val = 1) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r, if s[0] = s[1] then r = 2, and if s[0] != s[1] then r = 3.
    Preconditions: s is a byte slice; len(s) = 2; s[0] and s[1] are ASCII codes of lowercase English letters. -/
  theorem spec_7 (s : Slice U8)
      (hlen : s.val.length = 2)
      (hletters : IsLowerBytes s) :
      ∃ r : I64, number_of_special_substrings s = ok r ∧
        (s.val[0]? = s.val[1]? → r.val = 2) ∧
        (s.val[0]? ≠ s.val[1]? → r.val = 3) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8)
        (hlen : s.val.length = 2)
        (hletters : IsLowerBytes s), ∃ r : I64, number_of_special_substrings s = ok r ∧
          (s.val[0]? = s.val[1]? → r.val = 2) ∧
          (s.val[0]? ≠ s.val[1]? → r.val = 3)) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r, we have r = len(s).
    Preconditions: s is a byte slice; 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter; for all i and j with 0 <= i < len(s) and 0 <= j < len(s), s[i] = s[j]. -/
  theorem spec_8 (s : Slice U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
      (hletters : IsLowerBytes s)
      (hall : ∀ (i j : Nat), i < s.val.length → j < s.val.length →
        s.val[i]? = s.val[j]?) :
      ∃ r : I64, number_of_special_substrings s = ok r ∧ r.val = (s.val.length : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
        (hletters : IsLowerBytes s)
        (hall : ∀ (i j : Nat), i < s.val.length → j < s.val.length →
          s.val[i]? = s.val[j]?), ∃ r : I64, number_of_special_substrings s = ok r ∧ r.val = (s.val.length : Int)) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r, we have r = len(s)*(len(s)+1)/2.
    Preconditions: s is a byte slice; 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter; for all i and j with 0 <= i < j < len(s), s[i] != s[j]. -/
  theorem spec_9 (s : Slice U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
      (hletters : IsLowerBytes s)
      (hall : ∀ (i j : Nat), i < j → j < s.val.length → s.val[i]? ≠ s.val[j]?) :
      ∃ r : I64, number_of_special_substrings s = ok r ∧
        r.val = ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
        (hletters : IsLowerBytes s)
        (hall : ∀ (i j : Nat), i < j → j < s.val.length → s.val[i]? ≠ s.val[j]?), ∃ r : I64, number_of_special_substrings s = ok r ∧
          r.val = ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r and number_of_special_substrings(t) returns r', we have r = r'.
    Preconditions: s is a byte slice; 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. Let n = len(s), and let t be the byte slice of length n defined by t[i] = s[n-1-i] for every 0 <= i < n. -/
  theorem spec_10 (s t : Slice U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
      (hletters : IsLowerBytes s)
      (ht : t.val = s.val.reverse) :
      ∃ r r' : I64, number_of_special_substrings s = ok r ∧
        number_of_special_substrings t = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t : Slice U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
        (hletters : IsLowerBytes s)
        (ht : t.val = s.val.reverse), ∃ r r' : I64, number_of_special_substrings s = ok r ∧
          number_of_special_substrings t = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r, number_of_special_substrings(x) returns rx, and number_of_special_substrings(y) returns ry, we have r >= rx + ry.
    Preconditions: s is a byte slice; 1 <= len(s) <= 100000; all entries of s are ASCII codes of lowercase English letters; x and y are byte slices with 1 <= len(x), 1 <= len(y), and s = x ++ y. -/
  theorem spec_11 (s x y : Slice U8)
      (hx : 1 ≤ x.val.length) (hy : 1 ≤ y.val.length)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
      (hletters : IsLowerBytes s)
      (hs : s.val = x.val ++ y.val) :
      ∃ r rx ry : I64, number_of_special_substrings s = ok r ∧
        number_of_special_substrings x = ok rx ∧
        number_of_special_substrings y = ok ry ∧ rx.val + ry.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s x y : Slice U8)
        (hx : 1 ≤ x.val.length) (hy : 1 ≤ y.val.length)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
        (hletters : IsLowerBytes s)
        (hs : s.val = x.val ++ y.val), ∃ r rx ry : I64, number_of_special_substrings s = ok r ∧
          number_of_special_substrings x = ok rx ∧
          number_of_special_substrings y = ok ry ∧ rx.val + ry.val ≤ r.val) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r and number_of_special_substrings(t) returns rt, we have rt >= r + 1.
    Preconditions: s is a byte slice; 1 <= len(s) < 100000; all entries of s are ASCII codes of lowercase English letters; c is the ASCII code of a lowercase English letter; t is the byte slice of length len(s)+1 such that t[i] = s[i] for 0 <= i < len(s) and t[len(s)] = c. -/
  theorem spec_12 (s t : Slice U8) (c : U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length < 100000)
      (hletters : IsLowerBytes s)
      (hc : 97 ≤ c.val ∧ c.val ≤ 122)
      (ht : t.val = s.val ++ [c]) :
      ∃ r rt : I64, number_of_special_substrings s = ok r ∧
        number_of_special_substrings t = ok rt ∧ r.val + 1 ≤ rt.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Slice U8) (c : U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length < 100000)
        (hletters : IsLowerBytes s)
        (hc : 97 ≤ c.val ∧ c.val ≤ 122)
        (ht : t.val = s.val ++ [c]), ∃ r rt : I64, number_of_special_substrings s = ok r ∧
          number_of_special_substrings t = ok rt ∧ r.val + 1 ≤ rt.val) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r, define for each j with 0 <= j < len(s): last(j) = max({-1} U { p | 0 <= p < j and s[p] = s[j] }); L(0) = 0; for j > 0, L(j) = max(L(j-1), last(j)+1). Then r = sum_{j=0}^{len(s)-1} (j - L(j) + 1). Equivalently, exactly j - L(j) + 1 special substrings end at j.
    Preconditions: s is a byte slice; 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_13 (s : Slice U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
      (hletters : IsLowerBytes s) :
      ∃ r : I64, number_of_special_substrings s = ok r ∧
        r.val = Finset.sum (Finset.range s.val.length)
          (fun j => (j : Int) - L s.val j + 1) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100000)
        (hletters : IsLowerBytes s), ∃ r : I64, number_of_special_substrings s = ok r ∧
          r.val = Finset.sum (Finset.range s.val.length)
            (fun j => (j : Int) - L s.val j + 1)) := by
    sorry

  /-- Whenever number_of_special_substrings(s) returns r and number_of_special_substrings(t) returns rt, we have rt <= r.
    Preconditions: s and t are byte slices; 1 <= len(t) <= len(s) <= 100000; all entries of s and t are ASCII codes of lowercase English letters; there exists a with 0 <= a and a + len(t) <= len(s) such that for every i with 0 <= i < len(t), t[i] = s[a+i]. -/
  theorem spec_14 (s t : Slice U8)
      (hlen_t : 1 ≤ t.val.length) (hlen : t.val.length ≤ s.val.length)
      (hlen' : s.val.length ≤ 100000)
      (hletters_s : IsLowerBytes s) (hletters_t : IsLowerBytes t)
      (hsub : ∃ a : Nat, a + t.val.length ≤ s.val.length ∧
        ∀ (i : Nat), i < t.val.length → t.val[i]? = s.val[a + i]?) :
      ∃ r rt : I64, number_of_special_substrings s = ok r ∧
        number_of_special_substrings t = ok rt ∧ rt.val ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s t : Slice U8)
        (hlen_t : 1 ≤ t.val.length) (hlen : t.val.length ≤ s.val.length)
        (hlen' : s.val.length ≤ 100000)
        (hletters_s : IsLowerBytes s) (hletters_t : IsLowerBytes t)
        (hsub : ∃ a : Nat, a + t.val.length ≤ s.val.length ∧
          ∀ (i : Nat), i < t.val.length → t.val[i]? = s.val[a + i]?), ∃ r rt : I64, number_of_special_substrings s = ok r ∧
          number_of_special_substrings t = ok rt ∧ rt.val ≤ r.val) := by
    sorry

  end AegisSpec.NumberOfSpecialSubstrings
