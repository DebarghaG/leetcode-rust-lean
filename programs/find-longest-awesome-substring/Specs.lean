import Aegis.LongestAwesome.Code.Funs

/-!
# Specifications of `Aegis.LongestAwesome.longest_awesome`

LeetCode problem `find-longest-awesome-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestAwesome

  open Aegis.LongestAwesome

  def byteAt (s : Slice Std.U8) (i : Nat) : Nat :=
    match s.val[i]? with
    | some b => b.val
    | none => 0

  def substr (l : List Std.U8) (i j : Nat) : List Std.U8 := (l.drop i).take (j - i)

  def digitCount (l : List Std.U8) (d : Nat) : Nat :=
    (l.filter fun b => b.val = 48 + d).length

  def oddDigitCount (l : List Std.U8) : Nat :=
    (((List.range 10).map fun d => digitCount l d).filter fun c => c % 2 = 1).length

  def Awesome (l : List Std.U8) : Prop := oddDigitCount l ≤ 1

  def AwesomeSub (s : Slice Std.U8) (l u : Nat) : Prop := Awesome (substr s.val l u)

  def IsMaxAwesomeSub (s : Slice Std.U8) (r : Std.I64) : Prop :=
    (∃ l u : Nat, l < u ∧ u ≤ s.val.length ∧ ((u - l : Nat) : Int) = r.val ∧
        AwesomeSub s l u) ∧
      (∀ (l u : Nat), l < u → u ≤ s.val.length → AwesomeSub s l u →
        ((u - l : Nat) : Int) ≤ r.val)

  def AllBytesEqual (s : Slice Std.U8) : Prop :=
    ∀ (i j : Nat), i < s.val.length → j < s.val.length → byteAt s i = byteAt s j

  def PairwiseDistinctBytes (s : Slice Std.U8) : Prop :=
    ∀ (i j : Nat), i < j → j < s.val.length → byteAt s i ≠ byteAt s j

  def IsPalindrome (s : Slice Std.U8) : Prop :=
    ∀ i : Nat, i < s.val.length → byteAt s i = byteAt s (s.val.length - 1 - i)

  def revSlice (s : Slice Std.U8) : Slice Std.U8 where
    leng := s.val.reverse.length
    list := Aeneas.Data.ListN.ListN.fromList s.val.reverse
    bound := by
      have h : s.val.length ≤ Usize.max := by
        have h1 : s.val.length = s.leng := by
          simp [Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN_length]
        rw [h1]; exact s.bound
      rw [List.length_reverse]; exact h

  theorem revSlice_val (s : Slice Std.U8) : (revSlice s).val = s.val.reverse := by
    simp [revSlice, Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

  theorem revSlice_length (s : Slice Std.U8) : (revSlice s).val.length = s.val.length := by
    rw [revSlice_val, List.length_reverse]

  theorem revSlice_byteAt (s : Slice Std.U8) (i : Nat) (h : i < s.val.length) :
      byteAt (revSlice s) i = byteAt s (s.val.length - 1 - i) := by
    simp only [byteAt, revSlice_val]
    rw [List.getElem?_reverse h]

  /-- Let n = len(s). For 0 <= i < j <= n, call the contiguous substring s[i..j) awesome if, among the ten digit counts #{k | i <= k < j and s[k] = 48+d} for d = 0,1,...,9, at most one count is odd. The function returns a result r (it does not fail) such that: (1) there exist indices i,j with 0 <= i < j <= n, j-i = r, and s[i..j) awesome; and (2) for every i',j' with 0 <= i' < j' <= n and s[i'..j') awesome, j'-i' <= r. Thus r is exactly the maximum length of a non-empty contiguous awesome substring of s.
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), the byte s[i] is an ASCII decimal digit, i.e. 48 <= s[i] <= 57. -/
  theorem spec_1 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∃ r : Std.I64, longest_awesome s = ok r ∧ IsMaxAwesomeSub s r := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∃ r : Std.I64, longest_awesome s = ok r ∧ IsMaxAwesomeSub s r) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns some i64 value r and does not fail: no panic, no out-of-bounds slice access on s, and no i64 arithmetic overflow occurs during the computation.
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_2 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∃ r : Std.I64, longest_awesome s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∃ r : Std.I64, longest_awesome s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have r >= 1. In particular, the longest awesome substring has positive length because every one-character substring is awesome.
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_3 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∀ r : Std.I64, longest_awesome s = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∀ r : Std.I64, longest_awesome s = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, we have r <= len(s). No substring can be longer than the whole string.
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_4 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∀ r : Std.I64, longest_awesome s = ok r → r.val ≤ ((s.val.length : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∀ r : Std.I64, longest_awesome s = ok r → r.val ≤ ((s.val.length : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices l,u with 0 <= l < u <= len(s), u-l = r, and the substring s[l..u) is awesome: among the ten counts #{k | l <= k < u and s[k] = 48+d} for d = 0,1,...,9, at most one count is odd. Hence the returned length is realized by an actual non-empty contiguous substring.
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_5 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∀ r : Std.I64, longest_awesome s = ok r →
        ∃ l u : Nat, l < u ∧ u ≤ s.val.length ∧ ((u - l : Nat) : Int) = r.val ∧
          AwesomeSub s l u := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∀ r : Std.I64, longest_awesome s = ok r →
          ∃ l u : Nat, l < u ∧ u ≤ s.val.length ∧ ((u - l : Nat) : Int) = r.val ∧
            AwesomeSub s l u) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of indices l,u with 0 <= l < u <= len(s) such that s[l..u) is awesome, we have u-l <= r. Here awesome means that among the ten digit counts #{k | l <= k < u and s[k] = 48+d} for d = 0,1,...,9, at most one count is odd.
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_6 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∀ r : Std.I64, longest_awesome s = ok r →
        ∀ (l u : Nat), l < u → u ≤ s.val.length → AwesomeSub s l u →
          ((u - l : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∀ r : Std.I64, longest_awesome s = ok r →
          ∀ (l u : Nat), l < u → u ≤ s.val.length → AwesomeSub s l u →
            ((u - l : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = len(s) if and only if the whole string s is awesome, i.e. among the ten full-string digit counts #{k | 0 <= k < len(s) and s[k] = 48+d} for d = 0,1,...,9, at most one count is odd. Equivalently, r = len(s) exactly when the characters of s can be permuted into a palindrome.
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_7 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∀ r : Std.I64, longest_awesome s = ok r →
        (r.val = ((s.val.length : Nat) : Int) ↔ Awesome s.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∀ r : Std.I64, longest_awesome s = ok r →
          (r.val = ((s.val.length : Nat) : Int) ↔ Awesome s.val)) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) = 1 then r = 1.
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_8 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∀ r : Std.I64, longest_awesome s = ok r → s.val.length = 1 → r.val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∀ r : Std.I64, longest_awesome s = ok r → s.val.length = 1 → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, if all bytes of s are equal (s[0] = s[1] = ... = s[len(s)-1]), then r = len(s).
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_9 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∀ r : Std.I64, longest_awesome s = ok r → AllBytesEqual s →
        r.val = ((s.val.length : Nat) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∀ r : Std.I64, longest_awesome s = ok r → AllBytesEqual s →
          r.val = ((s.val.length : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if s[i] != s[j] for every pair of indices with 0 <= i < j < len(s), then r = 1.
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_10 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∀ r : Std.I64, longest_awesome s = ok r → PairwiseDistinctBytes s → r.val = 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∀ r : Std.I64, longest_awesome s = ok r → PairwiseDistinctBytes s → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, if s is a palindrome (s[i] = s[len(s)-1-i] for every 0 <= i < len(s)), then r = len(s).
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_11 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∀ r : Std.I64, longest_awesome s = ok r → IsPalindrome s →
        r.val = ((s.val.length : Nat) : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∀ r : Std.I64, longest_awesome s = ok r → IsPalindrome s →
          r.val = ((s.val.length : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) = 2 then: r = 2 when s[0] = s[1], and r = 1 when s[0] != s[1].
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_12 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∀ r : Std.I64, longest_awesome s = ok r → s.val.length = 2 →
        (byteAt s 0 = byteAt s 1 → r.val = 2) ∧
          (byteAt s 0 ≠ byteAt s 1 → r.val = 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∀ r : Std.I64, longest_awesome s = ok r → s.val.length = 2 →
          (byteAt s 0 = byteAt s 1 → r.val = 2) ∧
            (byteAt s 0 ≠ byteAt s 1 → r.val = 1)) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) = 3 then: r = 3 if s[0] = s[1] or s[0] = s[2] or s[1] = s[2] (i.e. not all three bytes are distinct), and r = 1 if all three bytes are pairwise distinct.
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_13 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      ∀ r : Std.I64, longest_awesome s = ok r → s.val.length = 3 →
        (byteAt s 0 = byteAt s 1 ∨ byteAt s 0 = byteAt s 2 ∨ byteAt s 1 = byteAt s 2 →
            r.val = 3) ∧
          (byteAt s 0 ≠ byteAt s 1 → byteAt s 0 ≠ byteAt s 2 → byteAt s 1 ≠ byteAt s 2 →
            r.val = 1) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), ∀ r : Std.I64, longest_awesome s = ok r → s.val.length = 3 →
          (byteAt s 0 = byteAt s 1 ∨ byteAt s 0 = byteAt s 2 ∨ byteAt s 1 = byteAt s 2 →
              r.val = 3) ∧
            (byteAt s 0 ≠ byteAt s 1 → byteAt s 0 ≠ byteAt s 2 → byteAt s 1 ≠ byteAt s 2 →
              r.val = 1)) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns the same i64 result on s and on the reversed slice rev(s) defined by rev(s)[i] = s[len(s)-1-i] for 0 <= i < len(s); that is, longest_awesome(s) = longest_awesome(rev(s)).
    Preconditions: 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_14 (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
      (hlen_le : s.val.length ≤ 100000)
      (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57) :
      longest_awesome s = longest_awesome (revSlice s) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_pos : 1 ≤ s.val.length)
        (hlen_le : s.val.length ≤ 100000)
        (hdig : ∀ (i : Nat), i < s.val.length → 48 ≤ byteAt s i ∧ byteAt s i ≤ 57), longest_awesome s = longest_awesome (revSlice s)) := by
    sorry

  end AegisSpec.LongestAwesome
