import Aegis.ScoreOfString.Code.Funs

/-!
# Specifications of `Aegis.ScoreOfString.score_of_string`

LeetCode problem `score-of-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ScoreOfString

namespace AegisSpec.ScoreOfString

def absDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

def scoreList : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: t => absDiff a b + scoreList (b :: t)

def byteVals (s : Slice U8) : List Nat := s.val.map (fun b => b.val)

def BytesWithin (s : Slice U8) (lo hi : Nat) : Prop :=
  ∀ (i : Nat) (h : i < s.val.length), lo ≤ (s.val.get ⟨i, h⟩).val ∧ (s.val.get ⟨i, h⟩).val ≤ hi

def AdjacentEqual (s : Slice U8) : Prop :=
  ∀ (i : Nat) (h : i < s.val.length - 1),
    (s.val.get ⟨i, by omega⟩).val = (s.val.get ⟨i + 1, by omega⟩).val

def lastByte (s : Slice U8) : Nat := (s.val.getLastD 0#u8).val

def firstByte (s : Slice U8) : Nat := (s.val.headD 0#u8).val

def MapBytes (f : Nat → Int) (s t : Slice U8) : Prop :=
  t.val.length = s.val.length ∧
    ∀ (i : Nat) (h : i < s.val.length),
      ∃ (h' : i < t.val.length), ((t.val.get ⟨i, h'⟩).val : Int) = f ((s.val.get ⟨i, h⟩).val)

def RepeatLast (s t : Slice U8) : Prop :=
  ∃ b : U8, s.val.getLast? = some b ∧ t.val = s.val ++ [b]

/-- The function returns a result r and r = sum_{i=0}^{len(s)-2} |s[i] - s[i+1]|, where s[i] denotes the unsigned byte value at index i and |x| is the mathematical absolute value of the integer x.
  Preconditions: len(s) >= 2, len(s) <= 100, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s consists of lowercase English letters). -/
theorem spec_1 (s : Slice U8)
    (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hlower : BytesWithin s 97 122) :
    ∃ r : I64, score_of_string s = .ok r ∧ r.val = (scoreList (byteVals s) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hlower : BytesWithin s 97 122), ∃ r : I64, score_of_string s = Result.ok r ∧ r.val = (scoreList (byteVals s) : Int)) := by
  sorry

/-- The function returns a result r; it does not fail.
  Preconditions: 1 <= len(s) <= 100 (the bytes need not be lowercase). -/
theorem spec_2 (s : Slice U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100) :
    ∃ r : I64, score_of_string s = .ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100), ∃ r : I64, score_of_string s = Result.ok r) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: len(s) = 1. -/
theorem spec_3 (s : Slice U8)
    (hlen : s.val.length = 1) :
    ∃ r : I64, score_of_string s = .ok r ∧ r.val = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : s.val.length = 1), ∃ r : I64, score_of_string s = Result.ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = |s[0] - s[1]|.
  Preconditions: len(s) = 2 (the two bytes need not be lowercase). -/
theorem spec_4 (s : Slice U8)
    (hlen : s.val.length = 2) :
    ∃ r : I64,
      score_of_string s = .ok r ∧
        r.val = (absDiff ((s.val.get ⟨0, by omega⟩).val)
          ((s.val.get ⟨1, by omega⟩).val) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : s.val.length = 2), ∃ r : I64,
      score_of_string s = Result.ok r ∧
        r.val = (absDiff ((s.val.get ⟨0, by omega⟩).val)
          ((s.val.get ⟨1, by omega⟩).val) : Int)) := by
  sorry

/-- Whenever the function returns a result r, we have r >= 0.
  Preconditions: 1 <= len(s) <= 100. -/
theorem spec_5 (s : Slice U8) (r : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hr : score_of_string s = .ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hr : score_of_string s = Result.ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 25 * (len(s) - 1).
  Preconditions: 2 <= len(s) <= 100 and every byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_6 (s : Slice U8) (r : I64)
    (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hlower : BytesWithin s 97 122)
    (hr : score_of_string s = .ok r) :
    r.val ≤ ((25 * (s.val.length - 1) : Nat) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hlower : BytesWithin s 97 122)
    (hr : score_of_string s = Result.ok r), r.val ≤ ((25 * (s.val.length - 1) : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(s) - 1, s[i] = s[i+1].
  Preconditions: 1 <= len(s) <= 100. -/
theorem spec_7 (s : Slice U8) (r : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hr : score_of_string s = .ok r) :
    (r.val = 0 ↔ AdjacentEqual s) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hr : score_of_string s = Result.ok r), (r.val = 0 ↔ AdjacentEqual s)) := by
  sorry

/-- Let rev(s) be the slice of length len(s) defined by rev(s)[i] = s[len(s)-1-i] for all 0 <= i < len(s). If the function returns r on input s and r' on input rev(s), then r = r'.
  Preconditions: 1 <= len(s) <= 100. -/
theorem spec_8 (s t : Slice U8) (r r' : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (ht : t.val = s.val.reverse)
    (hr : score_of_string s = .ok r) (hr' : score_of_string t = .ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice U8) (r r' : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (ht : t.val = s.val.reverse)
    (hr : score_of_string s = Result.ok r) (hr' : score_of_string t = Result.ok r'), r = r') := by
  sorry

/-- Let z = x ++ y. If the function returns r on z, rx on x, and ry on y, then r = rx + ry + |x[len(x)-1] - y[0]|.
  Preconditions: x and y are byte slices with len(x) >= 1, len(y) >= 1, and len(x) + len(y) <= 100. -/
theorem spec_9 (x y z : Slice U8) (r rx ry : I64)
    (hx : 1 ≤ x.val.length) (hy : 1 ≤ y.val.length)
    (hlen : x.val.length + y.val.length ≤ 100)
    (hz : z.val = x.val ++ y.val)
    (hr : score_of_string z = .ok r)
    (hrx : score_of_string x = .ok rx) (hry : score_of_string y = .ok ry) :
    r.val = rx.val + ry.val + (absDiff (lastByte x) (firstByte y) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (x y z : Slice U8) (r rx ry : I64)
    (hx : 1 ≤ x.val.length) (hy : 1 ≤ y.val.length)
    (hlen : x.val.length + y.val.length ≤ 100)
    (hz : z.val = x.val ++ y.val)
    (hr : score_of_string z = Result.ok r)
    (hrx : score_of_string x = Result.ok rx) (hry : score_of_string y = Result.ok ry), r.val = rx.val + ry.val + (absDiff (lastByte x) (firstByte y) : Int)) := by
  sorry

/-- Let t be the slice of length len(s)+1 with t[i] = s[i] for 0 <= i < len(s) and t[len(s)] = s[len(s)-1]. If the function returns r on s and r' on t, then r = r'.
  Preconditions: 1 <= len(s) <= 99. -/
theorem spec_10 (s t : Slice U8) (r r' : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 99)
    (ht : RepeatLast s t)
    (hr : score_of_string s = .ok r) (hr' : score_of_string t = .ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice U8) (r r' : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 99)
    (ht : RepeatLast s t)
    (hr : score_of_string s = Result.ok r) (hr' : score_of_string t = Result.ok r'), r = r') := by
  sorry

/-- Let t be the slice of length len(s) with t[i] = s[i] + c for all 0 <= i < len(s). If the function returns r on s and r' on t, then r = r'.
  Preconditions: 1 <= len(s) <= 100, c is an integer, and for every i with 0 <= i < len(s), 0 <= s[i] + c <= 255. -/
theorem spec_11 (s t : Slice U8) (c : Int) (r r' : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hc : ∀ (i : Nat) (h : i < s.val.length),
      0 ≤ ((s.val.get ⟨i, h⟩).val : Int) + c ∧ ((s.val.get ⟨i, h⟩).val : Int) + c ≤ 255)
    (ht : MapBytes (fun x => (x : Int) + c) s t)
    (hr : score_of_string s = .ok r) (hr' : score_of_string t = .ok r') :
    r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice U8) (c : Int) (r r' : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hc : ∀ (i : Nat) (h : i < s.val.length),
      0 ≤ ((s.val.get ⟨i, h⟩).val : Int) + c ∧ ((s.val.get ⟨i, h⟩).val : Int) + c ≤ 255)
    (ht : MapBytes (fun x => (x : Int) + c) s t)
    (hr : score_of_string s = Result.ok r) (hr' : score_of_string t = Result.ok r'), r = r') := by
  sorry

/-- Let t be the slice of length len(s) with t[i] = 255 - s[i] for all 0 <= i < len(s). If the function returns r on s and r' on t, then r = r'.
  Preconditions: 1 <= len(s) <= 100. -/
theorem spec_12 (s t : Slice U8) (r r' : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (ht : MapBytes (fun x => (255 : Int) - (x : Int)) s t)
    (hr : score_of_string s = .ok r) (hr' : score_of_string t = .ok r') :
    r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice U8) (r r' : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (ht : MapBytes (fun x => (255 : Int) - (x : Int)) s t)
    (hr : score_of_string s = Result.ok r) (hr' : score_of_string t = Result.ok r'), r = r') := by
  sorry

/-- Let t be the slice of length len(s) with t[i] = c * s[i] for all 0 <= i < len(s). If the function returns r on s and r' on t, then r' = c * r.
  Preconditions: 1 <= len(s) <= 100, c is an integer with c >= 0, and for every i with 0 <= i < len(s), 0 <= c * s[i] <= 255. -/
theorem spec_13 (s t : Slice U8) (c : Int) (r r' : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hc_nonneg : 0 ≤ c)
    (hc : ∀ (i : Nat) (h : i < s.val.length),
      0 ≤ c * ((s.val.get ⟨i, h⟩).val : Int) ∧
        c * ((s.val.get ⟨i, h⟩).val : Int) ≤ 255)
    (ht : MapBytes (fun x => c * (x : Int)) s t)
    (hr : score_of_string s = .ok r) (hr' : score_of_string t = .ok r') :
    r'.val = c * r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s t : Slice U8) (c : Int) (r r' : I64)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
    (hc_nonneg : 0 ≤ c)
    (hc : ∀ (i : Nat) (h : i < s.val.length),
      0 ≤ c * ((s.val.get ⟨i, h⟩).val : Int) ∧
        c * ((s.val.get ⟨i, h⟩).val : Int) ≤ 255)
    (ht : MapBytes (fun x => c * (x : Int)) s t)
    (hr : score_of_string s = Result.ok r) (hr' : score_of_string t = Result.ok r'), r'.val = c * r.val) := by
  sorry

end AegisSpec.ScoreOfString
