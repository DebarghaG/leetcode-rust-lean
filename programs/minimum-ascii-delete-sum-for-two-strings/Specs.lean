import Aegis.MinimumDeleteSum.Code.Funs

/-!
# Specifications of `Aegis.MinimumDeleteSum.minimum_delete_sum`

LeetCode problem `minimum-ascii-delete-sum-for-two-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumDeleteSum

namespace AegisSpec.MinimumDeleteSum

def ascii (b : U8) : Int := (b.val : Int)

def sumAscii (bs : List U8) : Int := (bs.map ascii).sum

def sumAsciiSlice (s : Slice U8) : Int := sumAscii s.val

def IsSubsequence (t s : List U8) : Prop := t.Sublist s

def IsCommonSubsequence (t : List U8) (s1 s2 : Slice U8) : Prop :=
  IsSubsequence t s1.val ∧ IsSubsequence t s2.val

def deleteCost (s1 s2 : Slice U8) (t : List U8) : Int :=
  sumAsciiSlice s1 + sumAsciiSlice s2 - 2 * sumAscii t

def IsLowerAscii (s : Slice U8) : Prop :=
  ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122

def firstByte (l : List U8) (h : 0 < l.length) : U8 := l.get ⟨0, h⟩

def lastByte (l : List U8) (h : 0 < l.length) : U8 :=
  l.get ⟨l.length - 1, by omega⟩

def sliceOfList (l : List U8) (h : l.length ≤ Usize.max) : Slice U8 :=
  Slice.mk l.length (Aeneas.Data.ListN.ListN.fromList l) h

def tailSlice (s : Slice U8) : Slice U8 :=
  sliceOfList (s.val.drop 1) (by
    have h := Aeneas.Data.ListN.ListN_length s.list
    have hb := s.bound
    simp only [Slice.val, List.length_drop] at h ⊢
    omega)

def initSlice (s : Slice U8) : Slice U8 :=
  sliceOfList (s.val.dropLast) (by
    have h := Aeneas.Data.ListN.ListN_length s.list
    have hb := s.bound
    simp only [Slice.val, List.length_dropLast] at h ⊢
    omega)

/-- The function returns a result r, and r is the minimum, over all byte sequences t that are common subsequences of s1 and s2, of (sum_ascii(s1) + sum_ascii(s2) - 2 * sum_ascii(t)). Here sum_ascii(x) = Sigma_{i=0}^{len(x)-1} ascii(x[i]), ascii(b) is the byte value of b, and t is a common subsequence of s1 and s2 iff t can be obtained by deleting zero or more bytes from each of s1 and s2 while preserving order; the empty t is allowed and is always common. Equivalently, r is the lowest total ASCII value of deleted characters needed to make the two resulting strings equal.
  Preconditions: len(s1) <= 1000, len(s2) <= 1000, and every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122); empty slices are allowed, as in the supplied examples. -/
theorem spec_1
    (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2) :
    ∃ r : I64,
      minimum_delete_sum s1 s2 = ok r ∧
        (∀ t : List U8, IsCommonSubsequence t s1 s2 → r.val ≤ deleteCost s1 s2 t) ∧
        (∃ t : List U8, IsCommonSubsequence t s1 s2 ∧ r.val = deleteCost s1 s2 t) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2), ∃ r : I64,
      minimum_delete_sum s1 s2 = ok r ∧
        (∀ t : List U8, IsCommonSubsequence t s1 s2 → r.val ≤ deleteCost s1 s2 t) ∧
        (∃ t : List U8, IsCommonSubsequence t s1 s2 ∧ r.val = deleteCost s1 s2 t)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access out of bounds on any input satisfying the preconditions.
  Preconditions: len(s1) <= 1000, len(s2) <= 1000, and every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122); empty slices are allowed. -/
theorem spec_2
    (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2) :
    ∃ r : I64, minimum_delete_sum s1 s2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2), ∃ r : I64, minimum_delete_sum s1 s2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= the absolute value of (sum_ascii(s1) - sum_ascii(s2)).
  Preconditions: len(s1) <= 1000, len(s2) <= 1000, and every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122); empty slices are allowed. -/
theorem spec_3
    (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2) :
    ∀ r : I64,
      minimum_delete_sum s1 s2 = ok r →
        |sumAscii s1.val - sumAscii s2.val| ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2), ∀ r : I64,
      minimum_delete_sum s1 s2 = ok r →
        |sumAscii s1.val - sumAscii s2.val| ≤ r.val) := by
  sorry

/-- The function returns a result r, and r = sum_ascii(s2) - sum_ascii(s1).
  Preconditions: len(s1) <= 1000, len(s2) <= 1000, every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122), and s1 is a subsequence of s2: there exist indices 0 <= j_0 < ... < j_{len(s1)-1} < len(s2) such that s2[j_i] = s1[i] for every i with 0 <= i < len(s1). If len(s1) = 0, this index list is empty. -/
theorem spec_4
    (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hsub : IsSubsequence s1.val s2.val) :
    ∃ r : I64,
      minimum_delete_sum s1 s2 = ok r ∧ r.val = sumAscii s2.val - sumAscii s1.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hsub : IsSubsequence s1.val s2.val), ∃ r : I64,
      minimum_delete_sum s1 s2 = ok r ∧ r.val = sumAscii s2.val - sumAscii s1.val) := by
  sorry

/-- The function returns a result r, and r = sum_ascii(s1) - sum_ascii(s2).
  Preconditions: len(s1) <= 1000, len(s2) <= 1000, every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122), and s2 is a subsequence of s1: there exist indices 0 <= i_0 < ... < i_{len(s2)-1} < len(s1) such that s1[i_j] = s2[j] for every j with 0 <= j < len(s2). If len(s2) = 0, this index list is empty. -/
theorem spec_5
    (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hsub : IsSubsequence s2.val s1.val) :
    ∃ r : I64,
      minimum_delete_sum s1 s2 = ok r ∧ r.val = sumAscii s1.val - sumAscii s2.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hsub : IsSubsequence s2.val s1.val), ∃ r : I64,
      minimum_delete_sum s1 s2 = ok r ∧ r.val = sumAscii s1.val - sumAscii s2.val) := by
  sorry

/-- If the function returns r for the ordered pair (s1, s2) and returns r' for the ordered pair (s2, s1), then r = r'.
  Preconditions: len(s1) <= 1000, len(s2) <= 1000, and every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122); empty slices are allowed. -/
theorem spec_6
    (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2) :
    ∀ r r' : I64,
      minimum_delete_sum s1 s2 = ok r →
        minimum_delete_sum s2 s1 = ok r' → r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2), ∀ r r' : I64,
      minimum_delete_sum s1 s2 = ok r →
        minimum_delete_sum s2 s1 = ok r' → r.val = r'.val) := by
  sorry

/-- The function returns a result r, and r = sum_ascii(s1) + sum_ascii(s2).
  Preconditions: len(s1) <= 1000, len(s2) <= 1000, every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122), and for every i with 0 <= i < len(s1) and every j with 0 <= j < len(s2), s1[i] != s2[j]. -/
theorem spec_7
    (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hdisj : ∀ (i : ℕ) (hi : i < s1.val.length) (j : ℕ) (hj : j < s2.val.length),
      s1.val.get ⟨i, hi⟩ ≠ s2.val.get ⟨j, hj⟩) :
    ∀ r : I64,
      minimum_delete_sum s1 s2 = ok r → r.val = sumAscii s1.val + sumAscii s2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hdisj : ∀ (i : ℕ) (hi : i < s1.val.length) (j : ℕ) (hj : j < s2.val.length),
      s1.val.get ⟨i, hi⟩ ≠ s2.val.get ⟨j, hj⟩), ∀ r : I64,
      minimum_delete_sum s1 s2 = ok r → r.val = sumAscii s1.val + sumAscii s2.val) := by
  sorry

/-- If the function returns r for (s1, s2) and returns r' for the slices (s1[1..len(s1)-1], s2[1..len(s2)-1]) obtained by removing the first byte from each string, then r = r'.
  Preconditions: len(s1) > 0, len(s2) > 0, len(s1) <= 1000, len(s2) <= 1000, every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122), and s1[0] = s2[0]. -/
theorem spec_8
    (s1 s2 : Slice U8)
    (h1pos : 0 < s1.val.length) (h2pos : 0 < s2.val.length)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hhead : firstByte s1.val h1pos = firstByte s2.val h2pos) :
    ∀ r r' : I64,
      minimum_delete_sum s1 s2 = ok r →
        minimum_delete_sum (tailSlice s1) (tailSlice s2) = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1pos : 0 < s1.val.length) (h2pos : 0 < s2.val.length)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hhead : firstByte s1.val h1pos = firstByte s2.val h2pos), ∀ r r' : I64,
      minimum_delete_sum s1 s2 = ok r →
        minimum_delete_sum (tailSlice s1) (tailSlice s2) = ok r' → r.val = r'.val) := by
  sorry

/-- If the function returns r for (s1, s2) and returns r' for the slices (s1[0..len(s1)-2], s2[0..len(s2)-2]) obtained by removing the last byte from each string, then r = r'.
  Preconditions: len(s1) > 0, len(s2) > 0, len(s1) <= 1000, len(s2) <= 1000, every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122), and s1[len(s1)-1] = s2[len(s2)-1]. -/
theorem spec_9
    (s1 s2 : Slice U8)
    (h1pos : 0 < s1.val.length) (h2pos : 0 < s2.val.length)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hlast : lastByte s1.val h1pos = lastByte s2.val h2pos) :
    ∀ r r' : I64,
      minimum_delete_sum s1 s2 = ok r →
        minimum_delete_sum (initSlice s1) (initSlice s2) = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1pos : 0 < s1.val.length) (h2pos : 0 < s2.val.length)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hlast : lastByte s1.val h1pos = lastByte s2.val h2pos), ∀ r r' : I64,
      minimum_delete_sum s1 s2 = ok r →
        minimum_delete_sum (initSlice s1) (initSlice s2) = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, r mod 2 = (sum_ascii(s1) + sum_ascii(s2)) mod 2.
  Preconditions: len(s1) <= 1000, len(s2) <= 1000, and every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122); empty slices are allowed. -/
theorem spec_10
    (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2) :
    ∀ r : I64,
      minimum_delete_sum s1 s2 = ok r →
        r.val % 2 = (sumAscii s1.val + sumAscii s2.val) % 2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2), ∀ r : I64,
      minimum_delete_sum s1 s2 = ok r →
        r.val % 2 = (sumAscii s1.val + sumAscii s2.val) % 2) := by
  sorry

/-- Whenever the function returns a result r, for every common subsequence t of s1 and s2, r <= sum_ascii(s1) + sum_ascii(s2) - 2 * sum_ascii(t).
  Preconditions: len(s1) <= 1000, len(s2) <= 1000, and every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122); empty slices are allowed. -/
theorem spec_11
    (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2) :
    ∀ r : I64,
      minimum_delete_sum s1 s2 = ok r →
        ∀ t : List U8, IsCommonSubsequence t s1 s2 → r.val ≤ deleteCost s1 s2 t := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2), ∀ r : I64,
      minimum_delete_sum s1 s2 = ok r →
        ∀ t : List U8, IsCommonSubsequence t s1 s2 → r.val ≤ deleteCost s1 s2 t) := by
  sorry

/-- Whenever the function returns a result r, there exists a common subsequence t of s1 and s2 such that r = sum_ascii(s1) + sum_ascii(s2) - 2 * sum_ascii(t).
  Preconditions: len(s1) <= 1000, len(s2) <= 1000, and every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122); empty slices are allowed. -/
theorem spec_12
    (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2) :
    ∀ r : I64,
      minimum_delete_sum s1 s2 = ok r →
        ∃ t : List U8, IsCommonSubsequence t s1 s2 ∧ r.val = deleteCost s1 s2 t := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2), ∀ r : I64,
      minimum_delete_sum s1 s2 = ok r →
        ∃ t : List U8, IsCommonSubsequence t s1 s2 ∧ r.val = deleteCost s1 s2 t) := by
  sorry

/-- If the function returns r for (s1, s2), returns r1 for (s1 with its first byte removed, s2), and returns r2 for (s1, s2 with its first byte removed), then r = min(ascii(s1[0]) + r1, ascii(s2[0]) + r2). Here ascii(b) is the byte value of b.
  Preconditions: len(s1) > 0, len(s2) > 0, len(s1) <= 1000, len(s2) <= 1000, every byte of s1 and s2 is a lowercase English letter (97 <= byte <= 122), and s1[0] != s2[0]. -/
theorem spec_13
    (s1 s2 : Slice U8)
    (h1pos : 0 < s1.val.length) (h2pos : 0 < s2.val.length)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hne : firstByte s1.val h1pos ≠ firstByte s2.val h2pos) :
    ∀ r r1 r2 : I64,
      minimum_delete_sum s1 s2 = ok r →
        minimum_delete_sum (tailSlice s1) s2 = ok r1 →
          minimum_delete_sum s1 (tailSlice s2) = ok r2 →
            r.val =
              min (ascii (firstByte s1.val h1pos) + r1.val)
                (ascii (firstByte s2.val h2pos) + r2.val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s1 s2 : Slice U8)
    (h1pos : 0 < s1.val.length) (h2pos : 0 < s2.val.length)
    (h1len : s1.val.length ≤ 1000) (h2len : s2.val.length ≤ 1000)
    (h1low : IsLowerAscii s1) (h2low : IsLowerAscii s2)
    (hne : firstByte s1.val h1pos ≠ firstByte s2.val h2pos), ∀ r r1 r2 : I64,
      minimum_delete_sum s1 s2 = ok r →
        minimum_delete_sum (tailSlice s1) s2 = ok r1 →
          minimum_delete_sum s1 (tailSlice s2) = ok r2 →
            r.val =
              min (ascii (firstByte s1.val h1pos) + r1.val)
                (ascii (firstByte s2.val h2pos) + r2.val)) := by
  sorry

end AegisSpec.MinimumDeleteSum
