import Aegis.MaximumSubsequenceCount.Code.Funs

/-!
# Specifications of `Aegis.MaximumSubsequenceCount.maximum_subsequence_count`

LeetCode problem `maximize-number-of-subsequences-in-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumSubsequenceCount

  namespace AegisSpec.MaximumSubsequenceCount

def bytes (s : Slice U8) : List Nat := s.val.map (fun c => c.val)

def cnt (s : List Nat) (x : Nat) : Int := ((s.filter (fun c => c = x)).length : Int)

def occ : List Nat → Nat → Nat → Int
  | [], _, _ => 0
  | c :: t, x, y => occ t x y + (if c = x then cnt t y else 0)

def insertAt (s : List Nat) (k c : Nat) : List Nat := s.take k ++ c :: s.drop k

def sliceOf (l : List U8) (h : l.length ≤ Usize.max) : Slice U8 :=
  { leng := l.length, list := Aeneas.Data.ListN.ListN.fromList l, bound := h }

@[simp] lemma sliceOf_val (l : List U8) (h : l.length ≤ Usize.max) : (sliceOf l h).val = l := by
  simp [sliceOf, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

lemma slice_val_length (s : Slice U8) : s.val.length = s.leng := by
  simp [Slice.val, Aeneas.Data.ListN.ListN_length]

def revSlice (s : Slice U8) : Slice U8 :=
  sliceOf s.val.reverse (by rw [List.length_reverse, slice_val_length]; exact s.bound)

def swapTwo : List U8 → List U8
  | a :: b :: t => b :: a :: t
  | l => l

lemma swapTwo_length (l : List U8) : (swapTwo l).length = l.length := by
  cases l with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => rfl
    | cons b t => rfl

def swapSlice (s : Slice U8) : Slice U8 :=
  sliceOf (swapTwo s.val) (by rw [swapTwo_length, slice_val_length]; exact s.bound)

@[simp] lemma revSlice_val (s : Slice U8) : (revSlice s).val = s.val.reverse := by
  simp [revSlice]

@[simp] lemma swapSlice_val (s : Slice U8) : (swapSlice s).val = swapTwo s.val := by
  simp [swapSlice]

def pat0 (pattern : Slice U8) : U8 := pattern.val.getD 0 0#u8

def pat1 (pattern : Slice U8) : U8 := pattern.val.getD 1 0#u8

@[simp] lemma pat0_of_cons_cons (pattern : Slice U8) (a b : U8) (t : List U8)
    (h : pattern.val = a :: b :: t) : pat0 pattern = a := by
  simp [pat0, h]

@[simp] lemma pat1_of_cons_cons (pattern : Slice U8) (a b : U8) (t : List U8)
    (h : pattern.val = a :: b :: t) : pat1 pattern = b := by
  simp [pat1, h]

/-- Let n = len(text), a = pattern[0], b = pattern[1]. Let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Let occ(s,x,y) be the number of pairs (i,j) with 0 <= i < j < len(s), s[i] = x, and s[j] = y. The function returns a result r and r = occ(text,a,b) + max(cnt(text,a), cnt(text,b)).
  Preconditions: len(text) >= 1, len(text) <= 100000, len(pattern) = 2, and every byte of text and pattern is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_1 (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : I64, maximum_subsequence_count text pattern = ok r ∧
      r.val = occ (bytes text) (pat0 pattern).val (pat1 pattern).val
        + max (cnt (bytes text) (pat0 pattern).val) (cnt (bytes text) (pat1 pattern).val) := by
    sorry

theorem spec_1_neg :
    ¬ (∀ (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : I64, maximum_subsequence_count text pattern = ok r ∧
      r.val = occ (bytes text) (pat0 pattern).val (pat1 pattern).val
        + max (cnt (bytes text) (pat0 pattern).val) (cnt (bytes text) (pat1 pattern).val)) := by
  sorry

/-- For every text and pattern satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: len(text) >= 1, len(text) <= 100000, len(pattern) = 2, and every byte of text and pattern is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_2 (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : I64, maximum_subsequence_count text pattern = ok r := by
    sorry

theorem spec_2_neg :
    ¬ (∀ (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : I64, maximum_subsequence_count text pattern = ok r) := by
  sorry

/-- Whenever the function returns a result r, let n = len(text); then 0 <= r <= n*(n+1)/2.
  Preconditions: len(text) >= 1, len(text) <= 100000, len(pattern) = 2, and every byte of text and pattern is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_3 (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      0 ≤ r.val ∧
        r.val ≤ (((text.val.length * (text.val.length + 1)) / 2 : Nat) : Int) := by
    sorry

theorem spec_3_neg :
    ¬ (∀ (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      0 ≤ r.val ∧
        r.val ≤ (((text.val.length * (text.val.length + 1)) / 2 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, let a = pattern[0], b = pattern[1], and let occ(s,x,y) be the number of pairs (i,j) with 0 <= i < j < len(s), s[i] = x, and s[j] = y. Then r >= occ(text,a,b).
  Preconditions: len(text) >= 1, len(text) <= 100000, len(pattern) = 2, and every byte of text and pattern is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_4 (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      occ (bytes text) (pat0 pattern).val (pat1 pattern).val ≤ r.val := by
    sorry

theorem spec_4_neg :
    ¬ (∀ (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      occ (bytes text) (pat0 pattern).val (pat1 pattern).val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, let a = pattern[0], b = pattern[1], and let cnt(s,x) be the number of indices i with 0 <= i < len(s) and s[i] = x. Then r >= max(cnt(text,a), cnt(text,b)).
  Preconditions: len(text) >= 1, len(text) <= 100000, len(pattern) = 2, and every byte of text and pattern is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_5 (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      max (cnt (bytes text) (pat0 pattern).val) (cnt (bytes text) (pat1 pattern).val) ≤ r.val := by
    sorry

theorem spec_5_neg :
    ¬ (∀ (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      max (cnt (bytes text) (pat0 pattern).val) (cnt (bytes text) (pat1 pattern).val) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 0 <= k <= len(text) and every c in {pattern[0], pattern[1]}, let T be the length len(text)+1 string defined by T[i] = text[i] for 0 <= i < k, T[k] = c, and T[i] = text[i-1] for k < i <= len(text). Let occ(T,x,y) be the number of pairs (i,j) with 0 <= i < j < len(T), T[i] = x, and T[j] = y. Then occ(T,pattern[0],pattern[1]) <= r.
  Preconditions: len(text) >= 1, len(text) <= 100000, len(pattern) = 2, and every byte of text and pattern is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_6 (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      ∀ (k : Nat) (c : Nat), k ≤ text.val.length →
        (c = (pat0 pattern).val ∨ c = (pat1 pattern).val) →
        occ (insertAt (bytes text) k c) (pat0 pattern).val (pat1 pattern).val ≤ r.val := by
    sorry

theorem spec_6_neg :
    ¬ (∀ (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      ∀ (k : Nat) (c : Nat), k ≤ text.val.length →
        (c = (pat0 pattern).val ∨ c = (pat1 pattern).val) →
        occ (insertAt (bytes text) k c) (pat0 pattern).val (pat1 pattern).val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist an integer k with 0 <= k <= len(text) and a character c in {pattern[0], pattern[1]} such that, if T is the length len(text)+1 string defined by T[i] = text[i] for 0 <= i < k, T[k] = c, and T[i] = text[i-1] for k < i <= len(text), then the number of pairs (i,j) with 0 <= i < j < len(T), T[i] = pattern[0], and T[j] = pattern[1], is exactly r.
  Preconditions: len(text) >= 1, len(text) <= 100000, len(pattern) = 2, and every byte of text and pattern is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_7 (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      ∃ k : Nat, k ≤ text.val.length ∧ ∃ c : Nat,
        (c = (pat0 pattern).val ∨ c = (pat1 pattern).val) ∧
        occ (insertAt (bytes text) k c) (pat0 pattern).val (pat1 pattern).val = r.val := by
    sorry

theorem spec_7_neg :
    ¬ (∀ (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      ∃ k : Nat, k ≤ text.val.length ∧ ∃ c : Nat,
        (c = (pat0 pattern).val ∨ c = (pat1 pattern).val) ∧
        occ (insertAt (bytes text) k c) (pat0 pattern).val (pat1 pattern).val = r.val) := by
  sorry

/-- Let rev(text) be the string of length len(text) with rev(text)[i] = text[len(text)-1-i]. Let swapped(pattern) be the length-2 string with swapped(pattern)[0] = pattern[1] and swapped(pattern)[1] = pattern[0]. Then the value returned by maximum_subsequence_count(text,pattern) equals the value returned by maximum_subsequence_count(rev(text),swapped(pattern)), whenever both calls return results.
  Preconditions: len(text) >= 1, len(text) <= 100000, len(pattern) = 2, and every byte of text and pattern is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_8 (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r r' : I64,
      maximum_subsequence_count text pattern = ok r →
      maximum_subsequence_count (revSlice text) (swapSlice pattern) = ok r' →
      r.val = r'.val := by
    sorry

theorem spec_8_neg :
    ¬ (∀ (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r r' : I64,
      maximum_subsequence_count text pattern = ok r →
      maximum_subsequence_count (revSlice text) (swapSlice pattern) = ok r' →
      r.val = r'.val) := by
  sorry

/-- If pattern[0] != pattern[1], then whenever the function returns a result r, r <= floor(((len(text)+1)*(len(text)+1))/4).
  Preconditions: len(text) >= 1, len(text) <= 100000, len(pattern) = 2, and every byte of text and pattern is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_9 (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpat_ne : pat0 pattern ≠ pat1 pattern) :
    ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      r.val ≤ ((((text.val.length + 1) * (text.val.length + 1)) / 4 : Nat) : Int) := by
    sorry

theorem spec_9_neg :
    ¬ (∀ (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpat_ne : pat0 pattern ≠ pat1 pattern), ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      r.val ≤ ((((text.val.length + 1) * (text.val.length + 1)) / 4 : Nat) : Int)) := by
  sorry

/-- If pattern[0] = pattern[1] = x, then for every integer k with 0 <= k <= len(text), let T be the length len(text)+1 string defined by T[i] = text[i] for 0 <= i < k, T[k] = x, and T[i] = text[i-1] for k < i <= len(text). The number of pairs (i,j) with 0 <= i < j < len(T), T[i] = x, and T[j] = x, is exactly r, where r is the result returned by the function.
  Preconditions: len(text) >= 1, len(text) <= 100000, len(pattern) = 2, and every byte of text and pattern is a lowercase English letter (97 <= byte <= 122). -/
theorem spec_10 (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpat_eq : pat0 pattern = pat1 pattern) :
    ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      ∀ k : Nat, k ≤ text.val.length →
        occ (insertAt (bytes text) k (pat0 pattern).val) (pat0 pattern).val (pat0 pattern).val
          = r.val := by
    sorry

theorem spec_10_neg :
    ¬ (∀ (text pattern : Slice U8)
    (htext_len_ge : 1 ≤ text.val.length) (htext_len_le : text.val.length ≤ 100000)
    (hpattern_len : pattern.val.length = 2)
    (htext_lower : ∀ c ∈ text.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpattern_lower : ∀ c ∈ pattern.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpat_eq : pat0 pattern = pat1 pattern), ∀ r : I64, maximum_subsequence_count text pattern = ok r →
      ∀ k : Nat, k ≤ text.val.length →
        occ (insertAt (bytes text) k (pat0 pattern).val) (pat0 pattern).val (pat0 pattern).val
          = r.val) := by
  sorry

  end AegisSpec.MaximumSubsequenceCount
