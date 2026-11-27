import Aegis.MinNumber.Code.Funs

/-!
# Specifications of `Aegis.MinNumber.min_number`

LeetCode problem `form-smallest-number-from-two-digit-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinNumber

open Aegis.MinNumber (min_number)

def Occurs (d : ℤ) (s : Slice I64) : Prop := d ∈ s.val.map (fun x => x.val)

def LenBounds (s : Slice I64) : Prop := 1 ≤ s.val.length ∧ s.val.length ≤ 9

def IsDigitSlice (s : Slice I64) : Prop :=
  ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 9

def Distinct (s : Slice I64) : Prop := (s.val.map (fun x => x.val)).Nodup

def fstVal (s : Slice I64) : ℤ := (s.val.map (fun x => x.val)).headD 0

def sliceMin (s : Slice I64) : ℤ :=
  match s.val.map (fun x => x.val) with
  | [] => 0
  | a :: l => l.foldr min a

def HasDigit (n : ℕ) (d : ℕ) : Prop :=
  ∃ k : ℕ, 0 < n / 10 ^ k ∧ n / 10 ^ k % 10 = d

def HasDigitFrom (n : ℕ) (s : Slice I64) : Prop :=
  ∃ d : ℕ, HasDigit n d ∧ Occurs (d : ℤ) s

def IsCandidate (n : ℕ) (nums1 nums2 : Slice I64) : Prop :=
  HasDigitFrom n nums1 ∧ HasDigitFrom n nums2

def HasCommonDigit (nums1 nums2 : Slice I64) : Prop :=
  ∃ d : ℤ, Occurs d nums1 ∧ Occurs d nums2

/-- The function returns a result r (it does not fail). The value r is the least positive integer n whose decimal representation contains at least one digit equal to some element of nums1 and at least one digit equal to some element of nums2; the same digit may witness both conditions if it occurs in both arrays. Equivalently: if nums1 and nums2 have a common digit, then r is the smallest digit occurring in both arrays; if they have no common digit, then r = 10*m + s, where m = min(min(nums1), min(nums2)), and s = min(nums2) when m occurs in nums1, while s = min(nums1) when m occurs in nums2.
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct. -/
theorem spec_1 (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2) :
    ∃ r : I64, min_number nums1 nums2 = ok r ∧ 1 ≤ r.val ∧
      IsCandidate r.val.toNat nums1 nums2 ∧
      ∀ n : ℕ, 1 ≤ n → IsCandidate n nums1 nums2 → r.val ≤ (n : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2), ∃ r : I64, min_number nums1 nums2 = ok r ∧ 1 ≤ r.val ∧
      IsCandidate r.val.toNat nums1 nums2 ∧
      ∀ n : ℕ, 1 ≤ n → IsCandidate n nums1 nums2 → r.val ≤ (n : ℤ)) := by
  sorry

/-- The function returns a result r; it does not fail (no arithmetic overflow, out-of-bounds access, or panic occurs).
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct. -/
theorem spec_2 (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2) :
    ∃ r : I64, min_number nums1 nums2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2), ∃ r : I64, min_number nums1 nums2 = ok r) := by
  sorry

/-- The function returns a result r, and 1 <= r <= 99.
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct. -/
theorem spec_3 (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2) :
    ∃ r : I64, min_number nums1 nums2 = ok r ∧ 1 ≤ r.val ∧ r.val ≤ 99 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2), ∃ r : I64, min_number nums1 nums2 = ok r ∧ 1 ≤ r.val ∧ r.val ≤ 99) := by
  sorry

/-- The function returns a result r. The integer r has exactly one decimal digit if and only if nums1 and nums2 have at least one common digit; otherwise r has exactly two decimal digits. Equivalently, r < 10 holds exactly when some digit occurs in both nums1 and nums2, and r >= 10 holds exactly when no digit occurs in both arrays.
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct. -/
theorem spec_4 (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2) :
    ∃ r : I64, min_number nums1 nums2 = ok r ∧
      (r.val < 10 ↔ HasCommonDigit nums1 nums2) ∧
      (10 ≤ r.val ↔ ¬ HasCommonDigit nums1 nums2) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2), ∃ r : I64, min_number nums1 nums2 = ok r ∧
      (r.val < 10 ↔ HasCommonDigit nums1 nums2) ∧
      (10 ≤ r.val ↔ ¬ HasCommonDigit nums1 nums2)) := by
  sorry

/-- If there exists a digit d that occurs in both nums1 and nums2, then the function returns a result r such that r occurs in nums1, r occurs in nums2, and for every digit d, if d occurs in both nums1 and nums2 then r <= d.
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct. -/
theorem spec_5 (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2)
    (hc : HasCommonDigit nums1 nums2) :
    ∃ r : I64, min_number nums1 nums2 = ok r ∧ Occurs r.val nums1 ∧ Occurs r.val nums2 ∧
      ∀ d : ℤ, Occurs d nums1 → Occurs d nums2 → r.val ≤ d := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2)
    (hc : HasCommonDigit nums1 nums2), ∃ r : I64, min_number nums1 nums2 = ok r ∧ Occurs r.val nums1 ∧ Occurs r.val nums2 ∧
      ∀ d : ℤ, Occurs d nums1 → Occurs d nums2 → r.val ≤ d) := by
  sorry

/-- If no digit occurs in both nums1 and nums2, then the function returns a result r equal to the minimum of the set { 10*min(a,b) + max(a,b) | a occurs in nums1 and b occurs in nums2 }.
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct. -/
theorem spec_6 (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2)
    (hc : ¬ HasCommonDigit nums1 nums2) :
    ∃ r : I64, min_number nums1 nums2 = ok r ∧
      (∃ a b : ℤ, Occurs a nums1 ∧ Occurs b nums2 ∧ r.val = 10 * min a b + max a b) ∧
      (∀ a b : ℤ, Occurs a nums1 → Occurs b nums2 → r.val ≤ 10 * min a b + max a b) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2)
    (hc : ¬ HasCommonDigit nums1 nums2), ∃ r : I64, min_number nums1 nums2 = ok r ∧
      (∃ a b : ℤ, Occurs a nums1 ∧ Occurs b nums2 ∧ r.val = 10 * min a b + max a b) ∧
      (∀ a b : ℤ, Occurs a nums1 → Occurs b nums2 → r.val ≤ 10 * min a b + max a b)) := by
  sorry

/-- Suppose no digit occurs in both nums1 and nums2, and let m = min(min(nums1), min(nums2)). If m occurs in nums1, then the function returns r = 10*m + min(nums2); if m occurs in nums2, then the function returns r = 10*m + min(nums1).
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct. -/
theorem spec_7 (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2)
    (hc : ¬ HasCommonDigit nums1 nums2) :
    let m : ℤ := min (sliceMin nums1) (sliceMin nums2)
    (Occurs m nums1 → ∃ r : I64, min_number nums1 nums2 = ok r ∧ r.val = 10 * m + sliceMin nums2) ∧
    (Occurs m nums2 → ∃ r : I64, min_number nums1 nums2 = ok r ∧ r.val = 10 * m + sliceMin nums1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2)
    (hc : ¬ HasCommonDigit nums1 nums2), let m : ℤ := min (sliceMin nums1) (sliceMin nums2)
    (Occurs m nums1 → ∃ r : I64, min_number nums1 nums2 = ok r ∧ r.val = 10 * m + sliceMin nums2) ∧
    (Occurs m nums2 → ∃ r : I64, min_number nums1 nums2 = ok r ∧ r.val = 10 * m + sliceMin nums1)) := by
  sorry

/-- Whenever the function returns a result r, the decimal representation of r contains at least one digit d such that d occurs in nums1 and at least one digit e such that e occurs in nums2; the witnesses d and e may be equal.
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct. -/
theorem spec_8 (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2) :
    ∀ r : I64, min_number nums1 nums2 = ok r →
      HasDigitFrom r.val.toNat nums1 ∧ HasDigitFrom r.val.toNat nums2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2), ∀ r : I64, min_number nums1 nums2 = ok r →
      HasDigitFrom r.val.toNat nums1 ∧ HasDigitFrom r.val.toNat nums2) := by
  sorry

/-- If no digit occurs in both nums1 and nums2, then whenever the function returns a result r, there exist a digit a occurring in nums1 and a digit b occurring in nums2 such that either r = 10*a + b or r = 10*b + a.
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct. -/
theorem spec_9 (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2)
    (hc : ¬ HasCommonDigit nums1 nums2) :
    ∀ r : I64, min_number nums1 nums2 = ok r →
      ∃ a b : ℕ, Occurs (a : ℤ) nums1 ∧ Occurs (b : ℤ) nums2 ∧
        (r.val = 10 * (a : ℤ) + (b : ℤ) ∨ r.val = 10 * (b : ℤ) + (a : ℤ)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2)
    (hc : ¬ HasCommonDigit nums1 nums2), ∀ r : I64, min_number nums1 nums2 = ok r →
      ∃ a b : ℕ, Occurs (a : ℤ) nums1 ∧ Occurs (b : ℤ) nums2 ∧
        (r.val = 10 * (a : ℤ) + (b : ℤ) ∨ r.val = 10 * (b : ℤ) + (a : ℤ))) := by
  sorry

/-- Whenever the function returns a result r, for every digit a occurring in nums1 and every digit b occurring in nums2, both r <= 10*a + b and r <= 10*b + a hold.
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct. -/
theorem spec_10 (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2) :
    ∀ r : I64, min_number nums1 nums2 = ok r →
      ∀ a b : ℤ, Occurs a nums1 → Occurs b nums2 → r.val ≤ 10 * a + b ∧ r.val ≤ 10 * b + a := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2), ∀ r : I64, min_number nums1 nums2 = ok r →
      ∀ a b : ℤ, Occurs a nums1 → Occurs b nums2 → r.val ≤ 10 * a + b ∧ r.val ≤ 10 * b + a) := by
  sorry

/-- Let r be the result returned by min_number(nums1, nums2), and let r' be the result returned by min_number(nums2, nums1). Then r = r'.
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct. -/
theorem spec_11 (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2) :
    ∀ r r' : I64, min_number nums1 nums2 = ok r → min_number nums2 nums1 = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2), ∀ r r' : I64, min_number nums1 nums2 = ok r → min_number nums2 nums1 = ok r' → r.val = r'.val) := by
  sorry

/-- Let r be the result returned by min_number(nums1, nums2), and let r' be the result returned by min_number(nums1', nums2). Then r' <= r.
  Preconditions: len(nums1) and len(nums2) are between 1 and 9 inclusive; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 9; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 9; all elements of nums1 are pairwise distinct; all elements of nums2 are pairwise distinct; len(nums1) < 9; e is a digit with 1 <= e <= 9 that does not occur in nums1; nums1' is any slice of length len(nums1)+1 whose first len(nums1) entries are exactly nums1 and whose last entry is e. -/
theorem spec_12 (nums1 nums2 nums1' : Slice I64) (e : I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2)
    (h7 : nums1.val.length < 9)
    (h8 : 1 ≤ e.val) (h9 : e.val ≤ 9) (h10 : ¬ Occurs e.val nums1)
    (h11 : nums1'.val = nums1.val ++ [e]) :
    ∀ r r' : I64, min_number nums1 nums2 = ok r → min_number nums1' nums2 = ok r' → r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 nums1' : Slice I64) (e : I64)
    (h1 : LenBounds nums1) (h2 : LenBounds nums2)
    (h3 : IsDigitSlice nums1) (h4 : IsDigitSlice nums2)
    (h5 : Distinct nums1) (h6 : Distinct nums2)
    (h7 : nums1.val.length < 9)
    (h8 : 1 ≤ e.val) (h9 : e.val ≤ 9) (h10 : ¬ Occurs e.val nums1)
    (h11 : nums1'.val = nums1.val ++ [e]), ∀ r r' : I64, min_number nums1 nums2 = ok r → min_number nums1' nums2 = ok r' → r'.val ≤ r.val) := by
  sorry

/-- If nums1[0] = nums2[0] = d, then the function returns r = d. If nums1[0] != nums2[0], then the function returns r = 10*min(nums1[0], nums2[0]) + max(nums1[0], nums2[0]).
  Preconditions: len(nums1) = 1, len(nums2) = 1, 1 <= nums1[0] <= 9, and 1 <= nums2[0] <= 9. -/
theorem spec_13 (nums1 nums2 : Slice I64)
    (h1 : nums1.val.length = 1) (h2 : nums2.val.length = 1)
    (hd1 : 1 ≤ fstVal nums1) (hd1' : fstVal nums1 ≤ 9)
    (hd2 : 1 ≤ fstVal nums2) (hd2' : fstVal nums2 ≤ 9) :
    (fstVal nums1 = fstVal nums2 →
      ∃ r : I64, min_number nums1 nums2 = ok r ∧ r.val = fstVal nums1) ∧
    (fstVal nums1 ≠ fstVal nums2 →
      ∃ r : I64, min_number nums1 nums2 = ok r ∧
        r.val = 10 * min (fstVal nums1) (fstVal nums2) + max (fstVal nums1) (fstVal nums2)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1 : nums1.val.length = 1) (h2 : nums2.val.length = 1)
    (hd1 : 1 ≤ fstVal nums1) (hd1' : fstVal nums1 ≤ 9)
    (hd2 : 1 ≤ fstVal nums2) (hd2' : fstVal nums2 ≤ 9), (fstVal nums1 = fstVal nums2 →
      ∃ r : I64, min_number nums1 nums2 = ok r ∧ r.val = fstVal nums1) ∧
    (fstVal nums1 ≠ fstVal nums2 →
      ∃ r : I64, min_number nums1 nums2 = ok r ∧
        r.val = 10 * min (fstVal nums1) (fstVal nums2) + max (fstVal nums1) (fstVal nums2))) := by
  sorry

end AegisSpec.MinNumber
