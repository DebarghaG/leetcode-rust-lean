import Aegis.MaxUncrossedLines.Code.Funs

/-!
# Specifications of `Aegis.MaxUncrossedLines.max_uncrossed_lines`

LeetCode problem `uncrossed-lines`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxUncrossedLines

open Aegis.MaxUncrossedLines

def valAt? (a : Slice Std.I64) (i : ℕ) : Option ℤ := (a.val[i]?).map (fun x => x.val)

def ValuesInRange (a : Slice Std.I64) : Prop :=
  ∀ (i : ℕ) (x : Std.I64), a.val[i]? = some x → 1 ≤ x.val ∧ x.val ≤ 2000

def IsUncrossedMatching (a b : Slice Std.I64) (M : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ M, p.1 < a.val.length ∧ p.2 < b.val.length ∧ valAt? a p.1 = valAt? b p.2) ∧
  (∀ p ∈ M, ∀ q ∈ M, p ≠ q → p.1 ≠ q.1) ∧
  (∀ p ∈ M, ∀ q ∈ M, p ≠ q → p.2 ≠ q.2) ∧
  (∀ p ∈ M, ∀ q ∈ M, p.1 < q.1 → p.2 < q.2)

def IsMaxUncrossedCard (a b : Slice Std.I64) (k : ℤ) : Prop :=
  (∃ M : Finset (ℕ × ℕ), IsUncrossedMatching a b M ∧ (M.card : ℤ) = k) ∧
  ∀ M : Finset (ℕ × ℕ), IsUncrossedMatching a b M → (M.card : ℤ) ≤ k

def countOf (a : Slice Std.I64) (c : ℤ) : ℕ := a.val.countP (fun x => x.val = c)

@[reducible] def Occurs (a : Slice Std.I64) (c : ℤ) : Prop := 0 < countOf a c

def minCountSum (a b : Slice Std.I64) : ℕ :=
  ∑ c ∈ Finset.Icc (1 : ℕ) 2000, min (countOf a (c : ℤ)) (countOf b (c : ℤ))

def commonValueCount (a b : Slice Std.I64) : ℕ :=
  ((Finset.Icc (1 : ℕ) 2000).filter (fun (c : ℕ) => Occurs a (c : ℤ) ∧ Occurs b (c : ℤ))).card

theorem le_usize_max {n : ℕ} (h : n ≤ 500) : n ≤ Aeneas.Std.Usize.max := by
  have hmax : (500 : ℕ) ≤ Aeneas.Std.Usize.max := by
    simp only [Aeneas.Std.Usize.max, Aeneas.Std.Usize.numBits, Aeneas.Std.UScalarTy.numBits]
    have h2 : (2 : ℕ) ^ 32 ≤ 2 ^ System.Platform.numBits :=
      Nat.pow_le_pow_right (by norm_num) System.Platform.le_numBits
    have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
    omega
  omega

def ofList (l : List Std.I64) (h : l.length ≤ 500) : Slice Std.I64 :=
  Slice.from l (le_usize_max h)

@[simp] theorem ofList_val (l : List Std.I64) (h : l.length ≤ 500) : (ofList l h).val = l :=
  Aeneas.Data.ListN.ListN.from_to_inverse

/-- Whenever max_uncrossed_lines(nums1, nums2) returns a result r, r is the maximum cardinality of a set M of pairs (i, j) such that: (a) 0 <= i < len(nums1) and 0 <= j < len(nums2); (b) nums1[i] = nums2[j]; (c) no two distinct pairs in M have the same first coordinate and no two distinct pairs in M have the same second coordinate; and (d) for any two distinct pairs (i, j) and (i', j') in M, if i < i' then j < j'. The empty set is allowed. Equivalently, r is the length of a longest common subsequence of nums1 and nums2.
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000. -/
theorem spec_1 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    IsMaxUncrossedCard nums1 nums2 r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r), IsMaxUncrossedCard nums1 nums2 r.val) := by
  sorry

/-- The call max_uncrossed_lines(nums1, nums2) returns a result r and does not fail: it does not panic, go out of bounds, or overflow. The returned i64 represents a nonnegative mathematical integer.
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000. -/
theorem spec_2 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2) :
    ∃ r : Std.I64, max_uncrossed_lines nums1 nums2 = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2), ∃ r : Std.I64, max_uncrossed_lines nums1 nums2 = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- Whenever max_uncrossed_lines(nums1, nums2) returns a result r, 0 <= r <= min(len(nums1), len(nums2)).
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000. -/
theorem spec_3 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    0 ≤ r.val ∧ r.val ≤ ((min nums1.val.length nums2.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r), 0 ≤ r.val ∧ r.val ≤ ((min nums1.val.length nums2.val.length : ℕ) : ℤ)) := by
  sorry

/-- Whenever max_uncrossed_lines(nums1, nums2) returns a result r, there exists a set M of exactly r pairs (i, j) such that: (a) 0 <= i < len(nums1) and 0 <= j < len(nums2); (b) nums1[i] = nums2[j]; (c) no two distinct pairs in M have the same first coordinate and no two distinct pairs in M have the same second coordinate; and (d) for any two distinct pairs (i, j) and (i', j') in M, if i < i' then j < j'.
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000. -/
theorem spec_4 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    ∃ M : Finset (ℕ × ℕ), IsUncrossedMatching nums1 nums2 M ∧ (M.card : ℤ) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r), ∃ M : Finset (ℕ × ℕ), IsUncrossedMatching nums1 nums2 M ∧ (M.card : ℤ) = r.val) := by
  sorry

/-- Whenever max_uncrossed_lines(nums1, nums2) returns a result r, every set M of pairs (i, j) satisfying (a) 0 <= i < len(nums1), 0 <= j < len(nums2), (b) nums1[i] = nums2[j], (c) no two distinct pairs in M have the same first coordinate and no two distinct pairs in M have the same second coordinate, and (d) for any two distinct pairs (i, j) and (i', j') in M, if i < i' then j < j', has cardinality at most r.
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000. -/
theorem spec_5 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    ∀ M : Finset (ℕ × ℕ), IsUncrossedMatching nums1 nums2 M → (M.card : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r), ∀ M : Finset (ℕ × ℕ), IsUncrossedMatching nums1 nums2 M → (M.card : ℤ) ≤ r.val) := by
  sorry

/-- For every nums1 and nums2 satisfying the preconditions, if max_uncrossed_lines(nums1, nums2) returns r and max_uncrossed_lines(nums2, nums1) returns r', then r = r'.
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000. -/
theorem spec_6 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r r' : Std.I64)
    (hr : max_uncrossed_lines nums1 nums2 = ok r)
    (hr' : max_uncrossed_lines nums2 nums1 = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r r' : Std.I64)
    (hr : max_uncrossed_lines nums1 nums2 = ok r)
    (hr' : max_uncrossed_lines nums2 nums1 = ok r'), r.val = r'.val) := by
  sorry

/-- Let rev1 be the array of length len(nums1) defined by rev1[i] = nums1[len(nums1) - 1 - i] for 0 <= i < len(nums1), and let rev2 be the array of length len(nums2) defined by rev2[j] = nums2[len(nums2) - 1 - j] for 0 <= j < len(nums2). If max_uncrossed_lines(nums1, nums2) returns r and max_uncrossed_lines(rev1, rev2) returns r', then r = r'.
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000. -/
theorem spec_7 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r r' : Std.I64)
    (hr : max_uncrossed_lines nums1 nums2 = ok r)
    (hr' : max_uncrossed_lines
        (ofList nums1.val.reverse (by simp only [List.length_reverse]; omega))
        (ofList nums2.val.reverse (by simp only [List.length_reverse]; omega)) = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r r' : Std.I64)
    (hr : max_uncrossed_lines nums1 nums2 = ok r)
    (hr' : max_uncrossed_lines
        (ofList nums1.val.reverse (by simp only [List.length_reverse]; omega))
        (ofList nums2.val.reverse (by simp only [List.length_reverse]; omega)) = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever max_uncrossed_lines(nums1, nums2) returns a result r, r = 1 if there exists an index j with 0 <= j < len(nums2) and nums2[j] = nums1[0], and r = 0 otherwise.
  Preconditions: len(nums1) = 1, 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000. -/
theorem spec_8 (nums1 nums2 : Slice Std.I64)
    (h1len : nums1.val.length = 1)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    ((∃ j : ℕ, j < nums2.val.length ∧ valAt? nums2 j = valAt? nums1 0) → r.val = 1) ∧
    (¬ (∃ j : ℕ, j < nums2.val.length ∧ valAt? nums2 j = valAt? nums1 0) → r.val = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1len : nums1.val.length = 1)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r), ((∃ j : ℕ, j < nums2.val.length ∧ valAt? nums2 j = valAt? nums1 0) → r.val = 1) ∧
    (¬ (∃ j : ℕ, j < nums2.val.length ∧ valAt? nums2 j = valAt? nums1 0) → r.val = 0)) := by
  sorry

/-- Whenever max_uncrossed_lines(nums1, nums2) returns a result r, r = 0 if and only if there is no pair (i, j) with 0 <= i < len(nums1), 0 <= j < len(nums2), and nums1[i] = nums2[j].
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000. -/
theorem spec_9 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    (r.val = 0 ↔
      ¬ ∃ (i j : ℕ), i < nums1.val.length ∧ j < nums2.val.length ∧
        valAt? nums1 i = valAt? nums2 j) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r), (r.val = 0 ↔
      ¬ ∃ (i j : ℕ), i < nums1.val.length ∧ j < nums2.val.length ∧
        valAt? nums1 i = valAt? nums2 j)) := by
  sorry

/-- Whenever max_uncrossed_lines(nums1, nums2) returns a result r, r = len(nums1).
  Preconditions: len(nums1) = len(nums2), 1 <= len(nums1) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000 and nums1[i] = nums2[i]. -/
theorem spec_10 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (hlen : nums1.val.length = nums2.val.length)
    (hv : ∀ (i : ℕ) (x y : Std.I64), nums1.val[i]? = some x → nums2.val[i]? = some y →
      1 ≤ x.val ∧ x.val ≤ 2000 ∧ x.val = y.val)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    r.val = (nums1.val.length : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (hlen : nums1.val.length = nums2.val.length)
    (hv : ∀ (i : ℕ) (x y : Std.I64), nums1.val[i]? = some x → nums2.val[i]? = some y →
      1 ≤ x.val ∧ x.val ≤ 2000 ∧ x.val = y.val)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r), r.val = (nums1.val.length : ℤ)) := by
  sorry

/-- Whenever max_uncrossed_lines(nums1, nums2) returns a result r, r = min(len(nums1), len(nums2)).
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; there exists an integer c with 1 <= c <= 2000 such that for every i with 0 <= i < len(nums1), nums1[i] = c, and for every j with 0 <= j < len(nums2), nums2[j] = c. -/
theorem spec_11 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2000)
    (hconst1 : ∀ (i : ℕ) (x : Std.I64), nums1.val[i]? = some x → x.val = c)
    (hconst2 : ∀ (j : ℕ) (y : Std.I64), nums2.val[j]? = some y → y.val = c)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    r.val = ((min nums1.val.length nums2.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2000)
    (hconst1 : ∀ (i : ℕ) (x : Std.I64), nums1.val[i]? = some x → x.val = c)
    (hconst2 : ∀ (j : ℕ) (y : Std.I64), nums2.val[j]? = some y → y.val = c)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r), r.val = ((min nums1.val.length nums2.val.length : ℕ) : ℤ)) := by
  sorry

/-- Whenever max_uncrossed_lines(nums1, nums2) returns a result r, r <= sum_{c=1}^{2000} min(count1(c), count2(c)), where count1(c) is the number of indices i with 0 <= i < len(nums1) and nums1[i] = c, and count2(c) is the number of indices j with 0 <= j < len(nums2) and nums2[j] = c.
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000. -/
theorem spec_12 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    r.val ≤ (minCountSum nums1 nums2 : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r), r.val ≤ (minCountSum nums1 nums2 : ℤ)) := by
  sorry

/-- Let p1 be the slice consisting of nums1[0], nums1[1], ..., nums1[len(nums1) - 2], and let p2 be the slice consisting of nums2[0], nums2[1], ..., nums2[len(nums2) - 2]. If max_uncrossed_lines(p1, p2) returns s and max_uncrossed_lines(nums1, nums2) returns r, then r = s + 1.
  Preconditions: len(nums1) and len(nums2) are integers with 2 <= len(nums1) <= 500 and 2 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000; nums1[len(nums1)-1] = nums2[len(nums2)-1]. -/
theorem spec_13 (nums1 nums2 : Slice Std.I64)
    (h1lo : 2 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 2 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (hlast : valAt? nums1 (nums1.val.length - 1) = valAt? nums2 (nums2.val.length - 1))
    (s r : Std.I64)
    (hs : max_uncrossed_lines
        (ofList (List.take (nums1.val.length - 1) nums1.val)
          (by simp only [List.length_take]; omega))
        (ofList (List.take (nums2.val.length - 1) nums2.val)
          (by simp only [List.length_take]; omega)) = ok s)
    (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    r.val = s.val + 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 2 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 2 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (hlast : valAt? nums1 (nums1.val.length - 1) = valAt? nums2 (nums2.val.length - 1))
    (s r : Std.I64)
    (hs : max_uncrossed_lines
        (ofList (List.take (nums1.val.length - 1) nums1.val)
          (by simp only [List.length_take]; omega))
        (ofList (List.take (nums2.val.length - 1) nums2.val)
          (by simp only [List.length_take]; omega)) = ok s)
    (hr : max_uncrossed_lines nums1 nums2 = ok r), r.val = s.val + 1) := by
  sorry

/-- Let nums1' be nums1 followed by extra1, and let nums2' be nums2 followed by extra2. If max_uncrossed_lines(nums1, nums2) returns r and max_uncrossed_lines(nums1', nums2') returns r', then r' >= r.
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000; extra1 and extra2 are finite arrays of integers in the range 1 <= value <= 2000 such that len(nums1) + len(extra1) <= 500 and len(nums2) + len(extra2) <= 500. -/
theorem spec_14 (nums1 nums2 extra1 extra2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (he1 : ValuesInRange extra1) (he2 : ValuesInRange extra2)
    (hlen1 : nums1.val.length + extra1.val.length ≤ 500)
    (hlen2 : nums2.val.length + extra2.val.length ≤ 500)
    (r r' : Std.I64)
    (hr : max_uncrossed_lines nums1 nums2 = ok r)
    (hr' : max_uncrossed_lines
        (ofList (nums1.val ++ extra1.val) (by simp only [List.length_append]; omega))
        (ofList (nums2.val ++ extra2.val) (by simp only [List.length_append]; omega)) = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums1 nums2 extra1 extra2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (he1 : ValuesInRange extra1) (he2 : ValuesInRange extra2)
    (hlen1 : nums1.val.length + extra1.val.length ≤ 500)
    (hlen2 : nums2.val.length + extra2.val.length ≤ 500)
    (r r' : Std.I64)
    (hr : max_uncrossed_lines nums1 nums2 = ok r)
    (hr' : max_uncrossed_lines
        (ofList (nums1.val ++ extra1.val) (by simp only [List.length_append]; omega))
        (ofList (nums2.val ++ extra2.val) (by simp only [List.length_append]; omega)) = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Let p1 be the slice consisting of nums1[0], ..., nums1[len(nums1)-2] and let p2 be the slice consisting of nums2[0], ..., nums2[len(nums2)-2]. If max_uncrossed_lines(p1, nums2) returns s1, max_uncrossed_lines(nums1, p2) returns s2, and max_uncrossed_lines(nums1, nums2) returns r, then r = max(s1, s2).
  Preconditions: len(nums1) and len(nums2) are integers with 2 <= len(nums1) <= 500 and 2 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000; nums1[len(nums1)-1] != nums2[len(nums2)-1]. -/
theorem spec_15 (nums1 nums2 : Slice Std.I64)
    (h1lo : 2 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 2 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (hlast : valAt? nums1 (nums1.val.length - 1) ≠ valAt? nums2 (nums2.val.length - 1))
    (s1 s2 r : Std.I64)
    (hs1 : max_uncrossed_lines
        (ofList (List.take (nums1.val.length - 1) nums1.val)
          (by simp only [List.length_take]; omega)) nums2 = ok s1)
    (hs2 : max_uncrossed_lines nums1
        (ofList (List.take (nums2.val.length - 1) nums2.val)
          (by simp only [List.length_take]; omega)) = ok s2)
    (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    r.val = max s1.val s2.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 2 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 2 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (hlast : valAt? nums1 (nums1.val.length - 1) ≠ valAt? nums2 (nums2.val.length - 1))
    (s1 s2 r : Std.I64)
    (hs1 : max_uncrossed_lines
        (ofList (List.take (nums1.val.length - 1) nums1.val)
          (by simp only [List.length_take]; omega)) nums2 = ok s1)
    (hs2 : max_uncrossed_lines nums1
        (ofList (List.take (nums2.val.length - 1) nums2.val)
          (by simp only [List.length_take]; omega)) = ok s2)
    (hr : max_uncrossed_lines nums1 nums2 = ok r), r.val = max s1.val s2.val) := by
  sorry

/-- Whenever max_uncrossed_lines(nums1, nums2) returns a result r, r equals the number of integers c with 1 <= c <= 2000 such that c occurs in nums1 and c occurs in nums2.
  Preconditions: len(nums1) and len(nums2) are integers with 1 <= len(nums1) <= 500 and 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000; nums1 is strictly increasing (nums1[i] < nums1[i+1] for 0 <= i < len(nums1)-1) and nums2 is strictly increasing (nums2[j] < nums2[j+1] for 0 <= j < len(nums2)-1). -/
theorem spec_16 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (hin1 : ∀ (i : ℕ) (x y : Std.I64), nums1.val[i]? = some x → nums1.val[i + 1]? = some y →
      x.val < y.val)
    (hin2 : ∀ (j : ℕ) (x y : Std.I64), nums2.val[j]? = some x → nums2.val[j + 1]? = some y →
      x.val < y.val)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    r.val = (commonValueCount nums1 nums2 : ℤ) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2lo : 1 ≤ nums2.val.length) (h2hi : nums2.val.length ≤ 500)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (hin1 : ∀ (i : ℕ) (x y : Std.I64), nums1.val[i]? = some x → nums1.val[i + 1]? = some y →
      x.val < y.val)
    (hin2 : ∀ (j : ℕ) (x y : Std.I64), nums2.val[j]? = some x → nums2.val[j + 1]? = some y →
      x.val < y.val)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r), r.val = (commonValueCount nums1 nums2 : ℤ)) := by
  sorry

/-- Whenever max_uncrossed_lines(nums1, nums2) returns a result r, r = 1 if there exists an index i with 0 <= i < len(nums1) and nums1[i] = nums2[0], and r = 0 otherwise.
  Preconditions: 1 <= len(nums1) <= 500, len(nums2) = 1; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 2000; for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 2000. -/
theorem spec_17 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2len : nums2.val.length = 1)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r) :
    ((∃ i : ℕ, i < nums1.val.length ∧ valAt? nums1 i = valAt? nums2 0) → r.val = 1) ∧
    (¬ (∃ i : ℕ, i < nums1.val.length ∧ valAt? nums1 i = valAt? nums2 0) → r.val = 0) := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ nums1.val.length) (h1hi : nums1.val.length ≤ 500)
    (h2len : nums2.val.length = 1)
    (hv1 : ValuesInRange nums1) (hv2 : ValuesInRange nums2)
    (r : Std.I64) (hr : max_uncrossed_lines nums1 nums2 = ok r), ((∃ i : ℕ, i < nums1.val.length ∧ valAt? nums1 i = valAt? nums2 0) → r.val = 1) ∧
    (¬ (∃ i : ℕ, i < nums1.val.length ∧ valAt? nums1 i = valAt? nums2 0) → r.val = 0)) := by
  sorry

end AegisSpec.MaxUncrossedLines
