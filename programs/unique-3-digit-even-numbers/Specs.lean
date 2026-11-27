import Aegis.TotalNumbers.Code.Funs

/-!
# Specifications of `Aegis.TotalNumbers.total_numbers`

LeetCode problem `unique-3-digit-even-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.TotalNumbers

namespace AegisSpec.TotalNumbers

def occ (d : ℤ) (xs : List Std.I64) : ℕ :=
  xs.countP (fun x => decide (x.val = d))

def decDigits (n : ℤ) : List ℤ :=
  [n / 100, n / 10 % 10, n % 10]

def decocc (d : ℤ) (n : ℤ) : ℕ :=
  (decDigits n).countP (fun m => decide (m = d))

def entry (xs : List Std.I64) (i : ℕ) : ℤ :=
  (xs.getD i 0#i64).val

def threeDigitNumbers : Finset ℤ :=
  (Finset.range 900).image (fun i : ℕ => (i : ℤ) + 100)

def digitsFit (xs : List Std.I64) (n : ℤ) : Prop :=
  ∀ d : ℤ, 0 ≤ d → d ≤ 9 → decocc d n ≤ occ d xs

noncomputable def fittingNumbers (xs : List Std.I64) : Finset ℤ := by
  classical
  exact threeDigitNumbers.filter (fun n => digitsFit xs n)

noncomputable def evenFittingNumbers (xs : List Std.I64) : Finset ℤ := by
  classical
  exact threeDigitNumbers.filter (fun n => Even n ∧ digitsFit xs n)

def indexTriples (len : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.range len ×ˢ (Finset.range len ×ˢ Finset.range len)

def validTriples (xs : List Std.I64) : Finset (ℕ × ℕ × ℕ) :=
  (indexTriples xs.length).filter (fun p =>
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧
      entry xs p.1 ≠ 0 ∧ entry xs p.2.2 % 2 = 0)

def tripleCount (xs : List Std.I64) : ℕ :=
  (validTriples xs).card

def reorderTriples (d0 d1 d2 : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  {(d0, d1, d2), (d0, d2, d1), (d1, d0, d2), (d1, d2, d0), (d2, d0, d1), (d2, d1, d0)}

noncomputable def reorderValues (d0 d1 d2 : ℤ) : Finset ℤ :=
  ((reorderTriples d0 d1 d2).filter (fun p => p.1 ≠ 0 ∧ p.2.2 % 2 = 0)).image
    (fun p => 100 * p.1 + 10 * p.2.1 + p.2.2)

/-- Let occ(d, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = d. For an integer n with 100 <= n <= 999, let decocc(d, n) be the number of occurrences of digit d among the three decimal digits of n (hundreds, tens, ones). The function returns a result r and r equals the cardinality of the set {n | 100 <= n <= 999, n is even, and for every d in {0,...,9}, decocc(d,n) <= occ(d,digits)}.
  Preconditions: 3 <= len(digits) <= 10, and for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9. -/
theorem spec_1 (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r) :
    r.val = ((evenFittingNumbers digits.val).card : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r), r.val = ((evenFittingNumbers digits.val).card : ℤ)) := by
  sorry

/-- For every such input, the function returns a result r; it does not panic, overflow, or go out of bounds.
  Preconditions: 3 <= len(digits) <= 10, and for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9. -/
theorem spec_2 (digits : Slice Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9) :
    ∃ r : Std.I64, total_numbers digits = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (digits : Slice Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9), ∃ r : Std.I64, total_numbers digits = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: 3 <= len(digits) <= 10, and for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9. -/
theorem spec_3 (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 450.
  Preconditions: 3 <= len(digits) <= 10, and for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9. -/
theorem spec_4 (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r) :
    r.val ≤ 450 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r), r.val ≤ 450) := by
  sorry

/-- Let count_d(xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = d. If for every d in {0,...,9}, count_d(xs) = count_d(ys), then whenever total_numbers(xs) returns r_x and total_numbers(ys) returns r_y, r_x = r_y.
  Preconditions: Both xs and ys satisfy 3 <= len(xs) <= 10, 3 <= len(ys) <= 10, and all their entries are in {0,...,9}. -/
theorem spec_5 (xs ys : Slice Std.I64) (rx ry : Std.I64)
    (hlenx : 3 ≤ xs.val.length ∧ xs.val.length ≤ 10)
    (hleny : 3 ≤ ys.val.length ∧ ys.val.length ≤ 10)
    (hdigx : ∀ x ∈ xs.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hdigy : ∀ y ∈ ys.val, 0 ≤ y.val ∧ y.val ≤ 9)
    (hcount : ∀ d : ℤ, 0 ≤ d → d ≤ 9 → occ d xs.val = occ d ys.val)
    (hrx : total_numbers xs = ok rx)
    (hry : total_numbers ys = ok ry) :
    rx.val = ry.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (xs ys : Slice Std.I64) (rx ry : Std.I64)
    (hlenx : 3 ≤ xs.val.length ∧ xs.val.length ≤ 10)
    (hleny : 3 ≤ ys.val.length ∧ ys.val.length ≤ 10)
    (hdigx : ∀ x ∈ xs.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hdigy : ∀ y ∈ ys.val, 0 ≤ y.val ∧ y.val ≤ 9)
    (hcount : ∀ d : ℤ, 0 ≤ d → d ≤ 9 → occ d xs.val = occ d ys.val)
    (hrx : total_numbers xs = ok rx)
    (hry : total_numbers ys = ok ry), rx.val = ry.val) := by
  sorry

/-- Let count_d(xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = d. If for every d in {0,...,9}, min(count_d(xs), 3) = min(count_d(ys), 3), then whenever total_numbers(xs) returns r_x and total_numbers(ys) returns r_y, r_x = r_y.
  Preconditions: Both xs and ys satisfy 3 <= len(xs) <= 10, 3 <= len(ys) <= 10, and all their entries are in {0,...,9}. -/
theorem spec_6 (xs ys : Slice Std.I64) (rx ry : Std.I64)
    (hlenx : 3 ≤ xs.val.length ∧ xs.val.length ≤ 10)
    (hleny : 3 ≤ ys.val.length ∧ ys.val.length ≤ 10)
    (hdigx : ∀ x ∈ xs.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hdigy : ∀ y ∈ ys.val, 0 ≤ y.val ∧ y.val ≤ 9)
    (hcount : ∀ d : ℤ, 0 ≤ d → d ≤ 9 → min (occ d xs.val) 3 = min (occ d ys.val) 3)
    (hrx : total_numbers xs = ok rx)
    (hry : total_numbers ys = ok ry) :
    rx.val = ry.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (xs ys : Slice Std.I64) (rx ry : Std.I64)
    (hlenx : 3 ≤ xs.val.length ∧ xs.val.length ≤ 10)
    (hleny : 3 ≤ ys.val.length ∧ ys.val.length ≤ 10)
    (hdigx : ∀ x ∈ xs.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hdigy : ∀ y ∈ ys.val, 0 ≤ y.val ∧ y.val ≤ 9)
    (hcount : ∀ d : ℤ, 0 ≤ d → d ≤ 9 → min (occ d xs.val) 3 = min (occ d ys.val) 3)
    (hrx : total_numbers xs = ok rx)
    (hry : total_numbers ys = ok ry), rx.val = ry.val) := by
  sorry

/-- Let digits' be the slice obtained from digits by appending one extra entry equal to d. Whenever total_numbers(digits) returns r and total_numbers(digits') returns r', we have r <= r'.
  Preconditions: 3 <= len(digits) <= 9, every entry of digits is in {0,...,9}, and d is an integer with 0 <= d <= 9. -/
theorem spec_7 (digits digits' : Slice Std.I64) (d r r' : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 9)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hd : 0 ≤ d.val ∧ d.val ≤ 9)
    (happ : digits'.val = digits.val ++ [d])
    (hr : total_numbers digits = ok r)
    (hr' : total_numbers digits' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (digits digits' : Slice Std.I64) (d r r' : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 9)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hd : 0 ≤ d.val ∧ d.val ≤ 9)
    (happ : digits'.val = digits.val ++ [d])
    (hr : total_numbers digits = ok r)
    (hr' : total_numbers digits' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if either no entry of digits is even, or no entry of digits is nonzero.
  Preconditions: 3 <= len(digits) <= 10, and for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9. -/
theorem spec_8 (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r) :
    (r.val = 0 ↔ (∀ x ∈ digits.val, ¬ Even x.val) ∨ (∀ x ∈ digits.val, x.val = 0)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r), (r.val = 0 ↔ (∀ x ∈ digits.val, ¬ Even x.val) ∨ (∀ x ∈ digits.val, x.val = 0))) := by
  sorry

/-- If every entry of digits is equal to the same digit d, then whenever the function returns a result r, r = 1 when d is in {2,4,6,8}, and r = 0 otherwise.
  Preconditions: 3 <= len(digits) <= 10, and for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9. -/
theorem spec_9 (digits : Slice Std.I64) (d r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hall : ∀ x ∈ digits.val, x.val = d.val)
    (hr : total_numbers digits = ok r) :
    ((d.val ∈ ({2, 4, 6, 8} : Finset ℤ)) → r.val = 1) ∧
      ((d.val ∉ ({2, 4, 6, 8} : Finset ℤ)) → r.val = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (digits : Slice Std.I64) (d r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hall : ∀ x ∈ digits.val, x.val = d.val)
    (hr : total_numbers digits = ok r), ((d.val ∈ ({2, 4, 6, 8} : Finset ℤ)) → r.val = 1) ∧
      ((d.val ∉ ({2, 4, 6, 8} : Finset ℤ)) → r.val = 0)) := by
  sorry

/-- Let T be the number of ordered triples (i,j,k) of indices such that 0 <= i,j,k < len(digits), i, j, and k are pairwise distinct, digits[i] != 0, and digits[k] is even. Whenever the function returns a result r, r <= T.
  Preconditions: 3 <= len(digits) <= 10, and for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9. -/
theorem spec_10 (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r) :
    r.val ≤ (tripleCount digits.val : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r), r.val ≤ (tripleCount digits.val : ℤ)) := by
  sorry

/-- Let occ(d, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = d, and for 100 <= n <= 999 let decocc(d,n) be the number of occurrences of digit d among the decimal digits of n. Whenever the function returns a result r, if r > 0 then there exists an integer n such that 100 <= n <= 999, n is even, and for every d in {0,...,9}, decocc(d,n) <= occ(d,digits).
  Preconditions: 3 <= len(digits) <= 10, and for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9. -/
theorem spec_11 (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r) :
    0 < r.val →
      ∃ n : ℤ, 100 ≤ n ∧ n ≤ 999 ∧ Even n ∧ digitsFit digits.val n := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hr : total_numbers digits = ok r), 0 < r.val →
      ∃ n : ℤ, 100 ≤ n ∧ n ≤ 999 ∧ Even n ∧ digitsFit digits.val n) := by
  sorry

/-- Let occ(d, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = d, and for 100 <= n <= 999 let decocc(d,n) be the number of occurrences of digit d among the decimal digits of n. Whenever the function returns a result r, r equals the cardinality of the set {n | 100 <= n <= 999 and for every d in {0,...,9}, decocc(d,n) <= occ(d,digits)}.
  Preconditions: 3 <= len(digits) <= 10, every entry of digits is in {0,...,9}, and every entry of digits is even (i.e., each entry is in {0,2,4,6,8}). -/
theorem spec_12 (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (heven : ∀ x ∈ digits.val, Even x.val)
    (hr : total_numbers digits = ok r) :
    r.val = ((fittingNumbers digits.val).card : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (digits : Slice Std.I64) (r : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (heven : ∀ x ∈ digits.val, Even x.val)
    (hr : total_numbers digits = ok r), r.val = ((fittingNumbers digits.val).card : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r equals the cardinality of the set of integers of the form 100*a + 10*b + c such that (a,b,c) is a reordering of the three entries digits[0], digits[1], digits[2], a != 0, and c is even.
  Preconditions: 3 <= len(digits) <= 10, len(digits) = 3, and for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9. -/
theorem spec_13 (digits : Slice Std.I64) (r x0 x1 x2 : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hlen3 : digits.val.length = 3)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hlist : digits.val = [x0, x1, x2])
    (hr : total_numbers digits = ok r) :
    r.val = ((reorderValues x0.val x1.val x2.val).card : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (digits : Slice Std.I64) (r x0 x1 x2 : Std.I64)
    (hlen : 3 ≤ digits.val.length ∧ digits.val.length ≤ 10)
    (hlen3 : digits.val.length = 3)
    (hdig : ∀ x ∈ digits.val, 0 ≤ x.val ∧ x.val ≤ 9)
    (hlist : digits.val = [x0, x1, x2])
    (hr : total_numbers digits = ok r), r.val = ((reorderValues x0.val x1.val x2.val).card : ℤ)) := by
  sorry

end AegisSpec.TotalNumbers
