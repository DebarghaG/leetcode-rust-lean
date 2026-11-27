import Aegis.MaxDiff.Code.Funs

/-!
# Specifications of `Aegis.MaxDiff.max_diff`

LeetCode problem `max-difference-you-can-get-from-changing-an-integer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxDiff

def digitsOf (n : ℕ) : List ℕ :=
  if n = 0 then [] else digitsOf (n / 10) ++ [n % 10]
termination_by n
decreasing_by
  omega

def numOfDigits (l : List ℕ) : ℕ :=
  l.foldl (fun acc d => acc * 10 + d) 0

def replaceAll (l : List ℕ) (x y : ℕ) : List ℕ :=
  l.map (fun d => if d = x then y else d)

def T (num x y : ℕ) : ℕ :=
  numOfDigits (replaceAll (digitsOf num) x y)

def validPair (num x y : ℕ) : Bool :=
  let s' := replaceAll (digitsOf num) x y
  !s'.isEmpty && (s'.head? != some 0)

def Svals (num : ℕ) : List ℕ :=
  ((List.range 10).product (List.range 10)).filterMap
    (fun p => if validPair num p.1 p.2 then some (T num p.1 p.2) else none)

def Smax (num : ℕ) : ℕ :=
  (Svals num).max?.getD 0

def Smin (num : ℕ) : ℕ :=
  (Svals num).min?.getD 0

def maxC1 (num : ℕ) : ℕ :=
  match (digitsOf num).find? (fun d => decide (d ≠ 9)) with
  | some x => T num x 9
  | none => num

def minC1 (num : ℕ) : ℕ :=
  match digitsOf num with
  | [] => num
  | d :: tl =>
    if d ≠ 1 then T num d 1
    else
      match tl.find? (fun e => decide (2 ≤ e)) with
      | some x => T num x 0
      | none => num

/-- Let s be the decimal representation of num (a string of digits without leading zeros, since num >= 1). For digits x and y in {0,...,9}, let T(num, x, y) be the integer whose decimal representation is obtained from s by replacing every occurrence of digit x with digit y. Call (x, y) valid if the first character of the resulting representation is not '0' (equivalently, either the first digit of s is not x, or y != 0). Let S(num) = { T(num, x, y) | x, y in {0,...,9} and (x, y) is valid }. Then whenever the function returns a result r, r = max(S(num)) - min(S(num)).
  Preconditions: 1 <= num <= 1000000000 -/
theorem spec_1 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r) :
    r.val = (Smax num.val.toNat : ℤ) - (Smin num.val.toNat : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r), r.val = (Smax num.val.toNat : ℤ) - (Smin num.val.toNat : ℤ)) := by
  sorry

/-- The function returns a result (it does not fail).
  Preconditions: 1 <= num <= 1000000000 -/
theorem spec_2 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000) :
    ∃ r : Std.I64, Aegis.MaxDiff.max_diff num = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000), ∃ r : Std.I64, Aegis.MaxDiff.max_diff num = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 8.
  Preconditions: 1 <= num <= 1000000000 -/
theorem spec_3 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r) :
    r.val ≥ 8 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r), r.val ≥ 8) := by
  sorry

/-- Whenever the function returns a result r, r <= 8000000000.
  Preconditions: 1 <= num <= 1000000000 -/
theorem spec_4 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r) :
    r.val ≤ 8000000000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r), r.val ≤ 8000000000) := by
  sorry

/-- If the decimal representation of num consists of a single digit d (with 1 <= d <= 9) repeated k times (k >= 1), then whenever the function returns a result r, r = 8 * (10^k - 1) / 9.
  Preconditions: 1 <= num <= 1000000000 -/
theorem spec_5 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (d k : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) (hk : 1 ≤ k)
    (hd : digitsOf num.val.toNat = List.replicate k d)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r) :
    r.val = 8 * ((10 : ℤ) ^ k - 1) / 9 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (d k : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) (hk : 1 ≤ k)
    (hd : digitsOf num.val.toNat = List.replicate k d)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r), r.val = 8 * ((10 : ℤ) ^ k - 1) / 9) := by
  sorry

/-- If the decimal representation of num contains only the digits 0 and 1 (and hence starts with 1), then whenever the function returns a result r, r = 8 * num.
  Preconditions: 1 <= num <= 1000000000 -/
theorem spec_6 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hd : ∀ z ∈ digitsOf num.val.toNat, z = 0 ∨ z = 1)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r) :
    r.val = 8 * num.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hd : ∀ z ∈ digitsOf num.val.toNat, z = 0 ∨ z = 1)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r), r.val = 8 * num.val) := by
  sorry

/-- If there exist integers d and k such that 2 <= d <= 8, k >= 0, and num = d * 10^k, then whenever the function returns a result r, r = 8 * 10^k.
  Preconditions: 1 <= num <= 1000000000 -/
theorem spec_7 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (d k : ℕ) (hd2 : 2 ≤ d) (hd8 : d ≤ 8) (hn : num.val = (d : ℤ) * 10 ^ k)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r) :
    r.val = 8 * (10 : ℤ) ^ k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (d k : ℕ) (hd2 : 2 ≤ d) (hd8 : d ≤ 8) (hn : num.val = (d : ℤ) * 10 ^ k)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r), r.val = 8 * (10 : ℤ) ^ k) := by
  sorry

/-- If there exists an integer k >= 0 such that num = 9 * 10^k, then whenever the function returns a result r, r = 9 * 10^k - 1.
  Preconditions: 1 <= num <= 1000000000 -/
theorem spec_8 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (k : ℕ) (hn : num.val = 9 * (10 : ℤ) ^ k)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r) :
    r.val = 9 * (10 : ℤ) ^ k - 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (k : ℕ) (hn : num.val = 9 * (10 : ℤ) ^ k)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r), r.val = 9 * (10 : ℤ) ^ k - 1) := by
  sorry

/-- Whenever the function returns a result r, r <= 8 * num, and r = 8 * num if and only if the decimal representation of num contains only the digits 0 and 1.
  Preconditions: 1 <= num <= 1000000000 -/
theorem spec_9 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r) :
    r.val ≤ 8 * num.val ∧
      (r.val = 8 * num.val ↔ ∀ z ∈ digitsOf num.val.toNat, z = 0 ∨ z = 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r), r.val ≤ 8 * num.val ∧
      (r.val = 8 * num.val ↔ ∀ z ∈ digitsOf num.val.toNat, z = 0 ∨ z = 1)) := by
  sorry

/-- Let s be the decimal representation of num (without leading zeros). For digits x,y in {0,...,9}, let s' be the string obtained from s by replacing every occurrence of digit x with digit y. Call (x,y) valid if s' is nonempty and s'[0] != '0' (equivalently, the resulting integer is nonzero and has no leading zeros), and write T(num,x,y) for the integer represented by s'. Whenever the function returns a result r, there exist digits x1,y1,x2,y2 in {0,...,9} such that (x1,y1) and (x2,y2) are valid, r = T(num,x1,y1) - T(num,x2,y2), and for every valid transformation (x,y), T(num,x,y) <= T(num,x1,y1) and T(num,x,y) >= T(num,x2,y2).
  Preconditions: 1 <= num <= 1000000000 -/
theorem spec_10 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r) :
    ∃ x1 y1 x2 y2 : ℕ,
      x1 ≤ 9 ∧ y1 ≤ 9 ∧ x2 ≤ 9 ∧ y2 ≤ 9 ∧
      validPair num.val.toNat x1 y1 = true ∧
      validPair num.val.toNat x2 y2 = true ∧
      r.val = (T num.val.toNat x1 y1 : ℤ) - (T num.val.toNat x2 y2 : ℤ) ∧
      (∀ x y : ℕ, x ≤ 9 → y ≤ 9 → validPair num.val.toNat x y = true →
        T num.val.toNat x y ≤ T num.val.toNat x1 y1 ∧
        T num.val.toNat x y ≥ T num.val.toNat x2 y2) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r), ∃ x1 y1 x2 y2 : ℕ,
      x1 ≤ 9 ∧ y1 ≤ 9 ∧ x2 ≤ 9 ∧ y2 ≤ 9 ∧
      validPair num.val.toNat x1 y1 = true ∧
      validPair num.val.toNat x2 y2 = true ∧
      r.val = (T num.val.toNat x1 y1 : ℤ) - (T num.val.toNat x2 y2 : ℤ) ∧
      (∀ x y : ℕ, x ≤ 9 → y ≤ 9 → validPair num.val.toNat x y = true →
        T num.val.toNat x y ≤ T num.val.toNat x1 y1 ∧
        T num.val.toNat x y ≥ T num.val.toNat x2 y2)) := by
  sorry

/-- Let s be the decimal representation of num. The maximum of S(num) is obtained by taking the leftmost digit of s that is not '9' (if any) and replacing all occurrences of that digit with '9'; if all digits are '9', the maximum is num. The minimum of S(num) is obtained as follows: if the first digit of s is not '1', replace all occurrences of that first digit with '1'; otherwise, if there is a digit other than the first that is at least 2, take the leftmost such digit and replace all occurrences of it with '0'; otherwise the minimum is num.
  Preconditions: 1 <= num <= 1000000000 -/
theorem spec_11 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r) :
    r.val = (maxC1 num.val.toNat : ℤ) - (minC1 num.val.toNat : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaxDiff.max_diff num = ok r), r.val = (maxC1 num.val.toNat : ℤ) - (minC1 num.val.toNat : ℤ)) := by
  sorry

end AegisSpec.MaxDiff
