import Aegis.KthPalindrome.Code.Funs

/-!
# Specifications of `Aegis.KthPalindrome.kth_palindrome`

LeetCode problem `find-palindrome-with-fixed-length`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.KthPalindrome

  def digitsRev (n : ℕ) : List ℕ :=
    if h : n = 0 then [] else n % 10 :: digitsRev (n / 10)
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

  def digits (n : ℕ) : List ℕ := (digitsRev n).reverse

  def IsDecimalPalindrome (n : ℤ) : Prop :=
    0 < n ∧ (digits n.toNat).reverse = digits n.toNat

  instance instDecidableIsDecimalPalindrome (n : ℤ) : Decidable (IsDecimalPalindrome n) := by
    unfold IsDecimalPalindrome
    infer_instance

  def IsLDigitPalindrome (L : ℕ) (n : ℤ) : Prop :=
    IsDecimalPalindrome n ∧ (digits n.toNat).length = L

  instance instDecidableIsLDigitPalindrome (L : ℕ) (n : ℤ) :
      Decidable (IsLDigitPalindrome L n) := by
    unfold IsLDigitPalindrome IsDecimalPalindrome
    infer_instance

  def countLDigitPalindromesBelow (L : ℕ) (N : ℤ) : ℕ :=
    ((Finset.Icc 1 (N.toNat - 1)).filter (fun k : ℕ => IsLDigitPalindrome L (k : ℤ))).card

  def countBound (L : ℤ) : ℤ := (9 : ℤ) * 10 ^ ((L + 1) / 2 - 1).toNat

  def sliceAt (s : Aeneas.Std.Slice Aeneas.Std.I64) (i : ℕ) : ℤ :=
    (s.val.getD i 0#i64).val

  def vecAt (v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64) (i : ℕ) : ℤ :=
    (v.val.getD i 0#i64).val

  /-- Whenever kth_palindrome(queries, intLength) returns a result r, let L = intLength and let C = 9 * 10^(ceil(L/2) - 1), the number of positive palindromes whose decimal representation has exactly L digits. Then len(r) = len(queries), and for every i with 0 <= i < len(queries): if queries[i] > C then r[i] = -1; if queries[i] <= C then r[i] is the unique positive integer whose decimal representation has exactly L digits, reads the same forwards and backwards, and has exactly queries[i] - 1 positive L-digit palindromes strictly less than it.
    Preconditions: len(queries) is between 1 and 50000 inclusive, for every i with 0 <= i < len(queries), 1 <= queries[i] <= 1000000000, and 1 <= intLength <= 15. -/
  theorem spec_1
      (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
      (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
      (hq : ∀ i, i < queries.val.length →
        1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
      (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
      (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
      (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r) :
      r.val.length = queries.val.length ∧
        ∀ i, i < queries.val.length →
          (countBound intLength.val < sliceAt queries i → vecAt r i = -1) ∧
          (sliceAt queries i ≤ countBound intLength.val →
            IsLDigitPalindrome intLength.val.toNat (vecAt r i) ∧
              countLDigitPalindromesBelow intLength.val.toNat (vecAt r i) =
                (sliceAt queries i).toNat - 1 ∧
              ∀ n : ℤ, IsLDigitPalindrome intLength.val.toNat n →
                countLDigitPalindromesBelow intLength.val.toNat n =
                  (sliceAt queries i).toNat - 1 →
                n = vecAt r i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
        (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
        (hq : ∀ i, i < queries.val.length →
          1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
        (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
        (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
        (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r), r.val.length = queries.val.length ∧
          ∀ i, i < queries.val.length →
            (countBound intLength.val < sliceAt queries i → vecAt r i = -1) ∧
            (sliceAt queries i ≤ countBound intLength.val →
              IsLDigitPalindrome intLength.val.toNat (vecAt r i) ∧
                countLDigitPalindromesBelow intLength.val.toNat (vecAt r i) =
                  (sliceAt queries i).toNat - 1 ∧
                ∀ n : ℤ, IsLDigitPalindrome intLength.val.toNat n →
                  countLDigitPalindromesBelow intLength.val.toNat n =
                    (sliceAt queries i).toNat - 1 →
                  n = vecAt r i)) := by
    sorry

  /-- Under the preconditions, kth_palindrome(queries, intLength) returns a result r; it does not fail, panic, or overflow.
    Preconditions: len(queries) is between 1 and 50000 inclusive, for every i with 0 <= i < len(queries), 1 <= queries[i] <= 1000000000, and 1 <= intLength <= 15. -/
  theorem spec_2
      (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
      (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
      (hq : ∀ i, i < queries.val.length →
        1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
      (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15) :
      ∃ r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64,
        Aegis.KthPalindrome.kth_palindrome queries intLength = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
        (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
        (hq : ∀ i, i < queries.val.length →
          1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
        (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15), ∃ r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64,
          Aegis.KthPalindrome.kth_palindrome queries intLength = ok r) := by
    sorry

  /-- Whenever kth_palindrome(queries, intLength) returns a result r, len(r) = len(queries).
    Preconditions: len(queries) is between 1 and 50000 inclusive, for every i with 0 <= i < len(queries), 1 <= queries[i] <= 1000000000, and 1 <= intLength <= 15. -/
  theorem spec_3
      (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
      (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
      (hq : ∀ i, i < queries.val.length →
        1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
      (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
      (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
      (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r) :
      r.val.length = queries.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
        (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
        (hq : ∀ i, i < queries.val.length →
          1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
        (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
        (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
        (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r), r.val.length = queries.val.length) := by
    sorry

  /-- Whenever kth_palindrome(queries, intLength) returns a result r, for every i with 0 <= i < len(queries), if r[i] != -1 then 10^(intLength - 1) <= r[i] < 10^intLength.
    Preconditions: len(queries) is between 1 and 50000 inclusive, for every i with 0 <= i < len(queries), 1 <= queries[i] <= 1000000000, and 1 <= intLength <= 15. -/
  theorem spec_4
      (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
      (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
      (hq : ∀ i, i < queries.val.length →
        1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
      (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
      (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
      (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r) :
      r.val.length = queries.val.length ∧
        ∀ i, i < queries.val.length → vecAt r i ≠ -1 →
          (10 : ℤ) ^ (intLength.val.toNat - 1) ≤ vecAt r i ∧
            vecAt r i < (10 : ℤ) ^ intLength.val.toNat := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
        (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
        (hq : ∀ i, i < queries.val.length →
          1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
        (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
        (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
        (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r), r.val.length = queries.val.length ∧
          ∀ i, i < queries.val.length → vecAt r i ≠ -1 →
            (10 : ℤ) ^ (intLength.val.toNat - 1) ≤ vecAt r i ∧
              vecAt r i < (10 : ℤ) ^ intLength.val.toNat) := by
    sorry

  /-- Whenever kth_palindrome(queries, intLength) returns a result r, for every i with 0 <= i < len(queries), if r[i] != -1 then r[i] is a palindrome: its base-10 digits read the same forwards and backwards.
    Preconditions: len(queries) is between 1 and 50000 inclusive, for every i with 0 <= i < len(queries), 1 <= queries[i] <= 1000000000, and 1 <= intLength <= 15. -/
  theorem spec_5
      (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
      (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
      (hq : ∀ i, i < queries.val.length →
        1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
      (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
      (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
      (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r) :
      r.val.length = queries.val.length ∧
        ∀ i, i < queries.val.length → vecAt r i ≠ -1 →
          IsDecimalPalindrome (vecAt r i) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
        (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
        (hq : ∀ i, i < queries.val.length →
          1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
        (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
        (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
        (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r), r.val.length = queries.val.length ∧
          ∀ i, i < queries.val.length → vecAt r i ≠ -1 →
            IsDecimalPalindrome (vecAt r i)) := by
    sorry

  /-- Whenever kth_palindrome(queries, intLength) returns a result r, for every i with 0 <= i < len(queries), r[i] = -1 if and only if queries[i] > C, where L = intLength and C = 9 * 10^(ceil(L/2) - 1).
    Preconditions: len(queries) is between 1 and 50000 inclusive, for every i with 0 <= i < len(queries), 1 <= queries[i] <= 1000000000, and 1 <= intLength <= 15. -/
  theorem spec_6
      (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
      (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
      (hq : ∀ i, i < queries.val.length →
        1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
      (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
      (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
      (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r) :
      r.val.length = queries.val.length ∧
        ∀ i, i < queries.val.length →
          (vecAt r i = -1 ↔ countBound intLength.val < sliceAt queries i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
        (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
        (hq : ∀ i, i < queries.val.length →
          1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
        (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
        (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
        (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r), r.val.length = queries.val.length ∧
          ∀ i, i < queries.val.length →
            (vecAt r i = -1 ↔ countBound intLength.val < sliceAt queries i)) := by
    sorry

  /-- Whenever kth_palindrome(queries, intLength) returns a result r, for every i with 0 <= i < len(queries), if r[i] != -1 then exactly queries[i] - 1 positive palindromes of length L are strictly less than r[i], where L = intLength.
    Preconditions: len(queries) is between 1 and 50000 inclusive, for every i with 0 <= i < len(queries), 1 <= queries[i] <= 1000000000, and 1 <= intLength <= 15. -/
  theorem spec_7
      (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
      (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
      (hq : ∀ i, i < queries.val.length →
        1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
      (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
      (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
      (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r) :
      r.val.length = queries.val.length ∧
        ∀ i, i < queries.val.length → vecAt r i ≠ -1 →
          countLDigitPalindromesBelow intLength.val.toNat (vecAt r i) =
            (sliceAt queries i).toNat - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
        (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
        (hq : ∀ i, i < queries.val.length →
          1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
        (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
        (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
        (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r), r.val.length = queries.val.length ∧
          ∀ i, i < queries.val.length → vecAt r i ≠ -1 →
            countLDigitPalindromesBelow intLength.val.toNat (vecAt r i) =
              (sliceAt queries i).toNat - 1) := by
    sorry

  /-- Whenever kth_palindrome(queries, intLength) returns a result r, for all i and j with 0 <= i < len(queries) and 0 <= j < len(queries), if queries[i] < queries[j] and r[j] != -1, then r[i] != -1 and r[i] < r[j].
    Preconditions: len(queries) is between 1 and 50000 inclusive, for every i with 0 <= i < len(queries), 1 <= queries[i] <= 1000000000, and 1 <= intLength <= 15. -/
  theorem spec_8
      (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
      (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
      (hq : ∀ i, i < queries.val.length →
        1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
      (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
      (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
      (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r) :
      r.val.length = queries.val.length ∧
        ∀ i j, i < queries.val.length → j < queries.val.length →
          sliceAt queries i < sliceAt queries j → vecAt r j ≠ -1 →
            vecAt r i ≠ -1 ∧ vecAt r i < vecAt r j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
        (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
        (hq : ∀ i, i < queries.val.length →
          1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
        (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
        (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
        (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r), r.val.length = queries.val.length ∧
          ∀ i j, i < queries.val.length → j < queries.val.length →
            sliceAt queries i < sliceAt queries j → vecAt r j ≠ -1 →
              vecAt r i ≠ -1 ∧ vecAt r i < vecAt r j) := by
    sorry

  /-- Whenever kth_palindrome(queries, intLength) returns a result r, for all i and j with 0 <= i < len(queries) and 0 <= j < len(queries), if queries[i] = queries[j] then r[i] = r[j].
    Preconditions: len(queries) is between 1 and 50000 inclusive, for every i with 0 <= i < len(queries), 1 <= queries[i] <= 1000000000, and 1 <= intLength <= 15. -/
  theorem spec_9
      (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
      (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
      (hq : ∀ i, i < queries.val.length →
        1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
      (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
      (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
      (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r) :
      r.val.length = queries.val.length ∧
        ∀ i j, i < queries.val.length → j < queries.val.length →
          sliceAt queries i = sliceAt queries j → vecAt r i = vecAt r j := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
        (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
        (hq : ∀ i, i < queries.val.length →
          1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
        (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
        (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
        (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r), r.val.length = queries.val.length ∧
          ∀ i j, i < queries.val.length → j < queries.val.length →
            sliceAt queries i = sliceAt queries j → vecAt r i = vecAt r j) := by
    sorry

  /-- Whenever kth_palindrome(queries, intLength) returns a result r, for all i and j with 0 <= i < len(queries) and 0 <= j < len(queries), if queries[i] != queries[j] and r[i] != -1 and r[j] != -1, then r[i] != r[j].
    Preconditions: len(queries) is between 1 and 50000 inclusive, for every i with 0 <= i < len(queries), 1 <= queries[i] <= 1000000000, and 1 <= intLength <= 15. -/
  theorem spec_10
      (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
      (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
      (hq : ∀ i, i < queries.val.length →
        1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
      (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
      (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
      (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r) :
      r.val.length = queries.val.length ∧
        ∀ i j, i < queries.val.length → j < queries.val.length →
          sliceAt queries i ≠ sliceAt queries j → vecAt r i ≠ -1 → vecAt r j ≠ -1 →
            vecAt r i ≠ vecAt r j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
        (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
        (hq : ∀ i, i < queries.val.length →
          1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
        (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
        (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
        (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r), r.val.length = queries.val.length ∧
          ∀ i j, i < queries.val.length → j < queries.val.length →
            sliceAt queries i ≠ sliceAt queries j → vecAt r i ≠ -1 → vecAt r j ≠ -1 →
              vecAt r i ≠ vecAt r j) := by
    sorry

  /-- Whenever kth_palindrome(queries, intLength) returns a result r, the number of indices i with 0 <= i < len(queries) and r[i] = -1 equals the number of indices i with 0 <= i < len(queries) and queries[i] > C, where C = 9 * 10^(ceil(intLength/2) - 1).
    Preconditions: len(queries) is between 1 and 50000 inclusive, for every i with 0 <= i < len(queries), 1 <= queries[i] <= 1000000000, and 1 <= intLength <= 15. -/
  theorem spec_11
      (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
      (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
      (hq : ∀ i, i < queries.val.length →
        1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
      (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
      (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
      (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r) :
      r.val.length = queries.val.length ∧
        r.val.countP (fun x => x.val == -1) =
          queries.val.countP (fun q => decide (countBound intLength.val < q.val)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (queries : Aeneas.Std.Slice Aeneas.Std.I64) (intLength : Aeneas.Std.I64)
        (hlen1 : 1 ≤ queries.val.length) (hlen2 : queries.val.length ≤ 50000)
        (hq : ∀ i, i < queries.val.length →
          1 ≤ sliceAt queries i ∧ sliceAt queries i ≤ 1000000000)
        (hL1 : 1 ≤ intLength.val) (hL2 : intLength.val ≤ 15)
        (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)
        (hr : Aegis.KthPalindrome.kth_palindrome queries intLength = ok r), r.val.length = queries.val.length ∧
          r.val.countP (fun x => x.val == -1) =
            queries.val.countP (fun q => decide (countBound intLength.val < q.val))) := by
    sorry

  end AegisSpec.KthPalindrome
