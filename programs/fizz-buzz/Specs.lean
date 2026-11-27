import Aegis.FizzBuzz.Code.Funs

/-!
# Specifications of `Aegis.FizzBuzz.fizz_buzz`

LeetCode problem `fizz-buzz`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FizzBuzz

abbrev ByteVec : Type := alloc.vec.Vec U8

abbrev ByteVecVec : Type := alloc.vec.Vec ByteVec

def bytesOf (v : ByteVec) : List ℕ := v.val.map (fun b => b.val)

def rowsOf (r : ByteVecVec) : List (List ℕ) := r.val.map bytesOf

def row? (r : ByteVecVec) (j : ℕ) : Option (List ℕ) := (rowsOf r)[j]?

def rowLen (r : ByteVecVec) (j : ℕ) : ℕ := ((row? r j).map List.length).getD 0

def asciiFizzBuzz : List ℕ := [70, 105, 122, 122, 66, 117, 122, 122]

def asciiFizz : List ℕ := [70, 105, 122, 122]

def asciiBuzz : List ℕ := [66, 117, 122, 122]

def asciiOne : List ℕ := [49]

def decDigits (k : ℕ) : List ℕ :=
  if h : k < 10 then [48 + k]
  else decDigits (k / 10) ++ [48 + k % 10]
termination_by k
decreasing_by
  exact Nat.div_lt_self
    (Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 10) (Nat.le_of_not_gt h))
    (by decide : (1 : ℕ) < 10)

def expectedRow (i : ℕ) : List ℕ :=
  if 15 ∣ i then asciiFizzBuzz
  else if 3 ∣ i then asciiFizz
  else if 5 ∣ i then asciiBuzz
  else decDigits i

def IsDigitSeq (l : List ℕ) : Prop := l ≠ [] ∧ ∀ b ∈ l, 48 ≤ b ∧ b ≤ 57

def NoLeadingZero (l : List ℕ) : Prop := l.head? ≠ some 48

def digitsVal (l : List ℕ) : ℕ := l.foldl (fun acc b => acc * 10 + (b - 48)) 0

def allowedBytes : List ℕ :=
  [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 66, 70, 105, 117, 122]

/-- fizz_buzz n returns a result r and does not fail. The vector r has len(r) = n. For every 0-based index j with 0 <= j < n, let i = j + 1. Then r[j] is exactly: the 8-byte ASCII text 'FizzBuzz' [70,105,122,122,66,117,122,122] if i is divisible by both 3 and 5; the 4-byte ASCII text 'Fizz' [70,105,122,122] if i is divisible by 3 but not by 5; the 4-byte ASCII text 'Buzz' [66,117,122,122] if i is divisible by 5 but not by 3; otherwise the ASCII decimal representation of i (no leading zeros).
  Preconditions: n is an integer with 1 <= n <= 10^4. The Lean parameter is Std.I64, and this range is representable in I64. -/
theorem spec_1 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∃ r, Aegis.FizzBuzz.fizz_buzz n = ok r ∧
      r.val.length = n.val.toNat ∧
      ∀ j, j < n.val.toNat → row? r j = some (expectedRow (j + 1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∃ r, Aegis.FizzBuzz.fizz_buzz n = ok r ∧
      r.val.length = n.val.toNat ∧
      ∀ j, j < n.val.toNat → row? r j = some (expectedRow (j + 1))) := by
  sorry

/-- Whenever fizz_buzz n returns a result r, the length of r is n: len(r) = n.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_2 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r → r.val.length = n.val.toNat := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r → r.val.length = n.val.toNat) := by
  sorry

/-- Whenever fizz_buzz n returns a result r, for every index j with 0 <= j < n, let i = j + 1. If i is divisible by 15 (i.e. by both 3 and 5) then len(r[j]) = 8. If i is divisible by exactly one of 3 and 5 then len(r[j]) = 4. If i is divisible by neither 3 nor 5 then len(r[j]) equals the number of decimal digits of i; since i <= 10^4 and 10^4 = 10000 is itself divisible by 5, such i is at most 9999, so 1 <= len(r[j]) <= 4.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_3 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat →
        (15 ∣ (j + 1) → rowLen r j = 8) ∧
        (((3 ∣ (j + 1) ∧ ¬ 5 ∣ (j + 1)) ∨ (5 ∣ (j + 1) ∧ ¬ 3 ∣ (j + 1))) →
          rowLen r j = 4) ∧
        (¬ 3 ∣ (j + 1) → ¬ 5 ∣ (j + 1) →
          rowLen r j = (decDigits (j + 1)).length ∧
          1 ≤ rowLen r j ∧ rowLen r j ≤ 4) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat →
        (15 ∣ (j + 1) → rowLen r j = 8) ∧
        (((3 ∣ (j + 1) ∧ ¬ 5 ∣ (j + 1)) ∨ (5 ∣ (j + 1) ∧ ¬ 3 ∣ (j + 1))) →
          rowLen r j = 4) ∧
        (¬ 3 ∣ (j + 1) → ¬ 5 ∣ (j + 1) →
          rowLen r j = (decDigits (j + 1)).length ∧
          1 ≤ rowLen r j ∧ rowLen r j ≤ 4)) := by
  sorry

/-- Whenever fizz_buzz n returns a result r, for every index j with 0 <= j < n such that i = j + 1 is divisible by 15, r[j] is the ASCII byte sequence [70,105,122,122,66,117,122,122], i.e. the text 'FizzBuzz'.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_4 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → 15 ∣ (j + 1) → row? r j = some asciiFizzBuzz := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → 15 ∣ (j + 1) → row? r j = some asciiFizzBuzz) := by
  sorry

/-- Whenever fizz_buzz n returns a result r, for every index j with 0 <= j < n such that i = j + 1 is divisible by 3 and not divisible by 5, r[j] is the ASCII byte sequence [70,105,122,122], i.e. the text 'Fizz'.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_5 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → 3 ∣ (j + 1) → ¬ 5 ∣ (j + 1) →
        row? r j = some asciiFizz := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → 3 ∣ (j + 1) → ¬ 5 ∣ (j + 1) →
        row? r j = some asciiFizz) := by
  sorry

/-- Whenever fizz_buzz n returns a result r, for every index j with 0 <= j < n such that i = j + 1 is divisible by 5 and not divisible by 3, r[j] is the ASCII byte sequence [66,117,122,122], i.e. the text 'Buzz'.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_6 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → 5 ∣ (j + 1) → ¬ 3 ∣ (j + 1) →
        row? r j = some asciiBuzz := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → 5 ∣ (j + 1) → ¬ 3 ∣ (j + 1) →
        row? r j = some asciiBuzz) := by
  sorry

/-- Whenever fizz_buzz n returns a result r, for every index j with 0 <= j < n such that i = j + 1 is divisible by neither 3 nor 5, r[j] is the unique nonempty ASCII digit sequence (bytes 48 through 57) whose decimal numerical value is i and which has no leading zero.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_7 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → ¬ 3 ∣ (j + 1) → ¬ 5 ∣ (j + 1) →
        ∃ l, row? r j = some l ∧ IsDigitSeq l ∧ NoLeadingZero l ∧ digitsVal l = j + 1 ∧
          ∀ m, IsDigitSeq m → NoLeadingZero m → digitsVal m = j + 1 → m = l := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → ¬ 3 ∣ (j + 1) → ¬ 5 ∣ (j + 1) →
        ∃ l, row? r j = some l ∧ IsDigitSeq l ∧ NoLeadingZero l ∧ digitsVal l = j + 1 ∧
          ∀ m, IsDigitSeq m → NoLeadingZero m → digitsVal m = j + 1 → m = l) := by
  sorry

/-- For every n satisfying the precondition, fizz_buzz n returns a result r; it does not fail (no overflow, out-of-bounds, panic, or error result occurs).
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_8 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∃ r, Aegis.FizzBuzz.fizz_buzz n = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∃ r, Aegis.FizzBuzz.fizz_buzz n = ok r) := by
  sorry

/-- Whenever fizz_buzz n returns a result r, the first entry r[0] is the ASCII byte sequence [49], i.e. the text '1'.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_9 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r → row? r 0 = some asciiOne := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r → row? r 0 = some asciiOne) := by
  sorry

/-- Whenever fizz_buzz n returns a result r, the last entry r[n-1] is determined by n as follows: it is ASCII 'FizzBuzz' [70,105,122,122,66,117,122,122] if n is divisible by 15; it is ASCII 'Fizz' [70,105,122,122] if n is divisible by 3 but not 5; it is ASCII 'Buzz' [66,117,122,122] if n is divisible by 5 but not 3; otherwise it is the ASCII decimal representation of n with no leading zeros.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_10 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      row? r (n.val.toNat - 1) = some (expectedRow n.val.toNat) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      row? r (n.val.toNat - 1) = some (expectedRow n.val.toNat)) := by
  sorry

/-- If fizz_buzz n1 returns r1 and fizz_buzz n2 returns r2, then len(r1) = n1, len(r2) = n2, and for every index j with 0 <= j < n1, r1[j] = r2[j]. Equivalently, r1 is a prefix of r2.
  Preconditions: n1 and n2 are integers with 1 <= n1 <= n2 <= 10^4. -/
theorem spec_11 (n1 n2 : I64) (h1 : 1 ≤ n1.val) (h2 : n1.val ≤ n2.val)
    (h3 : n2.val ≤ 10000) :
    ∀ r1 r2, Aegis.FizzBuzz.fizz_buzz n1 = ok r1 →
      Aegis.FizzBuzz.fizz_buzz n2 = ok r2 →
      r1.val.length = n1.val.toNat ∧ r2.val.length = n2.val.toNat ∧
      (∀ j, j < n1.val.toNat → row? r1 j = row? r2 j) ∧
      List.IsPrefix (rowsOf r1) (rowsOf r2) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n1 n2 : I64) (h1 : 1 ≤ n1.val) (h2 : n1.val ≤ n2.val)
    (h3 : n2.val ≤ 10000), ∀ r1 r2, Aegis.FizzBuzz.fizz_buzz n1 = ok r1 →
      Aegis.FizzBuzz.fizz_buzz n2 = ok r2 →
      r1.val.length = n1.val.toNat ∧ r2.val.length = n2.val.toNat ∧
      (∀ j, j < n1.val.toNat → row? r1 j = row? r2 j) ∧
      List.IsPrefix (rowsOf r1) (rowsOf r2)) := by
  sorry

/-- Whenever fizz_buzz n returns a result r, for every index j with 0 <= j < n and every position k with 0 <= k < len(r[j]), the byte r[j][k] belongs to the ASCII set of digits '0' through '9' or to one of the letters occurring in 'FizzBuzz'; explicitly, r[j][k] is one of 48,49,50,51,52,53,54,55,56,57,66,70,105,117,122.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_12 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → ∀ l, row? r j = some l → ∀ b ∈ l, b ∈ allowedBytes := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → ∀ l, row? r j = some l → ∀ b ∈ l, b ∈ allowedBytes) := by
  sorry

/-- Whenever fizz_buzz n returns a result r, for every index j with 0 <= j < n such that i = j + 1 is divisible by neither 3 nor 5, the byte array r[j] is nonempty and its first byte is not 48, the ASCII code of '0'.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_13 (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → ¬ 3 ∣ (j + 1) → ¬ 5 ∣ (j + 1) →
        ∀ l, row? r j = some l → l ≠ [] ∧ l.head? ≠ some 48 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.FizzBuzz.fizz_buzz n = ok r →
      ∀ j, j < n.val.toNat → ¬ 3 ∣ (j + 1) → ¬ 5 ∣ (j + 1) →
        ∀ l, row? r j = some l → l ≠ [] ∧ l.head? ≠ some 48) := by
  sorry

end AegisSpec.FizzBuzz
