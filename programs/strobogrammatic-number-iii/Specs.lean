import Aegis.StrobogrammaticInRange.Code.Funs

/-!
# Specifications of `Aegis.StrobogrammaticInRange.strobogrammatic_in_range`

LeetCode problem `strobogrammatic-number-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open Aegis.StrobogrammaticInRange

namespace AegisSpec.StrobogrammaticInRange

def byteDigit (b : U8) : Int := (b.val : Int) - 48

def value (s : Slice U8) : Int :=
  (s.val.mapIdx (fun i b => byteDigit b * 10 ^ (s.val.length - 1 - i))).sum

abbrev IsDigitByte (b : U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

abbrev IsDigitString (l : List U8) : Prop := ∀ b ∈ l, IsDigitByte b

abbrev NoLeadingZero (s : Slice U8) : Prop :=
  ∀ (b : U8) (rest : List U8), s.val = b :: rest → b.val ≠ 48 ∨ rest = []

abbrev ValidInput (s : Slice U8) : Prop :=
  1 ≤ s.val.length ∧ s.val.length ≤ 15 ∧ IsDigitString s.val ∧ NoLeadingZero s

abbrev IsCanonicalDec (s : Slice U8) (n : Int) : Prop := ValidInput s ∧ value s = n

def digitsOf : Nat → List Nat
  | n => if n < 10 then [n] else digitsOf (n / 10) ++ [n % 10]
termination_by n => n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def digitsAscii (n : Nat) : List Nat := (digitsOf n).map (fun d => d + 48)

def rotByte (c : Nat) : Nat :=
  if c = 48 then 48
  else if c = 49 then 49
  else if c = 54 then 57
  else if c = 56 then 56
  else if c = 57 then 54
  else 0

abbrev IsStrob (n : Nat) : Prop :=
  (∀ c ∈ digitsAscii n, c ∈ [48, 49, 54, 56, 57]) ∧
    (digitsAscii n).reverse.map rotByte = digitsAscii n

abbrev IsStrobInt (z : Int) : Prop := 0 ≤ z ∧ IsStrob z.toNat

def strobCount (lo hi : Int) : Nat :=
  (Finset.filter (fun k : Nat => IsStrobInt (lo + (k : Int)))
      (Finset.range (hi - lo + 1).toNat)).card

def strobCountSmall (lo hi : Int) : Nat :=
  (Finset.filter (fun d : Int => lo ≤ d ∧ d ≤ hi) ({0, 1, 8} : Finset Int)).card

/-- Whenever the function returns a result r, r = |{ n in Z : value(low) <= n <= value(high) and n is strobogrammatic }|, i.e. r is exactly the number of strobogrammatic integers in the inclusive interval from value(low) to value(high).
  Preconditions: len(low) and len(high) are between 1 and 15 inclusive. Every byte of low and high is an ASCII decimal digit code (48 through 57). low has no leading zero unless low is the one-byte string '0', and high has no leading zero unless high is the one-byte string '0'. value(low) <= value(high), where value(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). A nonnegative integer n is strobogrammatic iff, letting s be its ordinary decimal representation with no leading zeros (s='0' for n=0), every byte of s is in {48,49,54,56,57} and for every i with 0 <= i < len(s), s[len(s)-1-i] equals rot(s[i]), where rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54. -/
theorem spec_1 (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hres : strobogrammatic_in_range low high = Result.ok r) :
    r.val = (strobCount (value low) (value high) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hres : strobogrammatic_in_range low high = Result.ok r), r.val = (strobCount (value low) (value high) : Int)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or signal arithmetic overflow) for every low and high satisfying the preconditions.
  Preconditions: len(low) and len(high) are between 1 and 15 inclusive. Every byte of low and high is an ASCII decimal digit code (48 through 57). low has no leading zero unless low is the one-byte string '0', and high has no leading zero unless high is the one-byte string '0'. value(low) <= value(high), where value(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_2 (low high : Slice U8)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high) :
    ∃ r : I64, strobogrammatic_in_range low high = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (low high : Slice U8)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high), ∃ r : I64, strobogrammatic_in_range low high = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: len(low) and len(high) are between 1 and 15 inclusive. Every byte of low and high is an ASCII decimal digit code (48 through 57). low has no leading zero unless low is the one-byte string '0', and high has no leading zero unless high is the one-byte string '0'. value(low) <= value(high), where value(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). A nonnegative integer n is strobogrammatic iff, letting s be its ordinary decimal representation with no leading zeros (s='0' for n=0), every byte of s is in {48,49,54,56,57} and for every i with 0 <= i < len(s), s[len(s)-1-i] equals rot(s[i]), where rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54. -/
theorem spec_3 (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hres : strobogrammatic_in_range low high = Result.ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hres : strobogrammatic_in_range low high = Result.ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= value(high) - value(low) + 1.
  Preconditions: len(low) and len(high) are between 1 and 15 inclusive. Every byte of low and high is an ASCII decimal digit code (48 through 57). low has no leading zero unless low is the one-byte string '0', and high has no leading zero unless high is the one-byte string '0'. value(low) <= value(high), where value(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). A nonnegative integer n is strobogrammatic iff, letting s be its ordinary decimal representation with no leading zeros (s='0' for n=0), every byte of s is in {48,49,54,56,57} and for every i with 0 <= i < len(s), s[len(s)-1-i] equals rot(s[i]), where rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54. -/
theorem spec_4 (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hres : strobogrammatic_in_range low high = Result.ok r) :
    r.val ≤ value high - value low + 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hres : strobogrammatic_in_range low high = Result.ok r), r.val ≤ value high - value low + 1) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is no integer n such that value(low) <= n <= value(high) and n is strobogrammatic.
  Preconditions: len(low) and len(high) are between 1 and 15 inclusive. Every byte of low and high is an ASCII decimal digit code (48 through 57). low has no leading zero unless low is the one-byte string '0', and high has no leading zero unless high is the one-byte string '0'. value(low) <= value(high), where value(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). A nonnegative integer n is strobogrammatic iff, letting s be its ordinary decimal representation with no leading zeros (s='0' for n=0), every byte of s is in {48,49,54,56,57} and for every i with 0 <= i < len(s), s[len(s)-1-i] equals rot(s[i]), where rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54. -/
theorem spec_5 (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hres : strobogrammatic_in_range low high = Result.ok r) :
    (r.val = 0) ↔ ¬ ∃ n : Int, value low ≤ n ∧ n ≤ value high ∧ IsStrobInt n := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hres : strobogrammatic_in_range low high = Result.ok r), (r.val = 0) ↔ ¬ ∃ n : Int, value low ≤ n ∧ n ≤ value high ∧ IsStrobInt n) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if value(low) is strobogrammatic, and r = 0 otherwise.
  Preconditions: len(low) and len(high) are between 1 and 15 inclusive. Every byte of low and high is an ASCII decimal digit code (48 through 57). low has no leading zero unless low is the one-byte string '0', and high has no leading zero unless high is the one-byte string '0'. value(low) = value(high), where value(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). A nonnegative integer n is strobogrammatic iff, letting s be its ordinary decimal representation with no leading zeros (s='0' for n=0), every byte of s is in {48,49,54,56,57} and for every i with 0 <= i < len(s), s[len(s)-1-i] equals rot(s[i]), where rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54. -/
theorem spec_6 (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (hsame : value low = value high)
    (hres : strobogrammatic_in_range low high = Result.ok r) :
    r.val = (if IsStrob (value low).toNat then 1 else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (hsame : value low = value high)
    (hres : strobogrammatic_in_range low high = Result.ok r), r.val = (if IsStrob (value low).toNat then 1 else 0)) := by
  sorry

/-- Whenever the function returns a result r, r = |{ d in {0,1,8} : value(low) <= d <= value(high) }|.
  Preconditions: len(low) and len(high) are between 1 and 15 inclusive. Every byte of low and high is an ASCII decimal digit code (48 through 57). low has no leading zero unless low is the one-byte string '0', and high has no leading zero unless high is the one-byte string '0'. value(low) <= value(high), and value(high) <= 9, where value(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_7 (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high) (hsmall : value high ≤ 9)
    (hres : strobogrammatic_in_range low high = Result.ok r) :
    r.val = (strobCountSmall (value low) (value high) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high) (hsmall : value high ≤ 9)
    (hres : strobogrammatic_in_range low high = Result.ok r), r.val = (strobCountSmall (value low) (value high) : Int)) := by
  sorry

/-- Whenever strobogrammatic_in_range(low, high1) returns r1 and strobogrammatic_in_range(low, high2) returns r2, r1 <= r2.
  Preconditions: low, high1, and high2 are byte strings satisfying the input constraints for their respective positions: len(low), len(high1), len(high2) are between 1 and 15 inclusive, all bytes are ASCII decimal digit codes (48 through 57), no leading zeros except for the one-byte string '0', and value(low) <= value(high1) <= value(high2), where value(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). A nonnegative integer n is strobogrammatic iff, letting s be its ordinary decimal representation with no leading zeros (s='0' for n=0), every byte of s is in {48,49,54,56,57} and for every i with 0 <= i < len(s), s[len(s)-1-i] equals rot(s[i]), where rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54. -/
theorem spec_8 (low high1 high2 : Slice U8) (r1 r2 : I64)
    (hlow : ValidInput low) (hh1 : ValidInput high1) (hh2 : ValidInput high2)
    (horder1 : value low ≤ value high1) (horder2 : value high1 ≤ value high2)
    (hres1 : strobogrammatic_in_range low high1 = Result.ok r1)
    (hres2 : strobogrammatic_in_range low high2 = Result.ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (low high1 high2 : Slice U8) (r1 r2 : I64)
    (hlow : ValidInput low) (hh1 : ValidInput high1) (hh2 : ValidInput high2)
    (horder1 : value low ≤ value high1) (horder2 : value high1 ≤ value high2)
    (hres1 : strobogrammatic_in_range low high1 = Result.ok r1)
    (hres2 : strobogrammatic_in_range low high2 = Result.ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Whenever strobogrammatic_in_range(low1, high) returns r1 and strobogrammatic_in_range(low2, high) returns r2, r2 <= r1.
  Preconditions: low1, low2, and high are byte strings satisfying the input constraints for their respective positions: len(low1), len(low2), len(high) are between 1 and 15 inclusive, all bytes are ASCII decimal digit codes (48 through 57), no leading zeros except for the one-byte string '0', and value(low1) <= value(low2) <= value(high), where value(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). A nonnegative integer n is strobogrammatic iff, letting s be its ordinary decimal representation with no leading zeros (s='0' for n=0), every byte of s is in {48,49,54,56,57} and for every i with 0 <= i < len(s), s[len(s)-1-i] equals rot(s[i]), where rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54. -/
theorem spec_9 (low1 low2 high : Slice U8) (r1 r2 : I64)
    (hl1 : ValidInput low1) (hl2 : ValidInput low2) (hhigh : ValidInput high)
    (horder1 : value low1 ≤ value low2) (horder2 : value low2 ≤ value high)
    (hres1 : strobogrammatic_in_range low1 high = Result.ok r1)
    (hres2 : strobogrammatic_in_range low2 high = Result.ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (low1 low2 high : Slice U8) (r1 r2 : I64)
    (hl1 : ValidInput low1) (hl2 : ValidInput low2) (hhigh : ValidInput high)
    (horder1 : value low1 ≤ value low2) (horder2 : value low2 ≤ value high)
    (hres1 : strobogrammatic_in_range low1 high = Result.ok r1)
    (hres2 : strobogrammatic_in_range low2 high = Result.ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Whenever strobogrammatic_in_range(low, a) returns r1, strobogrammatic_in_range(b, high) returns r2, and strobogrammatic_in_range(low, high) returns r, we have r = r1 + r2.
  Preconditions: low and high satisfy the input constraints: len(low), len(high) are between 1 and 15 inclusive, all bytes are ASCII decimal digit codes (48 through 57), no leading zeros except for the one-byte string '0', and value(low) <= value(high), where value(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). Let m be an integer with value(low) <= m < value(high), and let a and b be the canonical decimal byte strings representing m and m+1 respectively (no leading zeros, with a='0' when m=0). A nonnegative integer n is strobogrammatic iff, letting s be its ordinary decimal representation with no leading zeros (s='0' for n=0), every byte of s is in {48,49,54,56,57} and for every i with 0 <= i < len(s), s[len(s)-1-i] equals rot(s[i]), where rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54. -/
theorem spec_10 (low high a b : Slice U8) (r r1 r2 : I64) (m : Int)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hm_low : value low ≤ m) (hm_high : m < value high)
    (ha : IsCanonicalDec a m) (hb : IsCanonicalDec b (m + 1))
    (hres1 : strobogrammatic_in_range low a = Result.ok r1)
    (hres2 : strobogrammatic_in_range b high = Result.ok r2)
    (hres : strobogrammatic_in_range low high = Result.ok r) :
    r.val = r1.val + r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (low high a b : Slice U8) (r r1 r2 : I64) (m : Int)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hm_low : value low ≤ m) (hm_high : m < value high)
    (ha : IsCanonicalDec a m) (hb : IsCanonicalDec b (m + 1))
    (hres1 : strobogrammatic_in_range low a = Result.ok r1)
    (hres2 : strobogrammatic_in_range b high = Result.ok r2)
    (hres : strobogrammatic_in_range low high = Result.ok r), r.val = r1.val + r2.val) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exists an integer n such that value(low) <= n <= value(high) and n is strobogrammatic.
  Preconditions: len(low) and len(high) are between 1 and 15 inclusive. Every byte of low and high is an ASCII decimal digit code (48 through 57). low has no leading zero unless low is the one-byte string '0', and high has no leading zero unless high is the one-byte string '0'. value(low) <= value(high), where value(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). A nonnegative integer n is strobogrammatic iff, letting s be its ordinary decimal representation with no leading zeros (s='0' for n=0), every byte of s is in {48,49,54,56,57} and for every i with 0 <= i < len(s), s[len(s)-1-i] equals rot(s[i]), where rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54. -/
theorem spec_11 (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hres : strobogrammatic_in_range low high = Result.ok r)
    (hpos : 0 < r.val) :
    ∃ n : Int, value low ≤ n ∧ n ≤ value high ∧ IsStrobInt n := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (low high : Slice U8) (r : I64)
    (hlow : ValidInput low) (hhigh : ValidInput high)
    (horder : value low ≤ value high)
    (hres : strobogrammatic_in_range low high = Result.ok r)
    (hpos : 0 < r.val), ∃ n : Int, value low ≤ n ∧ n ≤ value high ∧ IsStrobInt n) := by
  sorry

end AegisSpec.StrobogrammaticInRange
