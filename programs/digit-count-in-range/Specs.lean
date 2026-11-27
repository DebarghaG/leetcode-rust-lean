import Aegis.DigitsCount.Code.Funs

/-!
# Specifications of `Aegis.DigitsCount.digits_count`

LeetCode problem `digit-count-in-range`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.DigitsCount (digits_count)

namespace AegisSpec.DigitsCount

def digitsRevAux : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else n % 10 :: digitsRevAux fuel (n / 10)

def digitsRev (n : Nat) : List Nat := digitsRevAux (n + 1) n

def decimalDigits (n : Nat) : List Nat :=
  if n = 0 then [0] else (digitsRev n).reverse

def numDigits (n : Nat) : Nat := (decimalDigits n).length

def digitAt (n k : Nat) : Nat := (decimalDigits n).getD k 0

def digitOcc (n d : Nat) : Nat :=
  ((Finset.range (numDigits n)).filter (fun k => digitAt n k = d)).card

def i64OfNat (n : Nat) : Std.I64 := ⟨BitVec.ofNat 64 n⟩

/-- The function returns a result r and r equals the sum over all integers n with low <= n <= high of occ(n,d), where for each n >= 1, occ(n,d) is the number of positions k with 0 <= k < L(n) such that the k-th digit from the left in the ordinary decimal representation of n (no leading zeros) equals the decimal digit d (ASCII code 48+d), and L(n) is the number of digits of n. A digit that appears several times in the same n is counted several times.
  Preconditions: 0 <= d <= 9 and 1 <= low <= high <= 200000000 (that is, 2*10^8). -/
theorem spec_1 (d low high : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000) :
    ∃ r : Std.I64, digits_count d low high = .ok r ∧
      r.val = ∑ n ∈ Finset.Icc low.val.toNat high.val.toNat,
        (digitOcc n d.val.toNat : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (d low high : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000), ∃ r : Std.I64, digits_count d low high = Result.ok r ∧
      r.val = ∑ n ∈ Finset.Icc low.val.toNat high.val.toNat,
        (digitOcc n d.val.toNat : ℤ)) := by
  sorry

/-- Whenever digits_count(d, low, high) returns a result r, we have 0 <= r.
  Preconditions: 0 <= d <= 9 and 1 <= low <= high <= 200000000. -/
theorem spec_2 (d low high r : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : digits_count d low high = .ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (d low high r : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : digits_count d low high = Result.ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever digits_count(d, low, high) returns a result r, we have r <= 9 * (high - low + 1).
  Preconditions: 0 <= d <= 9 and 1 <= low <= high <= 200000000. -/
theorem spec_3 (d low high r : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : digits_count d low high = .ok r) :
    r.val ≤ 9 * (high.val - low.val + 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (d low high r : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : digits_count d low high = Result.ok r), r.val ≤ 9 * (high.val - low.val + 1)) := by
  sorry

/-- For every d, low, and high satisfying the preconditions, digits_count(d, low, high) returns a result r; it does not fail, panic, or overflow.
  Preconditions: 0 <= d <= 9 and 1 <= low <= high <= 200000000. -/
theorem spec_4 (d low high : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000) :
    ∃ r : Std.I64, digits_count d low high = .ok r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (d low high : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000), ∃ r : Std.I64, digits_count d low high = Result.ok r) := by
  sorry

/-- Whenever digits_count(d, low, high) returns r, digits_count(d, low, m) returns r1, and digits_count(d, m+1, high) returns r2, we have r = r1 + r2.
  Preconditions: 0 <= d <= 9 and 1 <= low <= m < high <= 200000000. -/
theorem spec_5 (d low m high mp r r1 r2 : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hlm : low.val ≤ m.val) (hmh : m.val < high.val)
    (hhigh : high.val ≤ 200000000)
    (hmp : mp.val = m.val + 1)
    (h : digits_count d low high = .ok r)
    (h1 : digits_count d low m = .ok r1)
    (h2 : digits_count d mp high = .ok r2) :
    r.val = r1.val + r2.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (d low m high mp r r1 r2 : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hlm : low.val ≤ m.val) (hmh : m.val < high.val)
    (hhigh : high.val ≤ 200000000)
    (hmp : mp.val = m.val + 1)
    (h : digits_count d low high = Result.ok r)
    (h1 : digits_count d low m = Result.ok r1)
    (h2 : digits_count d mp high = Result.ok r2), r.val = r1.val + r2.val) := by
  sorry

/-- Whenever digits_count(d, low, high1) returns r1 and digits_count(d, low, high2) returns r2, we have r1 <= r2.
  Preconditions: 0 <= d <= 9 and 1 <= low <= high1 <= high2 <= 200000000. -/
theorem spec_6 (d low high1 high2 r1 r2 : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (h1le : low.val ≤ high1.val) (h12 : high1.val ≤ high2.val)
    (hhigh : high2.val ≤ 200000000)
    (h1 : digits_count d low high1 = .ok r1)
    (h2 : digits_count d low high2 = .ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (d low high1 high2 r1 r2 : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (h1le : low.val ≤ high1.val) (h12 : high1.val ≤ high2.val)
    (hhigh : high2.val ≤ 200000000)
    (h1 : digits_count d low high1 = Result.ok r1)
    (h2 : digits_count d low high2 = Result.ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Whenever digits_count(d, low1, high) returns r1 and digits_count(d, low2, high) returns r2, we have r2 <= r1.
  Preconditions: 0 <= d <= 9 and 1 <= low1 <= low2 <= high <= 200000000. -/
theorem spec_7 (d low1 low2 high r1 r2 : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low1.val) (h12 : low1.val ≤ low2.val) (h2le : low2.val ≤ high.val)
    (hhigh : high.val ≤ 200000000)
    (h1 : digits_count d low1 high = .ok r1)
    (h2 : digits_count d low2 high = .ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (d low1 low2 high r1 r2 : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low1.val) (h12 : low1.val ≤ low2.val) (h2le : low2.val ≤ high.val)
    (hhigh : high.val ≤ 200000000)
    (h1 : digits_count d low1 high = Result.ok r1)
    (h2 : digits_count d low2 high = Result.ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Whenever digits_count(d, low, high) returns a result r, r = 0 if and only if no integer n with low <= n <= high has the digit d in its ordinary decimal representation (no leading zeros).
  Preconditions: 0 <= d <= 9 and 1 <= low <= high <= 200000000. -/
theorem spec_8 (d low high r : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : digits_count d low high = .ok r) :
    (r.val = 0 ↔
      ∀ n : Nat, low.val.toNat ≤ n → n ≤ high.val.toNat →
        d.val.toNat ∉ decimalDigits n) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (d low high r : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : digits_count d low high = Result.ok r), (r.val = 0 ↔
      ∀ n : Nat, low.val.toNat ≤ n → n ≤ high.val.toNat →
        d.val.toNat ∉ decimalDigits n)) := by
  sorry

/-- Whenever digits_count(d, low, high) returns a result r with r >= 2, at least one of the following holds: (a) there is an n with low <= n <= high whose ordinary decimal representation (no leading zeros) contains d at least twice; or (b) there are integers n1 and n2 with low <= n1 < n2 <= high such that each of the ordinary decimal representations of n1 and n2 contains d at least once.
  Preconditions: 0 <= d <= 9 and 1 <= low <= high <= 200000000. -/
theorem spec_9 (d low high r : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : digits_count d low high = .ok r) (hr : 2 ≤ r.val) :
    (∃ n : Nat, low.val.toNat ≤ n ∧ n ≤ high.val.toNat ∧
      2 ≤ digitOcc n d.val.toNat) ∨
    (∃ n1 n2 : Nat, low.val.toNat ≤ n1 ∧ n1 < n2 ∧ n2 ≤ high.val.toNat ∧
      1 ≤ digitOcc n1 d.val.toNat ∧ 1 ≤ digitOcc n2 d.val.toNat) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (d low high r : Std.I64)
    (hd0 : 0 ≤ d.val) (hd9 : d.val ≤ 9)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : digits_count d low high = Result.ok r) (hr : 2 ≤ r.val), (∃ n : Nat, low.val.toNat ≤ n ∧ n ≤ high.val.toNat ∧
      2 ≤ digitOcc n d.val.toNat) ∨
    (∃ n1 n2 : Nat, low.val.toNat ≤ n1 ∧ n1 < n2 ∧ n2 ≤ high.val.toNat ∧
      1 ≤ digitOcc n1 d.val.toNat ∧ 1 ≤ digitOcc n2 d.val.toNat)) := by
  sorry

/-- Whenever digits_count(0, low, high) returns a result r, we have r <= 8 * (high - low + 1).
  Preconditions: d = 0 and 1 <= low <= high <= 200000000. -/
theorem spec_10 (low high r : Std.I64)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : digits_count 0#i64 low high = .ok r) :
    r.val ≤ 8 * (high.val - low.val + 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (low high r : Std.I64)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : digits_count 0#i64 low high = Result.ok r), r.val ≤ 8 * (high.val - low.val + 1)) := by
  sorry

/-- Whenever for each digit e with 0 <= e <= 9 the call digits_count(e, low, high) returns a result r_e, we have sum_{e=0}^{9} r_e = sum_{n=low}^{high} L(n), where L(n) is the number of digits in the ordinary decimal representation of n with no leading zeros.
  Preconditions: 1 <= low <= high <= 200000000. -/
theorem spec_11 (low high : Std.I64) (r : Nat → Std.I64)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : ∀ e : Nat, e ≤ 9 → digits_count (i64OfNat e) low high = .ok (r e)) :
    (∑ e ∈ Finset.range 10, (r e).val) =
      ∑ n ∈ Finset.Icc low.val.toNat high.val.toNat, (numDigits n : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (low high : Std.I64) (r : Nat → Std.I64)
    (hlow : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhigh : high.val ≤ 200000000)
    (h : ∀ e : Nat, e ≤ 9 → digits_count (i64OfNat e) low high = Result.ok (r e)), (∑ e ∈ Finset.range 10, (r e).val) =
      ∑ n ∈ Finset.Icc low.val.toNat high.val.toNat, (numDigits n : ℤ)) := by
  sorry

end AegisSpec.DigitsCount
