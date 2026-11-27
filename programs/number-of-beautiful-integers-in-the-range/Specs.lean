import Aegis.NumberOfBeautifulIntegers.Code.Funs

/-!
# Specifications of `Aegis.NumberOfBeautifulIntegers.number_of_beautiful_integers`

LeetCode problem `number-of-beautiful-integers-in-the-range`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfBeautifulIntegers

  open Aegis.NumberOfBeautifulIntegers (number_of_beautiful_integers)

  def decimalDigitsRev (n : Nat) : List Nat :=
    if h : n = 0 then [] else n % 10 :: decimalDigitsRev (n / 10)
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

  def decimalDigits (n : Nat) : List Nat :=
    if n = 0 then [0] else decimalDigitsRev n

  def evenDigitCount (n : Nat) : Nat :=
    (decimalDigits n).countP (fun d => d % 2 == 0)

  def oddDigitCount (n : Nat) : Nat :=
    (decimalDigits n).countP (fun d => d % 2 == 1)

  def IsBeautiful (k n : Nat) : Prop :=
    evenDigitCount n = oddDigitCount n ∧ k ∣ n

  def EvenNumberOfDigits (n : Nat) : Prop :=
    (decimalDigits n).length % 2 = 0

  noncomputable def countBeautiful (low high k : Nat) : Nat := by
    classical
    exact ((Finset.Icc low high).filter (fun n => IsBeautiful k n)).card

  noncomputable def countEvenLength (low high : Nat) : Nat := by
    classical
    exact ((Finset.Icc low high).filter (fun n => EvenNumberOfDigits n)).card

  def i64Succ (m : I64) : I64 := m.wrapping_add 1#i64

  /-- Whenever number_of_beautiful_integers(low, high, k) returns a result r, r is the number of integers n such that low <= n <= high and n is beautiful for k, where n is beautiful for k means: writing n in base 10 with no leading zeros, the number of even decimal digits of n equals the number of odd decimal digits of n, and k divides n.
    Preconditions: low, high, and k are integers satisfying 0 < low <= high <= 10^9 and 0 < k <= 20. -/
  theorem spec_1 (low high k : I64)
      (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
      (hk : 0 < k.val) (hk20 : k.val ≤ 20) :
      ∀ r : I64, number_of_beautiful_integers low high k = ok r →
        r.val = (countBeautiful low.val.toNat high.val.toNat k.val.toNat : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (low high k : I64)
        (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
        (hk : 0 < k.val) (hk20 : k.val ≤ 20), ∀ r : I64, number_of_beautiful_integers low high k = ok r →
          r.val = (countBeautiful low.val.toNat high.val.toNat k.val.toNat : Int)) := by
    sorry

  /-- The function number_of_beautiful_integers(low, high, k) returns a result r for every input satisfying these preconditions; in particular, it does not fail, panic, overflow, or access an out-of-bounds index.
    Preconditions: low, high, and k are integers satisfying 0 < low <= high <= 10^9 and 0 < k <= 20. -/
  theorem spec_2 (low high k : I64)
      (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
      (hk : 0 < k.val) (hk20 : k.val ≤ 20) :
      ∃ r : I64, number_of_beautiful_integers low high k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (low high k : I64)
        (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
        (hk : 0 < k.val) (hk20 : k.val ≤ 20), ∃ r : I64, number_of_beautiful_integers low high k = ok r) := by
    sorry

  /-- Whenever number_of_beautiful_integers(low, high, k) returns a result r, we have r >= 0.
    Preconditions: low, high, and k are integers satisfying 0 < low <= high <= 10^9 and 0 < k <= 20. -/
  theorem spec_3 (low high k : I64)
      (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
      (hk : 0 < k.val) (hk20 : k.val ≤ 20) :
      ∀ r : I64, number_of_beautiful_integers low high k = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (low high k : I64)
        (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
        (hk : 0 < k.val) (hk20 : k.val ≤ 20), ∀ r : I64, number_of_beautiful_integers low high k = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever number_of_beautiful_integers(low, high, k) returns a result r, we have r <= high - low + 1.
    Preconditions: low, high, and k are integers satisfying 0 < low <= high <= 10^9 and 0 < k <= 20. -/
  theorem spec_4 (low high k : I64)
      (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
      (hk : 0 < k.val) (hk20 : k.val ≤ 20) :
      ∀ r : I64, number_of_beautiful_integers low high k = ok r →
        r.val ≤ high.val - low.val + 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (low high k : I64)
        (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
        (hk : 0 < k.val) (hk20 : k.val ≤ 20), ∀ r : I64, number_of_beautiful_integers low high k = ok r →
          r.val ≤ high.val - low.val + 1) := by
    sorry

  /-- Whenever number_of_beautiful_integers(low, high, k) returns a result r, we have r <= floor(high / k) - floor((low - 1) / k), where floor(x / k) denotes integer division of the nonnegative integer x by k. Equivalently, r is at most the number of multiples of k in [low, high].
    Preconditions: low, high, and k are integers satisfying 0 < low <= high <= 10^9 and 0 < k <= 20. -/
  theorem spec_5 (low high k : I64)
      (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
      (hk : 0 < k.val) (hk20 : k.val ≤ 20) :
      ∀ r : I64, number_of_beautiful_integers low high k = ok r →
        r.val ≤ high.val / k.val - (low.val - 1) / k.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (low high k : I64)
        (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
        (hk : 0 < k.val) (hk20 : k.val ≤ 20), ∀ r : I64, number_of_beautiful_integers low high k = ok r →
          r.val ≤ high.val / k.val - (low.val - 1) / k.val) := by
    sorry

  /-- Let E be the number of integers n with low <= n <= high whose decimal representation, written without leading zeros, has an even number of digits. Whenever number_of_beautiful_integers(low, high, k) returns a result r, we have r <= E.
    Preconditions: low, high, and k are integers satisfying 0 < low <= high <= 10^9 and 0 < k <= 20. -/
  theorem spec_6 (low high k : I64)
      (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
      (hk : 0 < k.val) (hk20 : k.val ≤ 20) :
      ∀ r : I64, number_of_beautiful_integers low high k = ok r →
        r.val ≤ (countEvenLength low.val.toNat high.val.toNat : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (low high k : I64)
        (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
        (hk : 0 < k.val) (hk20 : k.val ≤ 20), ∀ r : I64, number_of_beautiful_integers low high k = ok r →
          r.val ≤ (countEvenLength low.val.toNat high.val.toNat : Int)) := by
    sorry

  /-- Whenever number_of_beautiful_integers(low, high, k) returns a result r, we have r = 0.
    Preconditions: low, high, and k are integers satisfying 0 < low <= high <= 9 and 0 < k <= 20. -/
  theorem spec_7 (low high k : I64)
      (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 9)
      (hk : 0 < k.val) (hk20 : k.val ≤ 20) :
      ∀ r : I64, number_of_beautiful_integers low high k = ok r → r.val = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (low high k : I64)
        (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 9)
        (hk : 0 < k.val) (hk20 : k.val ≤ 20), ∀ r : I64, number_of_beautiful_integers low high k = ok r → r.val = 0) := by
    sorry

  /-- Whenever the three calls number_of_beautiful_integers(low, high, k), number_of_beautiful_integers(low, m, k), and number_of_beautiful_integers(m + 1, high, k) return results r, r1, and r2 respectively, we have r = r1 + r2.
    Preconditions: low, m, high, and k are integers satisfying 0 < low <= m < high <= 10^9 and 0 < k <= 20. -/
  theorem spec_8 (low m high k : I64)
      (hlow : 0 < low.val) (hlowm : low.val ≤ m.val) (hmhigh : m.val < high.val)
      (hhigh : high.val ≤ (10 : Int) ^ 9) (hk : 0 < k.val) (hk20 : k.val ≤ 20) :
      ∀ r r1 r2 : I64,
        number_of_beautiful_integers low high k = ok r →
        number_of_beautiful_integers low m k = ok r1 →
        number_of_beautiful_integers (i64Succ m) high k = ok r2 →
        r.val = r1.val + r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (low m high k : I64)
        (hlow : 0 < low.val) (hlowm : low.val ≤ m.val) (hmhigh : m.val < high.val)
        (hhigh : high.val ≤ (10 : Int) ^ 9) (hk : 0 < k.val) (hk20 : k.val ≤ 20), ∀ r r1 r2 : I64,
          number_of_beautiful_integers low high k = ok r →
          number_of_beautiful_integers low m k = ok r1 →
          number_of_beautiful_integers (i64Succ m) high k = ok r2 →
          r.val = r1.val + r2.val) := by
    sorry

  /-- Whenever number_of_beautiful_integers(low, high1, k) and number_of_beautiful_integers(low, high2, k) return results r1 and r2 respectively, we have r1 <= r2.
    Preconditions: low, high1, high2, and k are integers satisfying 0 < low <= high1 <= high2 <= 10^9 and 0 < k <= 20. -/
  theorem spec_9 (low high1 high2 k : I64)
      (hlow : 0 < low.val) (hlow1 : low.val ≤ high1.val) (h12 : high1.val ≤ high2.val)
      (hhigh : high2.val ≤ (10 : Int) ^ 9) (hk : 0 < k.val) (hk20 : k.val ≤ 20) :
      ∀ r1 r2 : I64,
        number_of_beautiful_integers low high1 k = ok r1 →
        number_of_beautiful_integers low high2 k = ok r2 →
        r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (low high1 high2 k : I64)
        (hlow : 0 < low.val) (hlow1 : low.val ≤ high1.val) (h12 : high1.val ≤ high2.val)
        (hhigh : high2.val ≤ (10 : Int) ^ 9) (hk : 0 < k.val) (hk20 : k.val ≤ 20), ∀ r1 r2 : I64,
          number_of_beautiful_integers low high1 k = ok r1 →
          number_of_beautiful_integers low high2 k = ok r2 →
          r1.val ≤ r2.val) := by
    sorry

  /-- Whenever number_of_beautiful_integers(low1, high, k) and number_of_beautiful_integers(low2, high, k) return results r1 and r2 respectively, we have r2 <= r1.
    Preconditions: low1, low2, high, and k are integers satisfying 0 < low1 <= low2 <= high <= 10^9 and 0 < k <= 20. -/
  theorem spec_10 (low1 low2 high k : I64)
      (hlow : 0 < low1.val) (h12 : low1.val ≤ low2.val) (h2high : low2.val ≤ high.val)
      (hhigh : high.val ≤ (10 : Int) ^ 9) (hk : 0 < k.val) (hk20 : k.val ≤ 20) :
      ∀ r1 r2 : I64,
        number_of_beautiful_integers low1 high k = ok r1 →
        number_of_beautiful_integers low2 high k = ok r2 →
        r2.val ≤ r1.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (low1 low2 high k : I64)
        (hlow : 0 < low1.val) (h12 : low1.val ≤ low2.val) (h2high : low2.val ≤ high.val)
        (hhigh : high.val ≤ (10 : Int) ^ 9) (hk : 0 < k.val) (hk20 : k.val ≤ 20), ∀ r1 r2 : I64,
          number_of_beautiful_integers low1 high k = ok r1 →
          number_of_beautiful_integers low2 high k = ok r2 →
          r2.val ≤ r1.val) := by
    sorry

  /-- Whenever number_of_beautiful_integers(low, high, k1) and number_of_beautiful_integers(low, high, k2) return results r1 and r2 respectively, we have r2 <= r1.
    Preconditions: low, high, k1, and k2 are integers satisfying 0 < low <= high <= 10^9, 0 < k1 <= k2 <= 20, and k1 divides k2. -/
  theorem spec_11 (low high k1 k2 : I64)
      (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
      (hk1 : 0 < k1.val) (hdiv : k1.val ∣ k2.val) (hk12 : k1.val ≤ k2.val) (hk220 : k2.val ≤ 20) :
      ∀ r1 r2 : I64,
        number_of_beautiful_integers low high k1 = ok r1 →
        number_of_beautiful_integers low high k2 = ok r2 →
        r2.val ≤ r1.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (low high k1 k2 : I64)
        (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
        (hk1 : 0 < k1.val) (hdiv : k1.val ∣ k2.val) (hk12 : k1.val ≤ k2.val) (hk220 : k2.val ≤ 20), ∀ r1 r2 : I64,
          number_of_beautiful_integers low high k1 = ok r1 →
          number_of_beautiful_integers low high k2 = ok r2 →
          r2.val ≤ r1.val) := by
    sorry

  /-- Whenever number_of_beautiful_integers(low, high, k) returns a result r, r > 0 if and only if there exists an integer n such that low <= n <= high and n is beautiful for k, where n is beautiful for k means that in the decimal representation of n without leading zeros the counts of even and odd digits are equal and k divides n.
    Preconditions: low, high, and k are integers satisfying 0 < low <= high <= 10^9 and 0 < k <= 20. -/
  theorem spec_12 (low high k : I64)
      (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
      (hk : 0 < k.val) (hk20 : k.val ≤ 20) :
      ∀ r : I64, number_of_beautiful_integers low high k = ok r →
        (0 < r.val ↔ ∃ n : Nat,
          low.val.toNat ≤ n ∧ n ≤ high.val.toNat ∧ IsBeautiful k.val.toNat n) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (low high k : I64)
        (hlow : 0 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ (10 : Int) ^ 9)
        (hk : 0 < k.val) (hk20 : k.val ≤ 20), ∀ r : I64, number_of_beautiful_integers low high k = ok r →
          (0 < r.val ↔ ∃ n : Nat,
            low.val.toNat ≤ n ∧ n ≤ high.val.toNat ∧ IsBeautiful k.val.toNat n)) := by
    sorry

  end AegisSpec.NumberOfBeautifulIntegers
