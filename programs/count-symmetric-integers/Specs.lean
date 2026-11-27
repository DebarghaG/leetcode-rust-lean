import Aegis.CountSymmetricIntegers.Code.Funs

/-!
# Specifications of `Aegis.CountSymmetricIntegers.count_symmetric_integers`

LeetCode problem `count-symmetric-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Classical
  open Aegis.CountSymmetricIntegers

  set_option maxHeartbeats 1000000

  namespace AegisSpec.CountSymmetricIntegers

  def digit (x i : ℕ) : ℕ := (x / 10 ^ i) % 10

  def numDigits (x : ℕ) : ℕ :=
    if h : x < 10 then (if x = 0 then 0 else 1) else numDigits (x / 10) + 1
  termination_by x
  decreasing_by omega

  def IsSymmetric (x : ℕ) : Prop :=
    ∃ n : ℕ, 1 ≤ n ∧ numDigits x = 2 * n ∧
      (∑ i ∈ Finset.range n, digit x i) = (∑ i ∈ Finset.range n, digit x (n + i))

  noncomputable def numSymmetric (lo hi : ℕ) : ℕ :=
    ((Finset.Icc lo hi).filter IsSymmetric).card

  noncomputable def numEvenDigits (lo hi : ℕ) : ℕ :=
    ((Finset.Icc lo hi).filter (fun x => numDigits x % 2 = 0)).card

  def numMultiplesOfEleven (low high : ℤ) : ℕ :=
    ((Finset.Icc 1 9).filter (fun a : ℕ => low ≤ 11 * (a : ℤ) ∧ 11 * (a : ℤ) ≤ high)).card

  def isBalancedFourDigit (x : ℕ) : Prop :=
    ∃ a b c d : ℕ, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧
      x = 1000 * a + 100 * b + 10 * c + d ∧ a + b = c + d

  noncomputable def numBalancedFourDigit (lo hi : ℕ) : ℕ :=
    ((Finset.Icc lo hi).filter isBalancedFourDigit).card

  /-- The function returns a result r and r is the number of integers x with low <= x <= high such that x is symmetric. An integer x > 0 is symmetric exactly when its decimal representation has even length 2n with n >= 1 and, writing digit_i(x) = (floor(x / 10^i)) mod 10 for i >= 0 (0-indexed from the units digit), the equality sum_{i=0}^{n-1} digit_i(x) = sum_{i=n}^{2n-1} digit_i(x) holds.
    Preconditions: low and high are Std.I64 values representing integers with 1 <= low <= high <= 10000. -/
  theorem spec_1 (low high : Std.I64)
      (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000) :
      ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
        r.val = (numSymmetric low.val.toNat high.val.toNat : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000), ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
          r.val = (numSymmetric low.val.toNat high.val.toNat : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or go out of bounds on any input satisfying the preconditions.
    Preconditions: low and high are Std.I64 values representing integers with 1 <= low <= high <= 10000. -/
  theorem spec_2 (low high : Std.I64)
      (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000) :
      ∃ r : Std.I64, count_symmetric_integers low high = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000), ∃ r : Std.I64, count_symmetric_integers low high = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r.
    Preconditions: low and high are Std.I64 values representing integers with 1 <= low <= high <= 10000. -/
  theorem spec_3 (low high : Std.I64)
      (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000) :
      ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧ 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000), ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧ 0 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= high - low + 1, the number of integers in [low, high].
    Preconditions: low and high are Std.I64 values representing integers with 1 <= low <= high <= 10000. -/
  theorem spec_4 (low high : Std.I64)
      (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000) :
      ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
        r.val ≤ high.val - low.val + 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000), ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
          r.val ≤ high.val - low.val + 1) := by
    sorry

  /-- The function returns a result r and r is at most the number of integers x in [low, high] whose decimal representation has an even number of digits.
    Preconditions: low and high are Std.I64 values representing integers with 1 <= low <= high <= 10000. -/
  theorem spec_5 (low high : Std.I64)
      (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000) :
      ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
        r.val ≤ (numEvenDigits low.val.toNat high.val.toNat : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000), ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
          r.val ≤ (numEvenDigits low.val.toNat high.val.toNat : ℤ)) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: low and high are Std.I64 values representing integers with 1 <= low <= high <= 10000, and every integer x with low <= x <= high has an odd number of decimal digits. -/
  theorem spec_6 (low high : Std.I64)
      (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000)
      (hodd : ∀ x : ℕ, low.val.toNat ≤ x → x ≤ high.val.toNat → numDigits x % 2 = 1) :
      ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000)
        (hodd : ∀ x : ℕ, low.val.toNat ≤ x → x ≤ high.val.toNat → numDigits x % 2 = 1), ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r = 1 if low is symmetric, and r = 0 otherwise. Here symmetric is defined as in spec_1: even decimal length 2n and equal sums of the last n and first n digits.
    Preconditions: low and high are Std.I64 values representing integers with 1 <= low <= high <= 10000, and low = high. -/
  theorem spec_7 (low high : Std.I64)
      (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000)
      (hsingle : low = high) :
      ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
        (IsSymmetric low.val.toNat → r.val = 1) ∧
        (¬ IsSymmetric low.val.toNat → r.val = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000)
        (hsingle : low = high), ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
          (IsSymmetric low.val.toNat → r.val = 1) ∧
          (¬ IsSymmetric low.val.toNat → r.val = 0)) := by
    sorry

  /-- The function returns a result r and r is the number of integers a with 1 <= a <= 9 and low <= 11*a <= high.
    Preconditions: low and high are Std.I64 values representing integers with 10 <= low <= high <= 99. -/
  theorem spec_8 (low high : Std.I64)
      (hlo : 10 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 99) :
      ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
        r.val = (numMultiplesOfEleven low.val high.val : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 10 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 99), ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
          r.val = (numMultiplesOfEleven low.val high.val : ℤ)) := by
    sorry

  /-- The function returns a result r and r is the number of integers x with low <= x <= high such that, writing x = 1000*a + 100*b + 10*c + d with a in {1,2,3,4,5,6,7,8,9} and b,c,d in {0,1,2,3,4,5,6,7,8,9}, the equality a + b = c + d holds.
    Preconditions: low and high are Std.I64 values representing integers with 1000 <= low <= high <= 9999. -/
  theorem spec_9 (low high : Std.I64)
      (hlo : 1000 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 9999) :
      ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
        r.val = (numBalancedFourDigit low.val.toNat high.val.toNat : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1000 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 9999), ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
          r.val = (numBalancedFourDigit low.val.toNat high.val.toNat : ℤ)) := by
    sorry

  /-- The function returns a result r and r is the number of symmetric integers x with low <= x <= 9999.
    Preconditions: low and high are Std.I64 values representing integers with 1 <= low <= high <= 10000, high = 10000, and low <= 9999. -/
  theorem spec_10 (low high : Std.I64)
      (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val = 10000)
      (hlow9999 : low.val ≤ 9999) :
      ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
        r.val = (numSymmetric low.val.toNat 9999 : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val = 10000)
        (hlow9999 : low.val ≤ 9999), ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
          r.val = (numSymmetric low.val.toNat 9999 : ℤ)) := by
    sorry

  /-- The function returns a result r and, for every integer mid with low <= mid < high, r = N(low, mid) + N(mid+1, high), where N(u,v) denotes the number of symmetric integers in [u,v].
    Preconditions: low and high are Std.I64 values representing integers with 1 <= low <= high <= 10000. -/
  theorem spec_11 (low high : Std.I64)
      (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000) :
      ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
        ∀ mid : ℕ, low.val ≤ (mid : ℤ) → (mid : ℤ) < high.val →
          r.val = (numSymmetric low.val.toNat mid : ℤ) +
            (numSymmetric (mid + 1) high.val.toNat : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000), ∃ r : Std.I64, count_symmetric_integers low high = ok r ∧
          ∀ mid : ℕ, low.val ≤ (mid : ℤ) → (mid : ℤ) < high.val →
            r.val = (numSymmetric low.val.toNat mid : ℤ) +
              (numSymmetric (mid + 1) high.val.toNat : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if r > 0 then there exists an integer x with low <= x <= high that is symmetric.
    Preconditions: low and high are Std.I64 values representing integers with 1 <= low <= high <= 10000. -/
  theorem spec_12 (low high : Std.I64)
      (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000) :
      ∀ r : Std.I64, count_symmetric_integers low high = ok r → 0 < r.val →
        ∃ x : ℕ, low.val ≤ (x : ℤ) ∧ (x : ℤ) ≤ high.val ∧ IsSymmetric x := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000), ∀ r : Std.I64, count_symmetric_integers low high = ok r → 0 < r.val →
          ∃ x : ℕ, low.val ≤ (x : ℤ) ∧ (x : ℤ) ≤ high.val ∧ IsSymmetric x) := by
    sorry

  /-- Whenever the function returns a result r, if r = 0 then for every integer x with low <= x <= high, x is not symmetric.
    Preconditions: low and high are Std.I64 values representing integers with 1 <= low <= high <= 10000. -/
  theorem spec_13 (low high : Std.I64)
      (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000) :
      ∀ r : Std.I64, count_symmetric_integers low high = ok r → r.val = 0 →
        ∀ x : ℕ, low.val ≤ (x : ℤ) → (x : ℤ) ≤ high.val → ¬ IsSymmetric x := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (low high : Std.I64)
        (hlo : 1 ≤ low.val) (hle : low.val ≤ high.val) (hhi : high.val ≤ 10000), ∀ r : Std.I64, count_symmetric_integers low high = ok r → r.val = 0 →
          ∀ x : ℕ, low.val ≤ (x : ℤ) → (x : ℤ) ≤ high.val → ¬ IsSymmetric x) := by
    sorry

  end AegisSpec.CountSymmetricIntegers
