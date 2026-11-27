import Aegis.KthSmallestPrimeFraction.Code.Funs

/-!
# Specifications of `Aegis.KthSmallestPrimeFraction.kth_smallest_prime_fraction`

LeetCode problem `k-th-smallest-prime-fraction`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.KthSmallestPrimeFraction

  namespace AegisSpec.KthSmallestPrimeFraction

  def vals (arr : Slice Std.I64) : List ℤ := arr.val.map IScalar.val

  def len (arr : Slice Std.I64) : ℕ := (vals arr).length

  def entry (arr : Slice Std.I64) (i : ℕ) : Option ℤ := (vals arr)[i]?

  def outVals (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map IScalar.val

  def outEntry (r : alloc.vec.Vec Std.I64) (i : ℕ) : Option ℤ := (outVals r)[i]?

  def IsPrimeInt (z : ℤ) : Prop := ∃ p : ℕ, Nat.Prime p ∧ z = (p : ℤ)

  def frac (arr : Slice Std.I64) (a b : ℕ) : ℚ :=
    match entry arr a, entry arr b with
    | some x, some y => (x : ℚ) / (y : ℚ)
    | _, _ => 0

  def pairSet (n : ℕ) : Finset (ℕ × ℕ) :=
    ((Finset.range n).product (Finset.range n)).filter (fun ab => ab.1 < ab.2)

  def countBelow (arr : Slice Std.I64) (i j : ℕ) : ℕ :=
    ((pairSet (len arr)).filter (fun ab => frac arr ab.1 ab.2 < frac arr i j)).card

  def countAbove (arr : Slice Std.I64) (i j : ℕ) : ℕ :=
    ((pairSet (len arr)).filter (fun ab => frac arr i j < frac arr ab.1 ab.2)).card

  /-- The call returns a result r (it does not fail). The vector r has length 2, and there exist indices i, j with 0 <= i < j < n such that r[0] = arr[i], r[1] = arr[j], and the number of pairs (a,b) with 0 <= a < b < n and arr[a]/arr[b] < arr[i]/arr[j] is exactly k-1.
    Preconditions: Let n = len(arr). The array arr satisfies 2 <= n <= 1000, arr[0] = 1, for every i with 1 <= i < n arr[i] is prime, and for all i, j with 0 <= i < j < n we have arr[i] < arr[j]; moreover 1 <= arr[i] <= 30000 for every 0 <= i < n. The integer k satisfies 1 <= k <= n*(n-1)/2. Fractions are ordinary rational values arr[i]/arr[j], not integer division. -/
  theorem spec_1
      (arr : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
      (hfirst : entry arr 0 = some 1)
      (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
      (hsorted : ∀ i j, i < j → j < len arr →
        ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
      (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)) :
      ∃ r : alloc.vec.Vec Std.I64,
        kth_smallest_prime_fraction arr k = ok r ∧
        (outVals r).length = 2 ∧
        ∃ i j : ℕ, i < j ∧ j < len arr ∧
          outEntry r 0 = entry arr i ∧
          outEntry r 1 = entry arr j ∧
          (countBelow arr i j : ℤ) = k.val - 1 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
        (hfirst : entry arr 0 = some 1)
        (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
        (hsorted : ∀ i j, i < j → j < len arr →
          ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
        (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)), ∃ r : alloc.vec.Vec Std.I64,
          kth_smallest_prime_fraction arr k = ok r ∧
          (outVals r).length = 2 ∧
          ∃ i j : ℕ, i < j ∧ j < len arr ∧
            outEntry r 0 = entry arr i ∧
            outEntry r 1 = entry arr j ∧
            (countBelow arr i j : ℤ) = k.val - 1) := by
    sorry

  /-- For every input satisfying the preconditions, the call returns a result r; it does not panic, overflow, index out of bounds, or otherwise fail.
    Preconditions: Let n = len(arr). The array arr satisfies 2 <= n <= 1000, arr[0] = 1, for every i with 1 <= i < n arr[i] is prime, and for all i, j with 0 <= i < j < n we have arr[i] < arr[j]; moreover 1 <= arr[i] <= 30000 for every 0 <= i < n. The integer k satisfies 1 <= k <= n*(n-1)/2. -/
  theorem spec_2
      (arr : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
      (hfirst : entry arr 0 = some 1)
      (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
      (hsorted : ∀ i j, i < j → j < len arr →
        ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
      (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)) :
      ∃ r : alloc.vec.Vec Std.I64, kth_smallest_prime_fraction arr k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
        (hfirst : entry arr 0 = some 1)
        (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
        (hsorted : ∀ i j, i < j → j < len arr →
          ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
        (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)), ∃ r : alloc.vec.Vec Std.I64, kth_smallest_prime_fraction arr k = ok r) := by
    sorry

  /-- Whenever the call returns a result r, len(r) = 2.
    Preconditions: Let n = len(arr). The array arr satisfies 2 <= n <= 1000, arr[0] = 1, for every i with 1 <= i < n arr[i] is prime, and for all i, j with 0 <= i < j < n we have arr[i] < arr[j]; moreover 1 <= arr[i] <= 30000 for every 0 <= i < n. The integer k satisfies 1 <= k <= n*(n-1)/2. -/
  theorem spec_3
      (arr : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
      (hfirst : entry arr 0 = some 1)
      (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
      (hsorted : ∀ i j, i < j → j < len arr →
        ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
      (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        kth_smallest_prime_fraction arr k = ok r → (outVals r).length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
        (hfirst : entry arr 0 = some 1)
        (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
        (hsorted : ∀ i j, i < j → j < len arr →
          ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
        (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          kth_smallest_prime_fraction arr k = ok r → (outVals r).length = 2) := by
    sorry

  /-- Whenever the call returns a result r, there exist indices i and j with 0 <= i < j < n such that r[0] = arr[i] and r[1] = arr[j].
    Preconditions: Let n = len(arr). The array arr satisfies 2 <= n <= 1000, arr[0] = 1, for every i with 1 <= i < n arr[i] is prime, and for all i, j with 0 <= i < j < n we have arr[i] < arr[j]; moreover 1 <= arr[i] <= 30000 for every 0 <= i < n. The integer k satisfies 1 <= k <= n*(n-1)/2. -/
  theorem spec_4
      (arr : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
      (hfirst : entry arr 0 = some 1)
      (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
      (hsorted : ∀ i j, i < j → j < len arr →
        ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
      (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        kth_smallest_prime_fraction arr k = ok r →
        ∃ i j : ℕ, i < j ∧ j < len arr ∧
          outEntry r 0 = entry arr i ∧ outEntry r 1 = entry arr j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
        (hfirst : entry arr 0 = some 1)
        (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
        (hsorted : ∀ i j, i < j → j < len arr →
          ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
        (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          kth_smallest_prime_fraction arr k = ok r →
          ∃ i j : ℕ, i < j ∧ j < len arr ∧
            outEntry r 0 = entry arr i ∧ outEntry r 1 = entry arr j) := by
    sorry

  /-- Whenever the call returns a result r, 1 <= r[0] < r[1] <= 30000.
    Preconditions: Let n = len(arr). The array arr satisfies 2 <= n <= 1000, arr[0] = 1, for every i with 1 <= i < n arr[i] is prime, and for all i, j with 0 <= i < j < n we have arr[i] < arr[j]; moreover 1 <= arr[i] <= 30000 for every 0 <= i < n. The integer k satisfies 1 <= k <= n*(n-1)/2. -/
  theorem spec_5
      (arr : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
      (hfirst : entry arr 0 = some 1)
      (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
      (hsorted : ∀ i j, i < j → j < len arr →
        ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
      (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        kth_smallest_prime_fraction arr k = ok r →
        ∀ x y : ℤ, outEntry r 0 = some x → outEntry r 1 = some y →
          1 ≤ x ∧ x < y ∧ y ≤ 30000 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
        (hfirst : entry arr 0 = some 1)
        (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
        (hsorted : ∀ i j, i < j → j < len arr →
          ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
        (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          kth_smallest_prime_fraction arr k = ok r →
          ∀ x y : ℤ, outEntry r 0 = some x → outEntry r 1 = some y →
            1 ≤ x ∧ x < y ∧ y ≤ 30000) := by
    sorry

  /-- Whenever the call returns a result r, r[0] = 1 and r[1] = arr[n-1].
    Preconditions: Let n = len(arr). The array arr satisfies 2 <= n <= 1000, arr[0] = 1, for every i with 1 <= i < n arr[i] is prime, and for all i, j with 0 <= i < j < n we have arr[i] < arr[j]; moreover 1 <= arr[i] <= 30000 for every 0 <= i < n. The integer k satisfies 1 <= k <= n*(n-1)/2, and additionally k = 1. -/
  theorem spec_6
      (arr : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
      (hfirst : entry arr 0 = some 1)
      (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
      (hsorted : ∀ i j, i < j → j < len arr →
        ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
      (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ))
      (hk : k.val = 1) :
      ∀ r : alloc.vec.Vec Std.I64,
        kth_smallest_prime_fraction arr k = ok r →
        outEntry r 0 = some 1 ∧ outEntry r 1 = entry arr (len arr - 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
        (hfirst : entry arr 0 = some 1)
        (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
        (hsorted : ∀ i j, i < j → j < len arr →
          ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
        (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ))
        (hk : k.val = 1), ∀ r : alloc.vec.Vec Std.I64,
          kth_smallest_prime_fraction arr k = ok r →
          outEntry r 0 = some 1 ∧ outEntry r 1 = entry arr (len arr - 1)) := by
    sorry

  /-- Whenever the call returns a result r, there exist indices i, j with 0 <= i < j < n such that r[0] = arr[i], r[1] = arr[j], and for every pair (a,b) with 0 <= a < b < n, arr[a]/arr[b] <= arr[i]/arr[j].
    Preconditions: Let n = len(arr). The array arr satisfies 2 <= n <= 1000, arr[0] = 1, for every i with 1 <= i < n arr[i] is prime, and for all i, j with 0 <= i < j < n we have arr[i] < arr[j]; moreover 1 <= arr[i] <= 30000 for every 0 <= i < n. The integer k satisfies 1 <= k <= n*(n-1)/2, and additionally k = n*(n-1)/2. Fractions such as arr[a]/arr[b] are ordinary rational values, not integer division. -/
  theorem spec_7
      (arr : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
      (hfirst : entry arr 0 = some 1)
      (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
      (hsorted : ∀ i j, i < j → j < len arr →
        ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
      (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ))
      (hk : k.val = ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        kth_smallest_prime_fraction arr k = ok r →
        ∃ i j : ℕ, i < j ∧ j < len arr ∧
          outEntry r 0 = entry arr i ∧ outEntry r 1 = entry arr j ∧
          ∀ a b : ℕ, a < b → b < len arr → frac arr a b ≤ frac arr i j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
        (hfirst : entry arr 0 = some 1)
        (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
        (hsorted : ∀ i j, i < j → j < len arr →
          ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
        (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ))
        (hk : k.val = ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          kth_smallest_prime_fraction arr k = ok r →
          ∃ i j : ℕ, i < j ∧ j < len arr ∧
            outEntry r 0 = entry arr i ∧ outEntry r 1 = entry arr j ∧
            ∀ a b : ℕ, a < b → b < len arr → frac arr a b ≤ frac arr i j) := by
    sorry

  /-- Whenever the call returns a result r and i, j are indices with 0 <= i < j < n such that r[0] = arr[i] and r[1] = arr[j], the number of pairs (a,b) with 0 <= a < b < n and arr[a]/arr[b] < arr[i]/arr[j] is at most k-1.
    Preconditions: Let n = len(arr). The array arr satisfies 2 <= n <= 1000, arr[0] = 1, for every i with 1 <= i < n arr[i] is prime, and for all i, j with 0 <= i < j < n we have arr[i] < arr[j]; moreover 1 <= arr[i] <= 30000 for every 0 <= i < n. The integer k satisfies 1 <= k <= n*(n-1)/2. Fractions such as arr[a]/arr[b] are ordinary rational values, not integer division. -/
  theorem spec_8
      (arr : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
      (hfirst : entry arr 0 = some 1)
      (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
      (hsorted : ∀ i j, i < j → j < len arr →
        ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
      (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)) :
      ∀ (r : alloc.vec.Vec Std.I64), kth_smallest_prime_fraction arr k = ok r →
      ∀ i j : ℕ, i < j → j < len arr →
        outEntry r 0 = entry arr i → outEntry r 1 = entry arr j →
        (countBelow arr i j : ℤ) ≤ k.val - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
        (hfirst : entry arr 0 = some 1)
        (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
        (hsorted : ∀ i j, i < j → j < len arr →
          ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
        (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)), ∀ (r : alloc.vec.Vec Std.I64), kth_smallest_prime_fraction arr k = ok r →
        ∀ i j : ℕ, i < j → j < len arr →
          outEntry r 0 = entry arr i → outEntry r 1 = entry arr j →
          (countBelow arr i j : ℤ) ≤ k.val - 1) := by
    sorry

  /-- Whenever the call returns a result r and i, j are indices with 0 <= i < j < n such that r[0] = arr[i] and r[1] = arr[j], the number of pairs (a,b) with 0 <= a < b < n and arr[a]/arr[b] < arr[i]/arr[j] is at least k-1.
    Preconditions: Let n = len(arr). The array arr satisfies 2 <= n <= 1000, arr[0] = 1, for every i with 1 <= i < n arr[i] is prime, and for all i, j with 0 <= i < j < n we have arr[i] < arr[j]; moreover 1 <= arr[i] <= 30000 for every 0 <= i < n. The integer k satisfies 1 <= k <= n*(n-1)/2. Fractions such as arr[a]/arr[b] are ordinary rational values, not integer division. -/
  theorem spec_9
      (arr : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
      (hfirst : entry arr 0 = some 1)
      (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
      (hsorted : ∀ i j, i < j → j < len arr →
        ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
      (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)) :
      ∀ (r : alloc.vec.Vec Std.I64), kth_smallest_prime_fraction arr k = ok r →
      ∀ i j : ℕ, i < j → j < len arr →
        outEntry r 0 = entry arr i → outEntry r 1 = entry arr j →
        k.val - 1 ≤ (countBelow arr i j : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
        (hfirst : entry arr 0 = some 1)
        (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
        (hsorted : ∀ i j, i < j → j < len arr →
          ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
        (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)), ∀ (r : alloc.vec.Vec Std.I64), kth_smallest_prime_fraction arr k = ok r →
        ∀ i j : ℕ, i < j → j < len arr →
          outEntry r 0 = entry arr i → outEntry r 1 = entry arr j →
          k.val - 1 ≤ (countBelow arr i j : ℤ)) := by
    sorry

  /-- Whenever the call returns a result r and i, j are indices with 0 <= i < j < n such that r[0] = arr[i] and r[1] = arr[j], the number of pairs (a,b) with 0 <= a < b < n and arr[a]/arr[b] > arr[i]/arr[j] is exactly n*(n-1)/2 - k.
    Preconditions: Let n = len(arr). The array arr satisfies 2 <= n <= 1000, arr[0] = 1, for every i with 1 <= i < n arr[i] is prime, and for all i, j with 0 <= i < j < n we have arr[i] < arr[j]; moreover 1 <= arr[i] <= 30000 for every 0 <= i < n. The integer k satisfies 1 <= k <= n*(n-1)/2. Fractions such as arr[a]/arr[b] are ordinary rational values, not integer division. -/
  theorem spec_10
      (arr : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
      (hfirst : entry arr 0 = some 1)
      (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
      (hsorted : ∀ i j, i < j → j < len arr →
        ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
      (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)) :
      ∀ (r : alloc.vec.Vec Std.I64), kth_smallest_prime_fraction arr k = ok r →
      ∀ i j : ℕ, i < j → j < len arr →
        outEntry r 0 = entry arr i → outEntry r 1 = entry arr j →
        (countAbove arr i j : ℤ) = ((len arr * (len arr - 1) / 2 : ℕ) : ℤ) - k.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
        (hfirst : entry arr 0 = some 1)
        (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
        (hsorted : ∀ i j, i < j → j < len arr →
          ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
        (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)), ∀ (r : alloc.vec.Vec Std.I64), kth_smallest_prime_fraction arr k = ok r →
        ∀ i j : ℕ, i < j → j < len arr →
          outEntry r 0 = entry arr i → outEntry r 1 = entry arr j →
          (countAbove arr i j : ℤ) = ((len arr * (len arr - 1) / 2 : ℕ) : ℤ) - k.val) := by
    sorry

  /-- If a call of kth_smallest_prime_fraction(arr, k1) returns r1 and a call of kth_smallest_prime_fraction(arr, k2) returns r2, then r1[0]/r1[1] < r2[0]/r2[1].
    Preconditions: Let n = len(arr). The array arr satisfies 2 <= n <= 1000, arr[0] = 1, for every i with 1 <= i < n arr[i] is prime, and for all i, j with 0 <= i < j < n we have arr[i] < arr[j]; moreover 1 <= arr[i] <= 30000 for every 0 <= i < n. Let k1 and k2 be integers satisfying 1 <= k1 < k2 <= n*(n-1)/2. Fractions are ordinary rational values. -/
  theorem spec_11
      (arr : Slice Std.I64) (k1 k2 : Std.I64)
      (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
      (hfirst : entry arr 0 = some 1)
      (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
      (hsorted : ∀ i j, i < j → j < len arr →
        ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
      (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
      (hk1_lo : 1 ≤ k1.val) (hk12 : k1.val < k2.val)
      (hk2_hi : k2.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)) :
      ∀ r1 r2 : alloc.vec.Vec Std.I64,
        kth_smallest_prime_fraction arr k1 = ok r1 →
        kth_smallest_prime_fraction arr k2 = ok r2 →
        ∀ x1 y1 x2 y2 : ℤ,
          outEntry r1 0 = some x1 → outEntry r1 1 = some y1 →
          outEntry r2 0 = some x2 → outEntry r2 1 = some y2 →
          (x1 : ℚ) / (y1 : ℚ) < (x2 : ℚ) / (y2 : ℚ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64) (k1 k2 : Std.I64)
        (hn_lo : 2 ≤ len arr) (hn_hi : len arr ≤ 1000)
        (hfirst : entry arr 0 = some 1)
        (hprime : ∀ i, 1 ≤ i → i < len arr → ∀ z : ℤ, entry arr i = some z → IsPrimeInt z)
        (hsorted : ∀ i j, i < j → j < len arr →
          ∀ x y : ℤ, entry arr i = some x → entry arr j = some y → x < y)
        (hbounds : ∀ i, i < len arr → ∀ z : ℤ, entry arr i = some z → 1 ≤ z ∧ z ≤ 30000)
        (hk1_lo : 1 ≤ k1.val) (hk12 : k1.val < k2.val)
        (hk2_hi : k2.val ≤ ((len arr * (len arr - 1) / 2 : ℕ) : ℤ)), ∀ r1 r2 : alloc.vec.Vec Std.I64,
          kth_smallest_prime_fraction arr k1 = ok r1 →
          kth_smallest_prime_fraction arr k2 = ok r2 →
          ∀ x1 y1 x2 y2 : ℤ,
            outEntry r1 0 = some x1 → outEntry r1 1 = some y1 →
            outEntry r2 0 = some x2 → outEntry r2 1 = some y2 →
            (x1 : ℚ) / (y1 : ℚ) < (x2 : ℚ) / (y2 : ℚ)) := by
    sorry

  end AegisSpec.KthSmallestPrimeFraction
