import Aegis.NthSuperUglyNumber.Code.Funs

/-!
# Specifications of `Aegis.NthSuperUglyNumber.nth_super_ugly_number`

LeetCode problem `super-ugly-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NthSuperUglyNumber

  namespace AegisSpec.NthSuperUglyNumber

  def vals (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

  def IntPrime (p : ℤ) : Prop := ∃ q : ℕ, Nat.Prime q ∧ p = (q : ℤ)

  def StrictlyIncreasing (l : List ℤ) : Prop := l.Pairwise (· < ·)

  def IsSuperUgly (primes : List ℤ) (u : ℤ) : Prop :=
    0 < u ∧ ∀ p : ℤ, IntPrime p → p ∣ u → p ∈ primes

  noncomputable def superUglyUpTo (primes : List ℤ) (r : ℤ) : Finset ℕ := by
    classical
    exact (Finset.range (r.toNat + 1)).filter (fun k => IsSuperUgly primes (k : ℤ))

  noncomputable def IsNthSuperUgly (primes : List ℤ) (n : ℕ) (u : ℤ) : Prop :=
    IsSuperUgly primes u ∧ (superUglyUpTo primes u).card = n

  def InsertSorted (l : List ℤ) (q : ℤ) (l' : List ℤ) : Prop :=
    StrictlyIncreasing l' ∧ ∃ (s t : List ℤ), l = s ++ t ∧ l' = s ++ q :: t

  /-- Whenever the call nth_super_ugly_number n primes returns a result r, the value r is exactly the n-th super ugly number for primes: r is positive, every prime divisor of r is equal to primes[i] for some i with 0 <= i < len(primes), and the number of positive super ugly integers u for primes with u <= r is exactly n.
    Preconditions: 1 <= n <= 100000; 1 <= len(primes) <= 100; for every i with 0 <= i < len(primes), primes[i] is prime and 2 <= primes[i] <= 1000; the entries are strictly increasing; and the n-th super ugly number for n and primes is at most 2147483647. Here a positive integer u is super ugly for primes iff every prime divisor of u is equal to primes[i] for some i with 0 <= i < len(primes); 1 is super ugly because it has no prime divisors. -/
  theorem spec_1
    (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
    (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
    (hprime : ∀ i (hi : i < primes.val.length),
      IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
    (hsorted : StrictlyIncreasing (vals primes.val))
    (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647) :
    nth_super_ugly_number n primes = ok r →
      IsNthSuperUgly (vals primes.val) n.val.toNat r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
      (hprime : ∀ i (hi : i < primes.val.length),
        IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
      (hsorted : StrictlyIncreasing (vals primes.val))
      (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647), nth_super_ugly_number n primes = ok r →
        IsNthSuperUgly (vals primes.val) n.val.toNat r.val) := by
    sorry

  /-- The call nth_super_ugly_number n primes returns a result r; that is, there exists an i64 value r with nth_super_ugly_number n primes = Result.ok r. It does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: 1 <= n <= 100000; 1 <= len(primes) <= 100; for every i with 0 <= i < len(primes), primes[i] is prime and 2 <= primes[i] <= 1000; the entries are strictly increasing; and the n-th super ugly number for n and primes is at most 2147483647. Here a positive integer u is super ugly for primes iff every prime divisor of u is equal to primes[i] for some i with 0 <= i < len(primes); 1 is super ugly. -/
  theorem spec_2
    (n : Std.I64) (primes : Slice Std.I64)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
    (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
    (hprime : ∀ i (hi : i < primes.val.length),
      IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
    (hsorted : StrictlyIncreasing (vals primes.val))
    (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647) :
    ∃ r : Std.I64, nth_super_ugly_number n primes = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (primes : Slice Std.I64)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
      (hprime : ∀ i (hi : i < primes.val.length),
        IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
      (hsorted : StrictlyIncreasing (vals primes.val))
      (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647), ∃ r : Std.I64, nth_super_ugly_number n primes = ok r) := by
    sorry

  /-- Whenever the call nth_super_ugly_number n primes returns a result r, we have 1 <= r <= 2147483647.
    Preconditions: 1 <= n <= 100000; 1 <= len(primes) <= 100; for every i with 0 <= i < len(primes), primes[i] is prime and 2 <= primes[i] <= 1000; the entries are strictly increasing; and the n-th super ugly number for n and primes is at most 2147483647. Here a positive integer u is super ugly for primes iff every prime divisor of u is equal to primes[i] for some i with 0 <= i < len(primes); 1 is super ugly. -/
  theorem spec_3
    (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
    (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
    (hprime : ∀ i (hi : i < primes.val.length),
      IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
    (hsorted : StrictlyIncreasing (vals primes.val))
    (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647) :
    nth_super_ugly_number n primes = ok r → 1 ≤ r.val ∧ r.val ≤ 2147483647 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
      (hprime : ∀ i (hi : i < primes.val.length),
        IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
      (hsorted : StrictlyIncreasing (vals primes.val))
      (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647), nth_super_ugly_number n primes = ok r → 1 ≤ r.val ∧ r.val ≤ 2147483647) := by
    sorry

  /-- Whenever the call nth_super_ugly_number n primes returns a result r, we have r >= n.
    Preconditions: 1 <= n <= 100000; 1 <= len(primes) <= 100; for every i with 0 <= i < len(primes), primes[i] is prime and 2 <= primes[i] <= 1000; the entries are strictly increasing; and the n-th super ugly number for n and primes is at most 2147483647. Here a positive integer u is super ugly for primes iff every prime divisor of u is equal to primes[i] for some i with 0 <= i < len(primes); 1 is super ugly. -/
  theorem spec_4
    (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
    (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
    (hprime : ∀ i (hi : i < primes.val.length),
      IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
    (hsorted : StrictlyIncreasing (vals primes.val))
    (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647) :
    nth_super_ugly_number n primes = ok r → n.val ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
      (hprime : ∀ i (hi : i < primes.val.length),
        IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
      (hsorted : StrictlyIncreasing (vals primes.val))
      (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647), nth_super_ugly_number n primes = ok r → n.val ≤ r.val) := by
    sorry

  /-- Whenever the call nth_super_ugly_number n primes returns a result r, we have r <= primes[0]^(n-1), where n-1 is interpreted as a nonnegative integer exponent.
    Preconditions: 1 <= n <= 100000; 1 <= len(primes) <= 100; for every i with 0 <= i < len(primes), primes[i] is prime and 2 <= primes[i] <= 1000; the entries are strictly increasing; and the n-th super ugly number for n and primes is at most 2147483647. Here a positive integer u is super ugly for primes iff every prime divisor of u is equal to primes[i] for some i with 0 <= i < len(primes); 1 is super ugly. -/
  theorem spec_5
    (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
    (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
    (hprime : ∀ i (hi : i < primes.val.length),
      IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
    (hsorted : StrictlyIncreasing (vals primes.val))
    (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647) :
    nth_super_ugly_number n primes = ok r →
      r.val ≤ (primes.val[0]'(by omega)).val ^ (n.val.toNat - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
      (hprime : ∀ i (hi : i < primes.val.length),
        IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
      (hsorted : StrictlyIncreasing (vals primes.val))
      (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647), nth_super_ugly_number n primes = ok r →
        r.val ≤ (primes.val[0]'(by omega)).val ^ (n.val.toNat - 1)) := by
    sorry

  /-- Whenever the call nth_super_ugly_number n primes returns a result r, we have r > 1.
    Preconditions: The standard constraints hold: 1 <= n <= 100000; 1 <= len(primes) <= 100; each primes[i] is prime with 2 <= primes[i] <= 1000; the entries are strictly increasing; and the n-th super ugly number fits in 32-bit signed range. Also n > 1. -/
  theorem spec_6
    (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
    (hn_gt_one : 1 < n.val)
    (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
    (hprime : ∀ i (hi : i < primes.val.length),
      IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
    (hsorted : StrictlyIncreasing (vals primes.val))
    (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647) :
    nth_super_ugly_number n primes = ok r → 1 < r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hn_gt_one : 1 < n.val)
      (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
      (hprime : ∀ i (hi : i < primes.val.length),
        IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
      (hsorted : StrictlyIncreasing (vals primes.val))
      (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647), nth_super_ugly_number n primes = ok r → 1 < r.val) := by
    sorry

  /-- Whenever the call nth_super_ugly_number n primes returns a result r, there exist nonnegative integers e_0, e_1, ..., e_{len(primes)-1} such that r = product_{i=0}^{len(primes)-1} primes[i]^(e_i).
    Preconditions: 1 <= n <= 100000; 1 <= len(primes) <= 100; for every i with 0 <= i < len(primes), primes[i] is prime and 2 <= primes[i] <= 1000; the entries are strictly increasing; and the n-th super ugly number for n and primes is at most 2147483647. Here a positive integer u is super ugly for primes iff every prime divisor of u is equal to primes[i] for some i with 0 <= i < len(primes); 1 is super ugly. -/
  theorem spec_7
    (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
    (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
    (hprime : ∀ i (hi : i < primes.val.length),
      IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
    (hsorted : StrictlyIncreasing (vals primes.val))
    (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647) :
    nth_super_ugly_number n primes = ok r →
      ∃ e : Fin (vals primes.val).length → ℕ,
        r.val = ∏ i : Fin (vals primes.val).length, ((vals primes.val)[i.val]'i.isLt) ^ e i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (primes : Slice Std.I64) (r : Std.I64)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
      (hprime : ∀ i (hi : i < primes.val.length),
        IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
      (hsorted : StrictlyIncreasing (vals primes.val))
      (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647), nth_super_ugly_number n primes = ok r →
        ∃ e : Fin (vals primes.val).length → ℕ,
          r.val = ∏ i : Fin (vals primes.val).length, ((vals primes.val)[i.val]'i.isLt) ^ e i) := by
    sorry

  /-- For every integer k with 1 <= k <= n, whenever nth_super_ugly_number k primes returns a result r_k and nth_super_ugly_number n primes returns a result r, we have r_k <= r.
    Preconditions: 1 <= n <= 100000; 1 <= len(primes) <= 100; for every i with 0 <= i < len(primes), primes[i] is prime and 2 <= primes[i] <= 1000; the entries are strictly increasing; and the n-th super ugly number for n and primes is at most 2147483647. Here a positive integer u is super ugly for primes iff every prime divisor of u is equal to primes[i] for some i with 0 <= i < len(primes); 1 is super ugly. -/
  theorem spec_8
    (n : Std.I64) (primes : Slice Std.I64)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
    (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
    (hprime : ∀ i (hi : i < primes.val.length),
      IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
    (hsorted : StrictlyIncreasing (vals primes.val))
    (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647) :
    ∀ (k : Std.I64), 1 ≤ k.val → k.val ≤ n.val →
      ∀ (r_k : Std.I64), nth_super_ugly_number k primes = ok r_k →
      ∀ (r : Std.I64), nth_super_ugly_number n primes = ok r → r_k.val ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (primes : Slice Std.I64)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
      (hprime : ∀ i (hi : i < primes.val.length),
        IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
      (hsorted : StrictlyIncreasing (vals primes.val))
      (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647), ∀ (k : Std.I64), 1 ≤ k.val → k.val ≤ n.val →
        ∀ (r_k : Std.I64), nth_super_ugly_number k primes = ok r_k →
        ∀ (r : Std.I64), nth_super_ugly_number n primes = ok r → r_k.val ≤ r.val) := by
    sorry

  /-- If nth_super_ugly_number n primes returns a result r and nth_super_ugly_number n primes' returns a result r', then r' <= r.
    Preconditions: 1 <= n <= 100000; 1 <= len(primes) <= 100; for every i with 0 <= i < len(primes), primes[i] is prime and 2 <= primes[i] <= 1000; the entries are strictly increasing; and the n-th super ugly number for n and primes is at most 2147483647. Also q is a prime with 2 <= q <= 1000, q is not in primes, len(primes) < 100, and primes' is the strictly increasing list obtained by inserting q into primes. The n-th super ugly number for primes' is also at most 2147483647. -/
  theorem spec_9
    (n : Std.I64) (primes primes' : Slice Std.I64) (q : ℤ) (r r' : Std.I64)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
    (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
    (hprime : ∀ i (hi : i < primes.val.length),
      IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
    (hsorted : StrictlyIncreasing (vals primes.val))
    (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647)
    (hq_prime : IntPrime q) (hq_lower : 2 ≤ q) (hq_upper : q ≤ 1000)
    (hq_not_mem : q ∉ vals primes.val)
    (hshort : primes.val.length < 100)
    (hinsert : InsertSorted (vals primes.val) q (vals primes'.val))
    (hfit' : ∃ u : ℤ, IsNthSuperUgly (vals primes'.val) n.val.toNat u ∧ u ≤ 2147483647) :
    nth_super_ugly_number n primes = ok r →
      nth_super_ugly_number n primes' = ok r' → r'.val ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (primes primes' : Slice Std.I64) (q : ℤ) (r r' : Std.I64)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hlen_lower : 1 ≤ primes.val.length) (hlen_upper : primes.val.length ≤ 100)
      (hprime : ∀ i (hi : i < primes.val.length),
        IntPrime (primes.val[i]).val ∧ 2 ≤ (primes.val[i]).val ∧ (primes.val[i]).val ≤ 1000)
      (hsorted : StrictlyIncreasing (vals primes.val))
      (hfit : ∃ u : ℤ, IsNthSuperUgly (vals primes.val) n.val.toNat u ∧ u ≤ 2147483647)
      (hq_prime : IntPrime q) (hq_lower : 2 ≤ q) (hq_upper : q ≤ 1000)
      (hq_not_mem : q ∉ vals primes.val)
      (hshort : primes.val.length < 100)
      (hinsert : InsertSorted (vals primes.val) q (vals primes'.val))
      (hfit' : ∃ u : ℤ, IsNthSuperUgly (vals primes'.val) n.val.toNat u ∧ u ≤ 2147483647), nth_super_ugly_number n primes = ok r →
        nth_super_ugly_number n primes' = ok r' → r'.val ≤ r.val) := by
    sorry

  end AegisSpec.NthSuperUglyNumber
