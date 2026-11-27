import Aegis.NumberOfWays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfWays.number_of_ways`

LeetCode problem `find-the-number-of-possible-ways-for-an-event`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfWays

  def M : ℕ := 1000000007

  def IsResidue (t r : ℤ) : Prop :=
    0 ≤ r ∧ r < (M : ℤ) ∧ r % (M : ℤ) = t % (M : ℤ)

  def stirling2 : ℕ → ℕ → ℕ
    | 0, 0 => 1
    | 0, _ + 1 => 0
    | _ + 1, 0 => 0
    | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

  def onto (n k : ℕ) : ℕ := k.factorial * stirling2 n k

  def C (x k : ℕ) : ℕ := x.choose k

  def falling (x : ℕ) : ℕ → ℕ
    | 0 => 1
    | m + 1 => falling x m * (x - m)

  def T (n x y : ℕ) : ℕ :=
    ∑ k ∈ Finset.range (min n x), C x (k + 1) * onto n (k + 1) * y ^ (k + 1)

  def Tevents (n x y : ℕ) : ℕ :=
    (Finset.univ : Finset (Fin n → Fin x)).sum (fun f => y ^ (Finset.univ.image f).card)

  def Tfall (n x y : ℕ) : ℕ :=
    ∑ k ∈ Finset.range (min n x), falling x (k + 1) * stirling2 n (k + 1) * y ^ (k + 1)

  def Tbin (n x y : ℕ) : ℤ :=
    ∑ i ∈ Finset.range x,
      (C x (i + 1) : ℤ) * ((i + 1 : ℕ) : ℤ) ^ n * (y : ℤ) ^ (i + 1)
        * (1 - (y : ℤ)) ^ (x - (i + 1))

  abbrev IsSetPartition {n : ℕ} (P : Finset (Finset (Fin n))) : Prop :=
    (∀ b, b ∈ P → b.Nonempty) ∧
    (∀ i : Fin n, ∃ b, b ∈ P ∧ i ∈ b) ∧
    (∀ b₁, b₁ ∈ P → ∀ b₂, b₂ ∈ P → b₁ ≠ b₂ → Disjoint b₁ b₂)

  def Tpart (n x y : ℕ) : ℕ :=
    ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter
      (fun P => IsSetPartition P)).sum (fun P => falling x P.card * y ^ P.card)

  /-- Whenever the function returns a result r, r is the unique integer satisfying 0 <= r < M and r == T(n,x,y) (mod M).
    Preconditions: n, x, y are Std.I64 values with 1 <= n <= 1000, 1 <= x <= 1000, and 1 <= y <= 1000. Let M = 1000000007. For k >= 1 let onto(n,k) be the number of surjective functions from {0,...,n-1} onto {0,...,k-1} (and onto(n,k)=0 for k>n). Let C(x,k)=x!/(k!(x-k)!). Define T(n,x,y) = sum_{k=1}^{min(n,x)} C(x,k) * onto(n,k) * y^k. -/
  theorem spec_1 (n x y r : Std.I64)
      (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
      (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r) :
      IsResidue (T n.val.toNat x.val.toNat y.val.toNat : ℤ) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n x y r : Std.I64)
        (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
        (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r), IsResidue (T n.val.toNat x.val.toNat y.val.toNat : ℤ) r.val) := by
    sorry

  /-- For every such n, x, y, the function returns a result r; it does not fail, overflow, or panic.
    Preconditions: n, x, y are Std.I64 values with 1 <= n <= 1000, 1 <= x <= 1000, and 1 <= y <= 1000. -/
  theorem spec_2 (n x y : Std.I64)
      (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n x y = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n x y : Std.I64)
        (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n x y = ok r) := by
    sorry

  /-- For every valid input, let T(n,x,y) be the exact number of events, i.e. T(n,x,y) = sum over all functions f from {0,...,n-1} to {0,...,x-1} of y^{|image(f)|}, where |image(f)| is the number of nonempty stages. Then x*y <= T(n,x,y) <= (x*y)^n. In particular, the returned r is the residue modulo M of an integer satisfying these bounds.
    Preconditions: 1 <= n <= 1000, 1 <= x <= 1000, 1 <= y <= 1000, and M = 1000000007. -/
  theorem spec_3 (n x y r : Std.I64)
      (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
      (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r) :
      x.val.toNat * y.val.toNat
          ≤ Tevents n.val.toNat x.val.toNat y.val.toNat ∧
        Tevents n.val.toNat x.val.toNat y.val.toNat
          ≤ (x.val.toNat * y.val.toNat) ^ n.val.toNat ∧
        IsResidue (Tevents n.val.toNat x.val.toNat y.val.toNat : ℤ) r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n x y r : Std.I64)
        (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
        (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r), x.val.toNat * y.val.toNat
            ≤ Tevents n.val.toNat x.val.toNat y.val.toNat ∧
          Tevents n.val.toNat x.val.toNat y.val.toNat
            ≤ (x.val.toNat * y.val.toNat) ^ n.val.toNat ∧
          IsResidue (Tevents n.val.toNat x.val.toNat y.val.toNat : ℤ) r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = x*y.
    Preconditions: n = 1, 1 <= x <= 1000, 1 <= y <= 1000, and M = 1000000007. -/
  theorem spec_4 (n x y r : Std.I64)
      (hn : n.val = 1)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
      (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r) :
      r.val = x.val * y.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n x y r : Std.I64)
        (hn : n.val = 1)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
        (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r), r.val = x.val * y.val) := by
    sorry

  /-- Whenever the function returns a result r, r = y.
    Preconditions: x = 1, 1 <= n <= 1000, 1 <= y <= 1000, and M = 1000000007. -/
  theorem spec_5 (n x y r : Std.I64)
      (hx : x.val = 1)
      (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
      (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r) :
      r.val = y.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n x y r : Std.I64)
        (hx : x.val = 1)
        (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
        (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r), r.val = y.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < M and r == x^n (mod M).
    Preconditions: y = 1, 1 <= n <= 1000, 1 <= x <= 1000, and M = 1000000007. -/
  theorem spec_6 (n x y r : Std.I64)
      (hy : y.val = 1)
      (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
      (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r) :
      IsResidue (x.val ^ n.val.toNat) r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n x y r : Std.I64)
        (hy : y.val = 1)
        (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
        (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r), IsResidue (x.val ^ n.val.toNat) r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < M and r == x*y + x*(x-1)*y^2 (mod M).
    Preconditions: n = 2, 1 <= x <= 1000, 1 <= y <= 1000, and M = 1000000007. -/
  theorem spec_7 (n x y r : Std.I64)
      (hn : n.val = 2)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
      (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r) :
      IsResidue (x.val * y.val + x.val * (x.val - 1) * y.val ^ 2) r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n x y r : Std.I64)
        (hn : n.val = 2)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
        (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r), IsResidue (x.val * y.val + x.val * (x.val - 1) * y.val ^ 2) r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < M and r == 2*y + (2^n - 2)*y^2 (mod M).
    Preconditions: x = 2, 1 <= n <= 1000, 1 <= y <= 1000, and M = 1000000007. -/
  theorem spec_8 (n x y r : Std.I64)
      (hx : x.val = 2)
      (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
      (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r) :
      IsResidue (2 * y.val + (2 ^ n.val.toNat - 2) * y.val ^ 2) r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n x y r : Std.I64)
        (hx : x.val = 2)
        (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
        (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r), IsResidue (2 * y.val + (2 ^ n.val.toNat - 2) * y.val ^ 2) r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < M and r == x*y + 3*x*(x-1)*y^2 + x*(x-1)*(x-2)*y^3 (mod M).
    Preconditions: n = 3, 1 <= x <= 1000, 1 <= y <= 1000, and M = 1000000007. -/
  theorem spec_9 (n x y r : Std.I64)
      (hn : n.val = 3)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
      (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r) :
      IsResidue
        (x.val * y.val + 3 * x.val * (x.val - 1) * y.val ^ 2
          + x.val * (x.val - 1) * (x.val - 2) * y.val ^ 3) r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n x y r : Std.I64)
        (hn : n.val = 3)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
        (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r), IsResidue
          (x.val * y.val + 3 * x.val * (x.val - 1) * y.val ^ 2
            + x.val * (x.val - 1) * (x.val - 2) * y.val ^ 3) r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < M and r == 3*y + 3*(2^n - 2)*y^2 + (3^n - 3*2^n + 3)*y^3 (mod M).
    Preconditions: x = 3, 1 <= n <= 1000, 1 <= y <= 1000, and M = 1000000007. -/
  theorem spec_10 (n x y r : Std.I64)
      (hx : x.val = 3)
      (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
      (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r) :
      IsResidue
        (3 * y.val + 3 * (2 ^ n.val.toNat - 2) * y.val ^ 2
          + (3 ^ n.val.toNat - 3 * 2 ^ n.val.toNat + 3) * y.val ^ 3) r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n x y r : Std.I64)
        (hx : x.val = 3)
        (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
        (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r), IsResidue
          (3 * y.val + 3 * (2 ^ n.val.toNat - 2) * y.val ^ 2
            + (3 ^ n.val.toNat - 3 * 2 ^ n.val.toNat + 3) * y.val ^ 3) r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < M and r == sum_{i=1}^{x} C(x,i) * i^n * y^i * (1-y)^{x-i} (mod M).
    Preconditions: 1 <= n <= 1000, 1 <= x <= 1000, 1 <= y <= 1000, M = 1000000007, and C(x,i)=x!/(i!(x-i)!). Interpret 0^0 as 1. -/
  theorem spec_11 (n x y r : Std.I64)
      (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
      (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r) :
      IsResidue (Tbin n.val.toNat x.val.toNat y.val.toNat) r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n x y r : Std.I64)
        (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
        (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r), IsResidue (Tbin n.val.toNat x.val.toNat y.val.toNat) r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < M and r == sum over all set partitions P of {0,...,n-1} of (x)_{|P|} * y^{|P|} (mod M), where |P| is the number of blocks of P.
    Preconditions: 1 <= n <= 1000, 1 <= x <= 1000, 1 <= y <= 1000, and M = 1000000007. For m >= 0 let (x)_m = x(x-1)...(x-m+1), with (x)_0=1. -/
  theorem spec_12 (n x y r : Std.I64)
      (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
      (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
      (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
      (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r) :
      IsResidue (Tpart n.val.toNat x.val.toNat y.val.toNat : ℤ) r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n x y r : Std.I64)
        (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000)
        (hx : 1 ≤ x.val) (hx' : x.val ≤ 1000)
        (hy : 1 ≤ y.val) (hy' : y.val ≤ 1000)
        (hr : Aegis.NumberOfWays.number_of_ways n x y = ok r), IsResidue (Tpart n.val.toNat x.val.toNat y.val.toNat : ℤ) r.val) := by
    sorry

  end AegisSpec.NumberOfWays
