import Aegis.NumWays.Code.Funs

/-!
# Specifications of `Aegis.NumWays.num_ways`

LeetCode problem `paint-fence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumWays

  abbrev Painting (n k : ℕ) : Type := Fin n → Fin k

  def HasTriple {n k : ℕ} (c : Painting n k) : Prop :=
    ∃ i : Fin (n - 2),
      c ⟨i.val, by omega⟩ = c ⟨i.val + 1, by omega⟩ ∧
      c ⟨i.val + 1, by omega⟩ = c ⟨i.val + 2, by omega⟩

  def Valid {n k : ℕ} (c : Painting n k) : Prop := ¬ HasTriple c

  noncomputable def W (n k : ℕ) : ℕ := by
    classical
    exact (Finset.univ.filter (fun c : Painting n k => Valid c)).card

  def fib : ℕ → ℕ
    | 0 => 0
    | 1 => 1
    | m + 2 => fib (m + 1) + fib m

  /-- Let a painting be a function c from {0,1,...,n-1} to a set of k colors, identified with {1,2,...,k}; it is valid exactly when for every i with 0 <= i <= n-3, it is not the case that c[i] = c[i+1] = c[i+2]. Let W(n,k) be the number of valid paintings. The function returns a result r and r = W(n,k).
    Preconditions: 1 <= n <= 50, 1 <= k <= 100000, and W(n,k) is in [0, 2^31 - 1], where W(n,k) is the number of color assignments c: {0,...,n-1} -> {1,...,k} such that no i with 0 <= i <= n-3 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_1 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64,
        Aegis.NumWays.num_ways n k = ok r ∧ r.val = (W n.toNat k.toNat : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64,
          Aegis.NumWays.num_ways n k = ok r ∧ r.val = (W n.toNat k.toNat : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, or panic.
    Preconditions: 1 <= n <= 50, 1 <= k <= 100000, and W(n,k) is in [0, 2^31 - 1], where W(n,k) is the number of color assignments c: {0,...,n-1} -> {1,...,k} such that no i with 0 <= i <= n-3 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_2 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= 2^31 - 1.
    Preconditions: 1 <= n <= 50, 1 <= k <= 100000, and W(n,k) is in [0, 2^31 - 1], where W(n,k) is the number of color assignments c: {0,...,n-1} -> {1,...,k} such that no i with 0 <= i <= n-3 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_3 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64,
        Aegis.NumWays.num_ways n k = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 2 ^ 31 - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64,
          Aegis.NumWays.num_ways n k = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 2 ^ 31 - 1) := by
    sorry

  /-- If n = 1, the function returns a result r and r = k.
    Preconditions: n = 1, 1 <= k <= 100000, and W(1,k) is in [0, 2^31 - 1], where W(1,k) is the number of color assignments c: {0} -> {1,...,k} such that no i with 0 <= i <= -2 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_4 (n k : Aeneas.Std.I64) (hn : n.val = 1) (hk1 : 1 ≤ k.val)
      (hk100000 : k.val ≤ 100000) (hW : W 1 k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r ∧ r.val = k.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn : n.val = 1) (hk1 : 1 ≤ k.val)
        (hk100000 : k.val ≤ 100000) (hW : W 1 k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r ∧ r.val = k.val) := by
    sorry

  /-- If n = 2, the function returns a result r and r = k*k.
    Preconditions: n = 2, 1 <= k <= 100000, and W(2,k) is in [0, 2^31 - 1], where W(2,k) is the number of color assignments c: {0,1} -> {1,...,k} such that no i with 0 <= i <= -1 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_5 (n k : Aeneas.Std.I64) (hn : n.val = 2) (hk1 : 1 ≤ k.val)
      (hk100000 : k.val ≤ 100000) (hW : W 2 k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r ∧ r.val = k.val * k.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn : n.val = 2) (hk1 : 1 ≤ k.val)
        (hk100000 : k.val ≤ 100000) (hW : W 2 k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r ∧ r.val = k.val * k.val) := by
    sorry

  /-- If n = 3, the function returns a result r and r = k^3 - k.
    Preconditions: n = 3, 1 <= k <= 100000, and W(3,k) is in [0, 2^31 - 1], where W(3,k) is the number of color assignments c: {0,1,2} -> {1,...,k} such that no i with 0 <= i <= 0 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_6 (n k : Aeneas.Std.I64) (hn : n.val = 3) (hk1 : 1 ≤ k.val)
      (hk100000 : k.val ≤ 100000) (hW : W 3 k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r ∧ r.val = k.val ^ 3 - k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn : n.val = 3) (hk1 : 1 ≤ k.val)
        (hk100000 : k.val ≤ 100000) (hW : W 3 k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r ∧ r.val = k.val ^ 3 - k.val) := by
    sorry

  /-- If n = 4, the function returns a result r and r = k^4 - 2*k^2 + k.
    Preconditions: n = 4, 1 <= k <= 100000, and W(4,k) is in [0, 2^31 - 1], where W(4,k) is the number of color assignments c: {0,1,2,3} -> {1,...,k} such that no i with 0 <= i <= 1 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_7 (n k : Aeneas.Std.I64) (hn : n.val = 4) (hk1 : 1 ≤ k.val)
      (hk100000 : k.val ≤ 100000) (hW : W 4 k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64,
        Aegis.NumWays.num_ways n k = ok r ∧ r.val = k.val ^ 4 - 2 * k.val ^ 2 + k.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn : n.val = 4) (hk1 : 1 ≤ k.val)
        (hk100000 : k.val ≤ 100000) (hW : W 4 k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64,
          Aegis.NumWays.num_ways n k = ok r ∧ r.val = k.val ^ 4 - 2 * k.val ^ 2 + k.val) := by
    sorry

  /-- If n >= 3, the function returns a result r and r = (k - 1)*(W(n-1,k) + W(n-2,k)).
    Preconditions: 1 <= n <= 50, n >= 3, 1 <= k <= 100000, and W(n,k) is in [0, 2^31 - 1], where W(n,k) is the number of color assignments c: {0,...,n-1} -> {1,...,k} such that no i with 0 <= i <= n-3 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_8 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hn3 : 3 ≤ n.val) (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000)
      (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64,
        Aegis.NumWays.num_ways n k = ok r ∧
          r.val = (k.val - 1) * (((W (n.toNat - 1) k.toNat : ℕ) : ℤ) +
            ((W (n.toNat - 2) k.toNat : ℕ) : ℤ)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hn3 : 3 ≤ n.val) (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000)
        (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64,
          Aegis.NumWays.num_ways n k = ok r ∧
            r.val = (k.val - 1) * (((W (n.toNat - 1) k.toNat : ℕ) : ℤ) +
              ((W (n.toNat - 2) k.toNat : ℕ) : ℤ))) := by
    sorry

  /-- If k = 2, the function returns a result r and r = 2*F_{n+1}, where F_1 = 1, F_2 = 1, and F_m = F_{m-1} + F_{m-2} for m >= 3.
    Preconditions: 1 <= n <= 50, k = 2, and W(n,2) is in [0, 2^31 - 1], where W(n,2) is the number of color assignments c: {0,...,n-1} -> {1,2} such that no i with 0 <= i <= n-3 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_9 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hk : k.val = 2) (hW : W n.toNat 2 ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64,
        Aegis.NumWays.num_ways n k = ok r ∧ r.val = 2 * (fib (n.toNat + 1) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hk : k.val = 2) (hW : W n.toNat 2 ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64,
          Aegis.NumWays.num_ways n k = ok r ∧ r.val = 2 * (fib (n.toNat + 1) : ℤ)) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if k = 1 and n >= 3.
    Preconditions: 1 <= n <= 50, 1 <= k <= 100000, and W(n,k) is in [0, 2^31 - 1], where W(n,k) is the number of color assignments c: {0,...,n-1} -> {1,...,k} such that no i with 0 <= i <= n-3 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_10 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64,
        Aegis.NumWays.num_ways n k = ok r ∧ (r.val = 0 ↔ k.val = 1 ∧ 3 ≤ n.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64,
          Aegis.NumWays.num_ways n k = ok r ∧ (r.val = 0 ↔ k.val = 1 ∧ 3 ≤ n.val)) := by
    sorry

  /-- If k >= 2, the function returns a result r and r >= k.
    Preconditions: 1 <= n <= 50, 2 <= k <= 100000, and W(n,k) is in [0, 2^31 - 1], where W(n,k) is the number of color assignments c: {0,...,n-1} -> {1,...,k} such that no i with 0 <= i <= n-3 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_11 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hk2 : 2 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r ∧ k.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hk2 : 2 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r ∧ k.val ≤ r.val) := by
    sorry

  /-- The function returns a result r and there exists an integer m such that r = k*m.
    Preconditions: 1 <= n <= 50, 1 <= k <= 100000, and W(n,k) is in [0, 2^31 - 1], where W(n,k) is the number of color assignments c: {0,...,n-1} -> {1,...,k} such that no i with 0 <= i <= n-3 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_12 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64,
        Aegis.NumWays.num_ways n k = ok r ∧ ∃ m : ℤ, r.val = k.val * m := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64,
          Aegis.NumWays.num_ways n k = ok r ∧ ∃ m : ℤ, r.val = k.val * m) := by
    sorry

  /-- If n >= 3 and k >= 2, the function returns a result r and there exists an integer m such that r = k*(k - 1)*m.
    Preconditions: 1 <= n <= 50, n >= 3, 2 <= k <= 100000, and W(n,k) is in [0, 2^31 - 1], where W(n,k) is the number of color assignments c: {0,...,n-1} -> {1,...,k} such that no i with 0 <= i <= n-3 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_13 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hn3 : 3 ≤ n.val) (hk2 : 2 ≤ k.val) (hk100000 : k.val ≤ 100000)
      (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64,
        Aegis.NumWays.num_ways n k = ok r ∧ ∃ m : ℤ, r.val = k.val * (k.val - 1) * m := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hn3 : 3 ≤ n.val) (hk2 : 2 ≤ k.val) (hk100000 : k.val ≤ 100000)
        (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64,
          Aegis.NumWays.num_ways n k = ok r ∧ ∃ m : ℤ, r.val = k.val * (k.val - 1) * m) := by
    sorry

  /-- The function returns a result r and r <= k^n, where k^n is interpreted as a mathematical integer power, not as machine arithmetic.
    Preconditions: 1 <= n <= 50, 1 <= k <= 100000, and W(n,k) is in [0, 2^31 - 1], where W(n,k) is the number of color assignments c: {0,...,n-1} -> {1,...,k} such that no i with 0 <= i <= n-3 has c[i] = c[i+1] = c[i+2]. -/
  theorem spec_14 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1) :
      ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r ∧ r.val ≤ k.val ^ n.toNat := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk100000 : k.val ≤ 100000) (hW : W n.toNat k.toNat ≤ 2 ^ 31 - 1), ∃ r : Aeneas.Std.I64, Aegis.NumWays.num_ways n k = ok r ∧ r.val ≤ k.val ^ n.toNat) := by
    sorry

  end AegisSpec.NumWays
