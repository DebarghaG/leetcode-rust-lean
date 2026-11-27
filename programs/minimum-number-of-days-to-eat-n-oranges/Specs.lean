import Aegis.MinDays.Code.Funs

/-!
# Specifications of `Aegis.MinDays.min_days`

LeetCode problem `minimum-number-of-days-to-eat-n-oranges`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinDays

  def Step (m k : ℕ) : Prop :=
    0 < m ∧ (k = m - 1 ∨ (m % 2 = 0 ∧ k = m / 2) ∨ (m % 3 = 0 ∧ k = m / 3))

  def Chain (m d : ℕ) (a : ℕ → ℕ) : Prop :=
    a 0 = m ∧ a d = 0 ∧ ∀ j : ℕ, j < d → Step (a j) (a (j + 1))

  def daysSet (m : ℕ) : Set ℕ := {d : ℕ | ∃ a : ℕ → ℕ, Chain m d a}

  noncomputable def D (m : ℕ) : ℕ := sInf (daysSet m)

  noncomputable def succDays (m : ℕ) : Set ℕ :=
    {x : ℕ | x = D (m - 1) ∨ (m % 2 = 0 ∧ x = D (m / 2)) ∨ (m % 3 = 0 ∧ x = D (m / 3))}

  noncomputable def leastC (n : ℕ) : ℕ := sInf {c : ℕ | n ≤ 3 * c}

  /-- The function returns a result r, and r is the minimum number of days needed to eat n oranges: equivalently, r is the least nonnegative integer d for which there exist nonnegative integers a_0,...,a_d with a_0=n, a_d=0, and for every j with 0 <= j < d, a_j > 0 and either a_{j+1}=a_j-1, or a_j is even and a_{j+1}=a_j/2, or a_j is divisible by 3 and a_{j+1}=a_j/3.
    Preconditions: 1 <= n <= 2000000000. -/
  theorem spec_1 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000) :
      ∃ r : Std.I64,
        Aegis.MinDays.min_days n = ok r ∧ r.val = (D n.val.toNat : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000), ∃ r : Std.I64,
          Aegis.MinDays.min_days n = ok r ∧ r.val = (D n.val.toNat : ℤ)) := by
    sorry

  /-- The function min_days n returns a result (it does not fail, panic, or overflow).
    Preconditions: 1 <= n <= 2000000000. -/
  theorem spec_2 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000) :
      ∃ r : Std.I64, Aegis.MinDays.min_days n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000), ∃ r : Std.I64, Aegis.MinDays.min_days n = ok r) := by
    sorry

  /-- Whenever min_days n returns a result r, r >= 1.
    Preconditions: 1 <= n <= 2000000000. -/
  theorem spec_3 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000) :
      ∀ r : Std.I64, Aegis.MinDays.min_days n = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000), ∀ r : Std.I64, Aegis.MinDays.min_days n = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever min_days n returns a result r, r <= n.
    Preconditions: 1 <= n <= 2000000000. -/
  theorem spec_4 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000) :
      ∀ r : Std.I64, Aegis.MinDays.min_days n = ok r → r.val ≤ n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000), ∀ r : Std.I64, Aegis.MinDays.min_days n = ok r → r.val ≤ n.val) := by
    sorry

  /-- Whenever min_days n returns a result r, r <= 2 + c, where c is the least nonnegative integer such that 3*c >= n.
    Preconditions: 1 <= n <= 2000000000. -/
  theorem spec_5 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000) :
      ∀ r : Std.I64,
        Aegis.MinDays.min_days n = ok r → r.val ≤ 2 + (leastC n.val.toNat : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000), ∀ r : Std.I64,
          Aegis.MinDays.min_days n = ok r → r.val ≤ 2 + (leastC n.val.toNat : ℤ)) := by
    sorry

  /-- For every integer k >= 0 such that 3^k <= n, whenever min_days n returns a result r, r >= k+1.
    Preconditions: 1 <= n <= 2000000000. -/
  theorem spec_6 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000) :
      ∀ k : ℕ, (3 : ℤ) ^ k ≤ n.val →
        ∀ r : Std.I64, Aegis.MinDays.min_days n = ok r → (k : ℤ) + 1 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000), ∀ k : ℕ, (3 : ℤ) ^ k ≤ n.val →
          ∀ r : Std.I64, Aegis.MinDays.min_days n = ok r → (k : ℤ) + 1 ≤ r.val) := by
    sorry

  /-- Whenever min_days n returns a result r, r <= 1 + D(n/2), where D(m) is the minimum number of days to eat m oranges under the same three allowed daily actions, with D(0)=0.
    Preconditions: 1 <= n <= 2000000000 and n is even. -/
  theorem spec_7 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000)
      (heven : n.val % 2 = 0) :
      ∀ r : Std.I64,
        Aegis.MinDays.min_days n = ok r → r.val ≤ 1 + (D (n.val.toNat / 2) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000)
        (heven : n.val % 2 = 0), ∀ r : Std.I64,
          Aegis.MinDays.min_days n = ok r → r.val ≤ 1 + (D (n.val.toNat / 2) : ℤ)) := by
    sorry

  /-- Whenever min_days n returns a result r, r <= 1 + D(n/3), where D(m) is the minimum number of days to eat m oranges under the same three allowed daily actions, with D(0)=0.
    Preconditions: 1 <= n <= 2000000000 and n is divisible by 3. -/
  theorem spec_8 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000)
      (hthree : n.val % 3 = 0) :
      ∀ r : Std.I64,
        Aegis.MinDays.min_days n = ok r → r.val ≤ 1 + (D (n.val.toNat / 3) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000)
        (hthree : n.val % 3 = 0), ∀ r : Std.I64,
          Aegis.MinDays.min_days n = ok r → r.val ≤ 1 + (D (n.val.toNat / 3) : ℤ)) := by
    sorry

  /-- Whenever min_days n returns a result r, r = 1 + D(n-1), where D(m) is the minimum number of days to eat m oranges under the same three allowed daily actions, with D(0)=0.
    Preconditions: 1 <= n <= 2000000000, n is odd, and n is not divisible by 3. -/
  theorem spec_9 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000)
      (hodd : n.val % 2 = 1) (hthree : n.val % 3 ≠ 0) :
      ∀ r : Std.I64,
        Aegis.MinDays.min_days n = ok r → r.val = 1 + (D (n.val.toNat - 1) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000)
        (hodd : n.val % 2 = 1) (hthree : n.val % 3 ≠ 0), ∀ r : Std.I64,
          Aegis.MinDays.min_days n = ok r → r.val = 1 + (D (n.val.toNat - 1) : ℤ)) := by
    sorry

  /-- Whenever min_days n returns a result r, r >= 2.
    Preconditions: 2 <= n <= 2000000000. -/
  theorem spec_10 (n : Std.I64) (h1 : 2 ≤ n.val) (h2 : n.val ≤ 2000000000) :
      ∀ r : Std.I64, Aegis.MinDays.min_days n = ok r → 2 ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (h1 : 2 ≤ n.val) (h2 : n.val ≤ 2000000000), ∀ r : Std.I64, Aegis.MinDays.min_days n = ok r → 2 ≤ r.val) := by
    sorry

  /-- Whenever min_days n returns a result r, r = 1 + min({D(n-1)} ∪ ({D(n/2)} if n is even else ∅) ∪ ({D(n/3)} if n is divisible by 3 else ∅)), where D(m) is the minimum number of days to eat m oranges under the same three allowed daily actions, with D(0)=0.
    Preconditions: 1 <= n <= 2000000000. -/
  theorem spec_11 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000) :
      ∀ r : Std.I64,
        Aegis.MinDays.min_days n = ok r →
          r.val = 1 + ((sInf (succDays n.val.toNat) : ℕ) : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2000000000), ∀ r : Std.I64,
          Aegis.MinDays.min_days n = ok r →
            r.val = 1 + ((sInf (succDays n.val.toNat) : ℕ) : ℤ)) := by
    sorry

  end AegisSpec.MinDays
