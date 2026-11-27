import Aegis.IntegerBreak.Code.Funs

/-!
# Specifications of `Aegis.IntegerBreak.integer_break`

LeetCode problem `integer-break`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IntegerBreak

open Aegis.IntegerBreak

def IsDecomposition (n : ℤ) (l : List ℤ) : Prop :=
  2 ≤ l.length ∧ (∀ a ∈ l, 0 < a) ∧ l.sum = n

def IsMaxProduct (n r : ℤ) : Prop :=
  (∃ l : List ℤ, IsDecomposition n l ∧ l.prod = r) ∧
    ∀ l : List ℤ, IsDecomposition n l → l.prod ≤ r

def ceilDiv3 (n : ℤ) : ℕ := (n + 2).toNat / 3

theorem ceilDiv3_spec (n : ℤ) (hn : 0 ≤ n) :
    3 * (ceilDiv3 n : ℤ) ≥ n ∧ ∀ c : ℤ, 3 * c ≥ n → (ceilDiv3 n : ℤ) ≤ c := by
  have hmod : ((n + 2).toNat % 3 : ℤ) < 3 := by
    have h := Nat.mod_lt (n + 2).toNat (by decide : 0 < 3)
    omega
  have hdiv : 3 * (((n + 2).toNat / 3) : ℤ) + ((n + 2).toNat % 3 : ℤ) = n + 2 := by
    have h := Nat.div_add_mod (n + 2).toNat 3
    have h' : 3 * ((n + 2).toNat / 3) + (n + 2).toNat % 3 = (n + 2).toNat := by
      simpa [Nat.mul_comm] using h
    omega
  unfold ceilDiv3
  constructor <;> omega

/-- For every such n, integer_break n returns a result r, and r equals the maximum, over all integers k ≥ 2 and all k-tuples (a_1, ..., a_k) of positive integers with a_1 + ... + a_k = n, of the product a_1 * ... * a_k.
  Preconditions: n is an integer of Lean type Std.I64 whose value satisfies 2 ≤ n ≤ 58. -/
theorem spec_1 (n : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58) :
    ∃ r : I64, integer_break n = ok r ∧ IsMaxProduct n.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58), ∃ r : I64, integer_break n = ok r ∧ IsMaxProduct n.val r.val) := by
  sorry

/-- For every n with 2 ≤ n ≤ 58, the call integer_break n returns a result (there exists an I64 value r with integer_break n = Result.ok r); it does not fail by overflow, panic, or out-of-bounds access.
  Preconditions: n is an integer of Lean type Std.I64 with 2 ≤ n ≤ 58. -/
theorem spec_2 (n : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58) :
    ∃ r : I64, integer_break n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58), ∃ r : I64, integer_break n = ok r) := by
  sorry

/-- For every n with 2 ≤ n ≤ 58, whenever integer_break n returns a result r, there exist an integer k ≥ 2 and positive integers a_1, ..., a_k such that a_1 + ... + a_k = n and a_1 * ... * a_k = r.
  Preconditions: n is an integer of Lean type Std.I64 with 2 ≤ n ≤ 58. -/
theorem spec_3 (n r : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r) :
    ∃ l : List ℤ, IsDecomposition n.val l ∧ l.prod = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n r : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r), ∃ l : List ℤ, IsDecomposition n.val l ∧ l.prod = r.val) := by
  sorry

/-- For every n with 2 ≤ n ≤ 58, whenever integer_break n returns a result r, for every integer k ≥ 2 and every k-tuple (a_1, ..., a_k) of positive integers with a_1 + ... + a_k = n, the product a_1 * ... * a_k is at most r.
  Preconditions: n is an integer of Lean type Std.I64 with 2 ≤ n ≤ 58. -/
theorem spec_4 (n r : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r) :
    ∀ l : List ℤ, IsDecomposition n.val l → l.prod ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n r : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r), ∀ l : List ℤ, IsDecomposition n.val l → l.prod ≤ r.val) := by
  sorry

/-- For every n with 2 ≤ n ≤ 58, whenever integer_break n returns a result r, r ≥ n - 1.
  Preconditions: n is an integer of Lean type Std.I64 with 2 ≤ n ≤ 58. -/
theorem spec_5 (n r : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r) : n.val - 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n r : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r), n.val - 1 ≤ r.val) := by
  sorry

/-- For every n with 2 ≤ n ≤ 58, whenever integer_break n returns a result r, r ≥ 2 * (n - 2).
  Preconditions: n is an integer of Lean type Std.I64 with 2 ≤ n ≤ 58. -/
theorem spec_6 (n r : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r) : 2 * (n.val - 2) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n r : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r), 2 * (n.val - 2) ≤ r.val) := by
  sorry

/-- For every n with 2 ≤ n ≤ 58, whenever integer_break n returns a result r, r ≤ 3^c, where c is the smallest integer with 3*c ≥ n (so c = ceil(n/3)).
  Preconditions: n is an integer of Lean type Std.I64 with 2 ≤ n ≤ 58. -/
theorem spec_7 (n r : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r) : r.val ≤ 3 ^ ceilDiv3 n.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n r : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r), r.val ≤ 3 ^ ceilDiv3 n.val) := by
  sorry

/-- Whenever integer_break 2 returns a result r, r = 1.
  Preconditions: n is an integer of Lean type Std.I64 with n = 2. -/
theorem spec_8 (n r : I64) (hn : n.val = 2) (hr : integer_break n = ok r) :
    r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n r : I64) (hn : n.val = 2) (hr : integer_break n = ok r), r.val = 1) := by
  sorry

/-- Whenever integer_break 3 returns a result r, r = 2.
  Preconditions: n is an integer of Lean type Std.I64 with n = 3. -/
theorem spec_9 (n r : I64) (hn : n.val = 3) (hr : integer_break n = ok r) :
    r.val = 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n r : I64) (hn : n.val = 3) (hr : integer_break n = ok r), r.val = 2) := by
  sorry

/-- Whenever integer_break 4 returns a result r, r = 4.
  Preconditions: n is an integer of Lean type Std.I64 with n = 4. -/
theorem spec_10 (n r : I64) (hn : n.val = 4) (hr : integer_break n = ok r) :
    r.val = 4 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n r : I64) (hn : n.val = 4) (hr : integer_break n = ok r), r.val = 4) := by
  sorry

/-- Whenever integer_break n returns a result r and integer_break (n + 1) returns a result s, we have r < s.
  Preconditions: n is an integer of Lean type Std.I64 with 2 ≤ n < 58. -/
theorem spec_11 (n n1 r s : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val < 58)
    (hn1 : n1.val = n.val + 1)
    (hr : integer_break n = ok r) (hs : integer_break n1 = ok s) : r.val < s.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n n1 r s : I64) (hn2 : 2 ≤ n.val) (hn58 : n.val < 58)
    (hn1 : n1.val = n.val + 1)
    (hr : integer_break n = ok r) (hs : integer_break n1 = ok s), r.val < s.val) := by
  sorry

/-- Whenever integer_break n returns a result r, 3 divides r (there exists an integer q with r = 3*q).
  Preconditions: n is an integer of Lean type Std.I64 with 5 ≤ n ≤ 58. -/
theorem spec_12 (n r : I64) (hn5 : 5 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r) : ∃ q : ℤ, r.val = 3 * q := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n r : I64) (hn5 : 5 ≤ n.val) (hn58 : n.val ≤ 58)
    (hr : integer_break n = ok r), ∃ q : ℤ, r.val = 3 * q) := by
  sorry

/-- Whenever integer_break n returns a result r and integer_break (n - 3) returns a result t, we have r = 3 * t.
  Preconditions: n is an integer of Lean type Std.I64 with 7 ≤ n ≤ 58. -/
theorem spec_13 (n n3 r t : I64) (hn7 : 7 ≤ n.val) (hn58 : n.val ≤ 58)
    (hn3 : n3.val = n.val - 3)
    (hr : integer_break n = ok r) (ht : integer_break n3 = ok t) : r.val = 3 * t.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n n3 r t : I64) (hn7 : 7 ≤ n.val) (hn58 : n.val ≤ 58)
    (hn3 : n3.val = n.val - 3)
    (hr : integer_break n = ok r) (ht : integer_break n3 = ok t), r.val = 3 * t.val) := by
  sorry

end AegisSpec.IntegerBreak
