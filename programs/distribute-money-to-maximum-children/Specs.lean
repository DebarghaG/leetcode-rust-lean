import Aegis.DistMoney.Code.Funs

/-!
# Specifications of `Aegis.DistMoney.dist_money`

LeetCode problem `distribute-money-to-maximum-children`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DistMoney

def Admissible (money children : ℤ) (a : List ℤ) : Prop :=
  a.length = children.toNat ∧ (∀ x ∈ a, 1 ≤ x ∧ x ≠ 4) ∧ a.sum = money

def numEights (a : List ℤ) : ℕ := List.countP (fun x : ℤ => x = 8) a

def HasEight (a : List ℤ) : Prop := ∃ x ∈ a, x = 8

/-- Whenever the function returns a result r, call an assignment admissible if it assigns to the children integer amounts a[0],...,a[children-1] such that a[i] >= 1 and a[i] != 4 for every 0 <= i < children, and the sum of all a[i] equals money. If no admissible assignment exists, then r = -1. Otherwise 0 <= r <= children, and r is the largest integer k for which some admissible assignment has exactly k amounts equal to 8; equivalently, some admissible assignment has exactly r amounts equal to 8 and every admissible assignment has at most r amounts equal to 8.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_1 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r) :
    (¬ (∃ a : List ℤ, Admissible money.val children.val a) → r.val = -1) ∧
      ((∃ a : List ℤ, Admissible money.val children.val a) →
        0 ≤ r.val ∧ r.val ≤ children.val ∧
          (∃ a : List ℤ, Admissible money.val children.val a ∧ (numEights a : ℤ) = r.val) ∧
            (∀ a : List ℤ, Admissible money.val children.val a → (numEights a : ℤ) ≤ r.val)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r), (¬ (∃ a : List ℤ, Admissible money.val children.val a) → r.val = -1) ∧
      ((∃ a : List ℤ, Admissible money.val children.val a) →
        0 ≤ r.val ∧ r.val ≤ children.val ∧
          (∃ a : List ℤ, Admissible money.val children.val a ∧ (numEights a : ℤ) = r.val) ∧
            (∀ a : List ℤ, Admissible money.val children.val a → (numEights a : ℤ) ≤ r.val))) := by
  sorry

/-- The function returns a result r; it does not fail.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_2 (money children : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30) :
    ∃ r : Std.I64, Aegis.DistMoney.dist_money money children = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (money children : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30), ∃ r : Std.I64, Aegis.DistMoney.dist_money money children = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if money < children.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_3 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r) :
    r.val = -1 ↔ money.val < children.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r), r.val = -1 ↔ money.val < children.val) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r <= children.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_4 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r) :
    r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ children.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ children.val)) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, children + 7*r <= money.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_5 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hr_nonneg : 0 ≤ r.val) :
    children.val + 7 * r.val ≤ money.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hr_nonneg : 0 ≤ r.val), children.val + 7 * r.val ≤ money.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there exists an admissible assignment, meaning children integer amounts each at least 1 and none equal to 4 whose sum is money, in which exactly r of the amounts are equal to 8.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_6 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hr_nonneg : 0 ≤ r.val) :
    ∃ a : List ℤ, Admissible money.val children.val a ∧ (numEights a : ℤ) = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hr_nonneg : 0 ≤ r.val), ∃ a : List ℤ, Admissible money.val children.val a ∧ (numEights a : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, every admissible assignment, meaning children integer amounts each at least 1 and none equal to 4 whose sum is money, has at most r amounts equal to 8.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_7 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hr_nonneg : 0 ≤ r.val) :
    ∀ a : List ℤ, Admissible money.val children.val a → (numEights a : ℤ) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hr_nonneg : 0 ≤ r.val), ∀ a : List ℤ, Admissible money.val children.val a → (numEights a : ℤ) ≤ r.val) := by
  sorry

/-- For every integer k with 0 <= k <= children, whenever the function returns a result r on an input satisfying money = children + 7*k, we have r = k.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_8 (k : ℤ) (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hk_lo : 0 ≤ k) (hk_hi : k ≤ children.val)
    (hmoney : money.val = children.val + 7 * k)
    (hr : Aegis.DistMoney.dist_money money children = ok r) :
    r.val = k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (k : ℤ) (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hk_lo : 0 ≤ k) (hk_hi : k ≤ children.val)
    (hmoney : money.val = children.val + 7 * k)
    (hr : Aegis.DistMoney.dist_money money children = ok r), r.val = k) := by
  sorry

/-- Whenever the function returns a result r, r = children if and only if money = 8*children.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_9 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r) :
    r.val = children.val ↔ money.val = 8 * children.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r), r.val = children.val ↔ money.val = 8 * children.val) := by
  sorry

/-- Whenever the function returns a result r, if children <= money < children + 7, then r = 0.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_10 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hrange_lo : children.val ≤ money.val) (hrange_hi : money.val < children.val + 7) :
    r.val = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hrange_lo : children.val ≤ money.val) (hrange_hi : money.val < children.val + 7), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if money = 8*children - 4, then r = children - 2.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_11 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hmoney : money.val = 8 * children.val - 4) :
    r.val = children.val - 2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hmoney : money.val = 8 * children.val - 4), r.val = children.val - 2) := by
  sorry

/-- Whenever the function returns a result r, if money > 8*children, then r = children - 1.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_12 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hmoney : 8 * children.val < money.val) :
    r.val = children.val - 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hmoney : 8 * children.val < money.val), r.val = children.val - 1) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, we have r = 0 if and only if there is no admissible assignment, meaning children integer amounts each at least 1 and none equal to 4 whose sum is money, in which at least one amount equals 8.
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_13 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hr_nonneg : 0 ≤ r.val) :
    r.val = 0 ↔ ¬ (∃ a : List ℤ, Admissible money.val children.val a ∧ HasEight a) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hr_nonneg : 0 ≤ r.val), r.val = 0 ↔ ¬ (∃ a : List ℤ, Admissible money.val children.val a ∧ HasEight a)) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, we have r >= 1 if and only if money >= children + 7 and not (children = 2 and money = 12).
  Preconditions: 1 <= money <= 200 and 2 <= children <= 30. -/
theorem spec_14 (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hr_nonneg : 0 ≤ r.val) :
    1 ≤ r.val ↔
      children.val + 7 ≤ money.val ∧ ¬ (children.val = 2 ∧ money.val = 12) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (money children r : Std.I64)
    (hmoney_lo : 1 ≤ money.val) (hmoney_hi : money.val ≤ 200)
    (hchildren_lo : 2 ≤ children.val) (hchildren_hi : children.val ≤ 30)
    (hr : Aegis.DistMoney.dist_money money children = ok r)
    (hr_nonneg : 0 ≤ r.val), 1 ≤ r.val ↔
      children.val + 7 ≤ money.val ∧ ¬ (children.val = 2 ∧ money.val = 12)) := by
  sorry

end AegisSpec.DistMoney
