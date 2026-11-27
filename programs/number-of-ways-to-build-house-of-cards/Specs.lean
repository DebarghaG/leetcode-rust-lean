import Aegis.HouseOfCards.Code.Funs

/-!
# Specifications of `Aegis.HouseOfCards.house_of_cards`

LeetCode problem `number-of-ways-to-build-house-of-cards`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.HouseOfCards

  namespace AegisSpec.HouseOfCards

  def rowCost (a : Nat) : Nat := 3 * a - 1

  def adjacentOK : List Nat → Bool
    | [] => true
    | [_] => true
    | a :: b :: rest => decide (b + 1 ≤ a) && adjacentOK (b :: rest)

  def IsValidHouse (n : Nat) (l : List Nat) : Prop :=
    l ≠ [] ∧ l.all (fun a => decide (1 ≤ a)) = true ∧ adjacentOK l = true ∧
      (l.map rowCost).sum = n

  instance instDecidableIsValidHouse (n : Nat) (l : List Nat) : Decidable (IsValidHouse n l) := by
    unfold IsValidHouse
    infer_instance

  def countHousesFuel : Nat → Nat → Nat → Nat
    | 0, r, _ => if r = 0 then 1 else 0
    | fuel + 1, r, maxA =>
      (if r = 0 then 1 else 0) +
        ((List.range maxA).map fun a =>
          if rowCost (a + 1) ≤ r then countHousesFuel fuel (r - rowCost (a + 1)) a else 0).sum

  def numHouses (n : Nat) : Nat :=
    ((List.range n).map fun a =>
      if rowCost (a + 1) ≤ n then countHousesFuel (n + 1) (n - rowCost (a + 1)) a else 0).sum

  def numHouseSets (n : Nat) : Nat :=
    ((Finset.Icc 1 n).powerset.filter fun S =>
      S.Nonempty ∧ 3 * ((S.sum fun a => a : Nat) : Int) - (S.card : Int) = (n : Int)).card

  /-- The function returns a result r, and r is the number of finite sequences (a_0, a_1, ..., a_{m-1}) such that m >= 1; every a_i is a positive integer; for every i with 0 <= i < m-1, a_{i+1} <= a_i - 1; and sum_{i=0}^{m-1} (3*a_i - 1) = n. The sequence lists the numbers of triangles in the rows from bottom (i=0) to top (i=m-1). A row with a_i triangles contributes 2*a_i cards for its triangles plus a_i - 1 horizontal cards between adjacent triangles, for a total of 3*a_i - 1 cards.
    Preconditions: n is an i64 satisfying 1 <= n <= 500. -/
  theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn500 : n.val ≤ 500) :
      ∃ r : Std.I64, house_of_cards n = ok r ∧ r.val = (numHouses n.val.toNat : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn500 : n.val ≤ 500), ∃ r : Std.I64, house_of_cards n = ok r ∧ r.val = (numHouses n.val.toNat : Int)) := by
    sorry

  /-- For every n with 1 <= n <= 500, the function returns a result (it does not fail, panic, or overflow).
    Preconditions: n is an i64 satisfying 1 <= n <= 500. -/
  theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn500 : n.val ≤ 500) :
      ∃ r : Std.I64, house_of_cards n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn500 : n.val ≤ 500), ∃ r : Std.I64, house_of_cards n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have 0 <= r.
    Preconditions: n is an i64 satisfying 1 <= n <= 500. -/
  theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn500 : n.val ≤ 500) :
      ∀ r : Std.I64, house_of_cards n = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn500 : n.val ≤ 500), ∀ r : Std.I64, house_of_cards n = ok r → 0 ≤ r.val) := by
    sorry

  /-- The function returns 0.
    Preconditions: n = 1. -/
  theorem spec_4 (n : Std.I64) (hn : n.val = 1) :
      house_of_cards n = ok 0#i64 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 1), house_of_cards n = ok 0#i64) := by
    sorry

  /-- The function returns 1.
    Preconditions: n = 2. -/
  theorem spec_5 (n : Std.I64) (hn : n.val = 2) :
      house_of_cards n = ok 1#i64 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 2), house_of_cards n = ok 1#i64) := by
    sorry

  /-- The function returns 2.
    Preconditions: n = 16. -/
  theorem spec_6 (n : Std.I64) (hn : n.val = 16) :
      house_of_cards n = ok 2#i64 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 16), house_of_cards n = ok 2#i64) := by
    sorry

  /-- The function returns 5.
    Preconditions: n = 30. -/
  theorem spec_7 (n : Std.I64) (hn : n.val = 30) :
      house_of_cards n = ok 5#i64 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 30), house_of_cards n = ok 5#i64) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exists at least one finite sequence (a_0, ..., a_{m-1}) satisfying m >= 1, all a_i positive, a_{i+1} <= a_i - 1 for 0 <= i < m-1, and sum_{i=0}^{m-1} (3*a_i - 1) = n.
    Preconditions: n is an i64 satisfying 1 <= n <= 500. -/
  theorem spec_8 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn500 : n.val ≤ 500) :
      ∀ r : Std.I64, house_of_cards n = ok r →
        (0 < r.val ↔ ∃ l : List Nat, IsValidHouse n.val.toNat l) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn500 : n.val ≤ 500), ∀ r : Std.I64, house_of_cards n = ok r →
          (0 < r.val ↔ ∃ l : List Nat, IsValidHouse n.val.toNat l)) := by
    sorry

  /-- The returned value r equals the number of finite nonempty sets S of positive integers such that 3*(sum_{a in S} a) - |S| = n. For each such set S, the corresponding house has one row for each a in S, ordered with the largest a at the bottom; a row contributes 3a - 1 cards.
    Preconditions: n is an i64 satisfying 1 <= n <= 500. -/
  theorem spec_9 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn500 : n.val ≤ 500) :
      ∃ r : Std.I64, house_of_cards n = ok r ∧ r.val = (numHouseSets n.val.toNat : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn500 : n.val ≤ 500), ∃ r : Std.I64, house_of_cards n = ok r ∧ r.val = (numHouseSets n.val.toNat : Int)) := by
    sorry

  end AegisSpec.HouseOfCards
