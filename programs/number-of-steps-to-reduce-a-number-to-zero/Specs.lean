import Aegis.NumberOfSteps.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSteps.number_of_steps`

LeetCode problem `number-of-steps-to-reduce-a-number-to-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NumberOfSteps (number_of_steps)

  namespace AegisSpec.NumberOfSteps

  def S (n : Nat) : Nat :=
    if h : n = 0 then 0
    else if n % 2 = 0 then 1 + S (n / 2)
    else 1 + S (n - 1)
  termination_by n
  decreasing_by
    all_goals first
      | exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)
      | exact Nat.sub_lt (Nat.pos_of_ne_zero h) (by norm_num)

  def popcount : Nat → Nat
    | 0 => 0
    | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)

  termination_by n => n
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

  def bitLength (n : Nat) : Nat := Nat.log2 n + 1

  def reduceStep (n : Nat) : Nat := if n % 2 = 0 then n / 2 else n - 1

  def IsReduction (start steps : Nat) (x : Nat → Nat) : Prop :=
    x 0 = start ∧ x steps = 0 ∧
      (∀ j, j < steps → 0 < x j) ∧
      (∀ j, j < steps → x (j + 1) = reduceStep (x j))

  def subtractions (steps : Nat) (x : Nat → Nat) : Nat :=
    ((List.range steps).filter (fun j => decide (x j % 2 = 1))).length

  def divisions (steps : Nat) (x : Nat → Nat) : Nat :=
    ((List.range steps).filter (fun j => decide (x j % 2 = 0))).length

  /-- number_of_steps returns a result r and r equals S(num), where S is defined on nonnegative integers by S(0)=0; for n>0, if n is even then S(n)=1+S(n/2), and if n is odd then S(n)=1+S(n-1). Here n/2 is exact integer division for even n.
    Preconditions: num is an I64 with 0 <= num <= 1000000. -/
  theorem spec_1 (num : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000) :
      ∃ r : I64, number_of_steps num = ok r ∧ r.val = (S num.val.toNat : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000), ∃ r : I64, number_of_steps num = ok r ∧ r.val = (S num.val.toNat : Int)) := by
    sorry

  /-- For every valid num, number_of_steps returns some result r (evaluation is of the form ok r); in particular, it does not overflow, panic, or get stuck.
    Preconditions: num is an I64 with 0 <= num <= 1000000. -/
  theorem spec_2 (num : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000) :
      ∃ r : I64, number_of_steps num = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000), ∃ r : I64, number_of_steps num = ok r) := by
    sorry

  /-- For every valid num, if number_of_steps returns a result r, then r=0 when num=0, and when num>0, r=k+p where k is the unique integer with k>=0 and 2^k <= num < 2^{k+1}, and p is the number of 1-bits in the binary representation of num.
    Preconditions: num is an I64 with 0 <= num <= 1000000. -/
  theorem spec_3 (num r : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000)
      (hres : number_of_steps num = ok r) :
      (num.val = 0 → r.val = 0) ∧
        (0 < num.val →
          r.val = (Nat.log2 num.val.toNat : Int) + (popcount num.val.toNat : Int)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num r : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000)
        (hres : number_of_steps num = ok r), (num.val = 0 → r.val = 0) ∧
          (0 < num.val →
            r.val = (Nat.log2 num.val.toNat : Int) + (popcount num.val.toNat : Int))) := by
    sorry

  /-- For every valid num, if number_of_steps returns a result r, then r >= 0.
    Preconditions: num is an I64 with 0 <= num <= 1000000. -/
  theorem spec_4 (num r : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000)
      (hres : number_of_steps num = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num r : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000)
        (hres : number_of_steps num = ok r), 0 ≤ r.val) := by
    sorry

  /-- For every valid num, if number_of_steps returns a result r, then r <= 38.
    Preconditions: num is an I64 with 0 <= num <= 1000000. -/
  theorem spec_5 (num r : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000)
      (hres : number_of_steps num = ok r) :
      r.val ≤ 38 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num r : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000)
        (hres : number_of_steps num = ok r), r.val ≤ 38) := by
    sorry

  /-- number_of_steps returns a result r and r=0.
    Preconditions: num = 0. -/
  theorem spec_6 (num : I64) (hnum : num.val = 0) :
      ∃ r : I64, number_of_steps num = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : I64) (hnum : num.val = 0), ∃ r : I64, number_of_steps num = ok r ∧ r.val = 0) := by
    sorry

  /-- number_of_steps returns a result r and r=1.
    Preconditions: num = 1. -/
  theorem spec_7 (num : I64) (hnum : num.val = 1) :
      ∃ r : I64, number_of_steps num = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : I64) (hnum : num.val = 1), ∃ r : I64, number_of_steps num = ok r ∧ r.val = 1) := by
    sorry

  /-- For every such num, if number_of_steps returns a result r, then r > 0.
    Preconditions: 0 < num <= 1000000. -/
  theorem spec_8 (num r : I64) (hnum_pos : 0 < num.val) (hnum_le : num.val ≤ 1000000)
      (hres : number_of_steps num = ok r) :
      0 < r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num r : I64) (hnum_pos : 0 < num.val) (hnum_le : num.val ≤ 1000000)
        (hres : number_of_steps num = ok r), 0 < r.val) := by
    sorry

  /-- If number_of_steps returns a result r, then r = 1 + S(num/2), where S is defined by S(0)=0; for n>0, S(n)=1+S(n/2) if n is even, and S(n)=1+S(n-1) if n is odd.
    Preconditions: 0 < num <= 1000000 and num is even. -/
  theorem spec_9 (num r : I64) (hnum_pos : 0 < num.val) (hnum_le : num.val ≤ 1000000)
      (heven : num.val % 2 = 0) (hres : number_of_steps num = ok r) :
      r.val = 1 + (S (num.val.toNat / 2) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num r : I64) (hnum_pos : 0 < num.val) (hnum_le : num.val ≤ 1000000)
        (heven : num.val % 2 = 0) (hres : number_of_steps num = ok r), r.val = 1 + (S (num.val.toNat / 2) : Int)) := by
    sorry

  /-- If number_of_steps returns a result r, then r = 2 + S((num-1)/2), where S is defined by S(0)=0; for n>0, S(n)=1+S(n/2) if n is even, and S(n)=1+S(n-1) if n is odd.
    Preconditions: 3 <= num <= 1000000 and num is odd. -/
  theorem spec_10 (num r : I64) (hnum_ge : 3 ≤ num.val) (hnum_le : num.val ≤ 1000000)
      (hodd : num.val % 2 = 1) (hres : number_of_steps num = ok r) :
      r.val = 2 + (S ((num.val - 1).toNat / 2) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num r : I64) (hnum_ge : 3 ≤ num.val) (hnum_le : num.val ≤ 1000000)
        (hodd : num.val % 2 = 1) (hres : number_of_steps num = ok r), r.val = 2 + (S ((num.val - 1).toNat / 2) : Int)) := by
    sorry

  /-- number_of_steps returns a result r and r = k+1.
    Preconditions: num = 2^k for some integer k with 0 <= k <= 19. -/
  theorem spec_11 (num : I64) (k : Nat) (hk_le : k ≤ 19) (hnum : num.val = 2 ^ k) :
      ∃ r : I64, number_of_steps num = ok r ∧ r.val = (k : Int) + 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num : I64) (k : Nat) (hk_le : k ≤ 19) (hnum : num.val = 2 ^ k), ∃ r : I64, number_of_steps num = ok r ∧ r.val = (k : Int) + 1) := by
    sorry

  /-- number_of_steps returns a result r and r = 2*k - 1.
    Preconditions: num = 2^k - 1 for some integer k with 1 <= k <= 19. -/
  theorem spec_12 (num : I64) (k : Nat) (hk_ge : 1 ≤ k) (hk_le : k ≤ 19)
      (hnum : num.val = 2 ^ k - 1) :
      ∃ r : I64, number_of_steps num = ok r ∧ r.val = 2 * (k : Int) - 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num : I64) (k : Nat) (hk_ge : 1 ≤ k) (hk_le : k ≤ 19)
        (hnum : num.val = 2 ^ k - 1), ∃ r : I64, number_of_steps num = ok r ∧ r.val = 2 * (k : Int) - 1) := by
    sorry

  /-- For every such num, if number_of_steps returns a result r, then r <= 2*b - 1, where b is the number of bits in the binary representation of num (the unique integer b>=1 with 2^{b-1} <= num < 2^b).
    Preconditions: 0 < num <= 1000000. -/
  theorem spec_13 (num r : I64) (hnum_pos : 0 < num.val) (hnum_le : num.val ≤ 1000000)
      (hres : number_of_steps num = ok r) :
      r.val ≤ 2 * (bitLength num.val.toNat : Int) - 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num r : I64) (hnum_pos : 0 < num.val) (hnum_le : num.val ≤ 1000000)
        (hres : number_of_steps num = ok r), r.val ≤ 2 * (bitLength num.val.toNat : Int) - 1) := by
    sorry

  /-- number_of_steps returns a result r and there exists a sequence x_0,...,x_r of nonnegative integers such that x_0=num, x_r=0, x_j>0 for every j with 0<=j<r, and for every j with 0<=j<r, x_{j+1}=x_j/2 if x_j is even and x_{j+1}=x_j-1 if x_j is odd.
    Preconditions: num is an I64 with 0 <= num <= 1000000. -/
  theorem spec_14 (num : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000) :
      ∃ r : I64, number_of_steps num = ok r ∧
        ∃ x : Nat → Nat, IsReduction num.val.toNat r.val.toNat x := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (num : I64) (hnum_ge : 0 ≤ num.val) (hnum_le : num.val ≤ 1000000), ∃ r : I64, number_of_steps num = ok r ∧
          ∃ x : Nat → Nat, IsReduction num.val.toNat r.val.toNat x) := by
    sorry

  /-- If number_of_steps returns a result r, then the reduction process starting at num reaches 0 for the first time after r steps, and among these r steps exactly p are subtractions (applied when the current value is odd) and exactly k are divisions by 2 (applied when the current value is positive and even), where k is the unique integer with 2^k <= num < 2^{k+1} and p is the number of 1-bits in the binary representation of num.
    Preconditions: 0 < num <= 1000000. -/
  theorem spec_15 (num r : I64) (hnum_pos : 0 < num.val) (hnum_le : num.val ≤ 1000000)
      (hres : number_of_steps num = ok r) :
      ∃ x : Nat → Nat, IsReduction num.val.toNat r.val.toNat x ∧
        subtractions r.val.toNat x = popcount num.val.toNat ∧
        divisions r.val.toNat x = Nat.log2 num.val.toNat := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (num r : I64) (hnum_pos : 0 < num.val) (hnum_le : num.val ≤ 1000000)
        (hres : number_of_steps num = ok r), ∃ x : Nat → Nat, IsReduction num.val.toNat r.val.toNat x ∧
          subtractions r.val.toNat x = popcount num.val.toNat ∧
          divisions r.val.toNat x = Nat.log2 num.val.toNat) := by
    sorry

  /-- For every such num, if number_of_steps returns a result r, then r >= b, where b is the bit-length of num (the unique b>=1 with 2^{b-1} <= num < 2^b); equivalently r >= 1 + floor(log2 num), since r = floor(log2 num) + popcount(num) and popcount(num) >= 1.
    Preconditions: 1 <= num <= 1000000 -/
  theorem spec_16 (num r : I64) (hnum_ge : 1 ≤ num.val) (hnum_le : num.val ≤ 1000000)
      (hres : number_of_steps num = ok r) :
      (bitLength num.val.toNat : Int) ≤ r.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (num r : I64) (hnum_ge : 1 ≤ num.val) (hnum_le : num.val ≤ 1000000)
        (hres : number_of_steps num = ok r), (bitLength num.val.toNat : Int) ≤ r.val) := by
    sorry

  end AegisSpec.NumberOfSteps
