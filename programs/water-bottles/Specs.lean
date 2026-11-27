import Aegis.NumWaterBottles.Code.Funs

/-!
# Specifications of `Aegis.NumWaterBottles.num_water_bottles`

LeetCode problem `water-bottles`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumWaterBottles

  structure BottleState where
    full : Nat
    empty : Nat

  def initialState (numBottles : I64) : BottleState := ⟨numBottles.val.toNat, 0⟩

  inductive BottleProcess (numExchange : Nat) : BottleState → Nat → BottleState → Prop where
    | nil (s : BottleState) : BottleProcess numExchange s 0 s
    | drink {s : BottleState} (h : 0 < s.full) {n : Nat} {t : BottleState}
        (rest : BottleProcess numExchange ⟨s.full - 1, s.empty + 1⟩ n t) :
        BottleProcess numExchange s (n + 1) t
    | exchange {s : BottleState} (h : numExchange ≤ s.empty) {n : Nat} {t : BottleState}
        (rest : BottleProcess numExchange ⟨s.full + 1, s.empty - numExchange⟩ n t) :
        BottleProcess numExchange s n t

  /-- The function returns a result r and r = numBottles + ((numBottles - 1) div (numExchange - 1)), where div denotes integer division (the floor of the real quotient). Equivalently, r is the maximum number of water bottles that can be drunk starting with numBottles full bottles and no empty bottles, when every exchange of numExchange empty bottles yields one full bottle.
    Preconditions: 1 <= numBottles <= 100 and 2 <= numExchange <= 100, interpreting both parameters as mathematical integers. -/
  theorem spec_1 (numBottles numExchange : I64)
      (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
      (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100) :
      ∃ r : I64,
        Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r ∧
          r.val = numBottles.val + (numBottles.val - 1) / (numExchange.val - 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (numBottles numExchange : I64)
        (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
        (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100), ∃ r : I64,
          Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r ∧
            r.val = numBottles.val + (numBottles.val - 1) / (numExchange.val - 1)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it never fails due to overflow, panic, or out-of-bounds access.
    Preconditions: 1 <= numBottles <= 100 and 2 <= numExchange <= 100, interpreting both parameters as mathematical integers. -/
  theorem spec_2 (numBottles numExchange : I64)
      (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
      (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100) :
      ∃ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (numBottles numExchange : I64)
        (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
        (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100), ∃ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= numBottles.
    Preconditions: 1 <= numBottles <= 100 and 2 <= numExchange <= 100, interpreting both parameters as mathematical integers. -/
  theorem spec_3 (numBottles numExchange : I64)
      (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
      (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100) :
      ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
        numBottles.val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (numBottles numExchange : I64)
        (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
        (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100), ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
          numBottles.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2*numBottles - 1.
    Preconditions: 1 <= numBottles <= 100 and 2 <= numExchange <= 100, interpreting both parameters as mathematical integers. -/
  theorem spec_4 (numBottles numExchange : I64)
      (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
      (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100) :
      ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
        r.val ≤ 2 * numBottles.val - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (numBottles numExchange : I64)
        (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
        (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100), ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
          r.val ≤ 2 * numBottles.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, r >= numBottles + 1.
    Preconditions: 2 <= numExchange <= numBottles <= 100. -/
  theorem spec_5 (numBottles numExchange : I64)
      (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_le : numExchange.val ≤ numBottles.val)
      (h_bottles_hi : numBottles.val ≤ 100) :
      ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
        numBottles.val + 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (numBottles numExchange : I64)
        (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_le : numExchange.val ≤ numBottles.val)
        (h_bottles_hi : numBottles.val ≤ 100), ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
          numBottles.val + 1 ≤ r.val) := by
    sorry

  /-- Whenever both calls return results r1 and r2, respectively, we have r1 <= r2.
    Preconditions: For every b1, b2, e with 1 <= b1 <= b2 <= 100 and 2 <= e <= 100, considering the two calls num_water_bottles(b1,e) and num_water_bottles(b2,e). -/
  theorem spec_6 (b1 b2 e : I64)
      (h_b1_lo : 1 ≤ b1.val) (h_b1_le : b1.val ≤ b2.val) (h_b2_hi : b2.val ≤ 100)
      (h_e_lo : 2 ≤ e.val) (h_e_hi : e.val ≤ 100) :
      ∀ r1 r2 : I64,
        Aegis.NumWaterBottles.num_water_bottles b1 e = ok r1 →
          Aegis.NumWaterBottles.num_water_bottles b2 e = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (b1 b2 e : I64)
        (h_b1_lo : 1 ≤ b1.val) (h_b1_le : b1.val ≤ b2.val) (h_b2_hi : b2.val ≤ 100)
        (h_e_lo : 2 ≤ e.val) (h_e_hi : e.val ≤ 100), ∀ r1 r2 : I64,
          Aegis.NumWaterBottles.num_water_bottles b1 e = ok r1 →
            Aegis.NumWaterBottles.num_water_bottles b2 e = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- Whenever both calls return results r1 and r2, respectively, we have r1 >= r2.
    Preconditions: For every b, e1, e2 with 1 <= b <= 100 and 2 <= e1 <= e2 <= 100, considering the two calls num_water_bottles(b,e1) and num_water_bottles(b,e2). -/
  theorem spec_7 (b e1 e2 : I64)
      (h_b_lo : 1 ≤ b.val) (h_b_hi : b.val ≤ 100)
      (h_e1_lo : 2 ≤ e1.val) (h_e1_le : e1.val ≤ e2.val) (h_e2_hi : e2.val ≤ 100) :
      ∀ r1 r2 : I64,
        Aegis.NumWaterBottles.num_water_bottles b e1 = ok r1 →
          Aegis.NumWaterBottles.num_water_bottles b e2 = ok r2 → r2.val ≤ r1.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (b e1 e2 : I64)
        (h_b_lo : 1 ≤ b.val) (h_b_hi : b.val ≤ 100)
        (h_e1_lo : 2 ≤ e1.val) (h_e1_le : e1.val ≤ e2.val) (h_e2_hi : e2.val ≤ 100), ∀ r1 r2 : I64,
          Aegis.NumWaterBottles.num_water_bottles b e1 = ok r1 →
            Aegis.NumWaterBottles.num_water_bottles b e2 = ok r2 → r2.val ≤ r1.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a finite sequence of legal operations—starting with numBottles full bottles and zero empty bottles, where a drink turns one full bottle into one empty bottle and an exchange consumes exactly numExchange empty bottles to produce one full bottle—that drinks exactly r bottles.
    Preconditions: 1 <= numBottles <= 100 and 2 <= numExchange <= 100, interpreting both parameters as mathematical integers. -/
  theorem spec_8 (numBottles numExchange : I64)
      (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
      (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100) :
      ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
        ∃ s : BottleState,
          BottleProcess numExchange.val.toNat (initialState numBottles) r.val.toNat s := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (numBottles numExchange : I64)
        (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
        (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100), ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
          ∃ s : BottleState,
            BottleProcess numExchange.val.toNat (initialState numBottles) r.val.toNat s) := by
    sorry

  /-- Whenever the function returns a result r, every finite sequence of legal operations starting with numBottles full bottles and zero empty bottles drinks at most r bottles.
    Preconditions: 1 <= numBottles <= 100 and 2 <= numExchange <= 100, interpreting both parameters as mathematical integers. -/
  theorem spec_9 (numBottles numExchange : I64)
      (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
      (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100) :
      ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
        ∀ (s : BottleState) (n : Nat),
          BottleProcess numExchange.val.toNat (initialState numBottles) n s → n ≤ r.val.toNat := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (numBottles numExchange : I64)
        (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
        (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100), ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
          ∀ (s : BottleState) (n : Nat),
            BottleProcess numExchange.val.toNat (initialState numBottles) n s → n ≤ r.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, every legal process that performs exactly r drink operations and then stops ends with exactly ((numBottles - 1) mod (numExchange - 1)) + 1 empty bottles.
    Preconditions: 1 <= numBottles <= 100 and 2 <= numExchange <= 100, interpreting both parameters as mathematical integers. -/
  theorem spec_10 (numBottles numExchange : I64)
      (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
      (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100) :
      ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
        ∀ s : BottleState,
          BottleProcess numExchange.val.toNat (initialState numBottles) r.val.toNat s →
            s.empty = (numBottles.val.toNat - 1) % (numExchange.val.toNat - 1) + 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (numBottles numExchange : I64)
        (h_bottles_lo : 1 ≤ numBottles.val) (h_bottles_hi : numBottles.val ≤ 100)
        (h_exchange_lo : 2 ≤ numExchange.val) (h_exchange_hi : numExchange.val ≤ 100), ∀ r : I64, Aegis.NumWaterBottles.num_water_bottles numBottles numExchange = ok r →
          ∀ s : BottleState,
            BottleProcess numExchange.val.toNat (initialState numBottles) r.val.toNat s →
              s.empty = (numBottles.val.toNat - 1) % (numExchange.val.toNat - 1) + 1) := by
    sorry

  end AegisSpec.NumWaterBottles
