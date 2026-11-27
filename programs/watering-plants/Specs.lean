import Aegis.WateringPlants.Code.Funs

/-!
# Specifications of `Aegis.WateringPlants.watering_plants`

LeetCode problem `watering-plants`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.WateringPlants

  open Aeneas Aeneas.Std Result

  def heights (plants : Aeneas.Std.Slice Aeneas.Std.I64) : List Int :=
    plants.val.map (fun p => p.val)

  def blockSum (l : List Int) (s t : Nat) : Int := ((l.drop s).take (t - s)).sum

  def totalSum (l : List Int) : Int := l.sum

  def Adjacent (b : List Nat) (s t : Nat) : Prop :=
    ∃ pre post : List Nat, b = pre ++ s :: t :: post

  def innerSum (b : List Nat) : Int :=
    (((b.drop 1).dropLast).map (fun x => (x : Int))).sum

  def ceilDiv (a b : Int) : Int := (a + b - 1) / b

  def ListInRange (l : List Int) (lo hi : Int) : Prop :=
    ∀ i, (h : i < l.length) → lo ≤ l[i] ∧ l[i] ≤ hi

  def ListLe (l : List Int) (hi : Int) : Prop :=
    ∀ i, (h : i < l.length) → l[i] ≤ hi

  def NeighboursExceed (l : List Int) (cap : Int) : Prop :=
    ∀ i, (h1 : 1 ≤ i) → (h2 : i < l.length) → l[i] + l[i - 1] > cap

  def IsBlockPartition (l : List Int) (cap : Int) (b : List Nat) : Prop :=
    b.head? = some 0 ∧
    b.getLast? = some l.length ∧
    b.Pairwise (· < ·) ∧
    (∀ s t, Adjacent b s t → blockSum l s t ≤ cap) ∧
    (∀ s t, Adjacent b s t → t < l.length → blockSum l s (t + 1) > cap)

  def refillGo (cap : Int) : Nat → Int → List Int → List Nat
    | _, _, [] => []
    | i, w, x :: xs =>
      if w + x > cap then i :: refillGo cap (i + 1) x xs else refillGo cap (i + 1) (w + x) xs

  def refills (l : List Int) (cap : Int) : List Nat := refillGo cap 0 0 l

  def prevRefill (l : List Int) (cap : Int) (i : Nat) : Nat :=
    ((refills l cap).filter (fun j => j < i)).foldr max 0

  def blockBounds (l : List Int) (cap : Int) : List Nat :=
    0 :: (refills l cap ++ [l.length])

  def GoodInput (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64) : Prop :=
    1 ≤ (heights plants).length ∧
    (heights plants).length ≤ 1000 ∧
    ListInRange (heights plants) 1 1000000 ∧
    capacity.val ≤ 1000000000 ∧
    ListLe (heights plants) capacity.val

  /-- Let n = len(plants). Let 0 = b_0 < b_1 < ... < b_m < b_{m+1} = n be the unique increasing sequence such that: (a) for every j with 0 <= j <= m, sum_{i=b_j}^{b_{j+1}-1} plants[i] <= capacity; and (b) for every j with 0 <= j < m, sum_{i=b_j}^{b_{j+1}} plants[i] > capacity. The function returns a result r and r = n + 2 * (sum_{j=1}^{m} b_j), where the sum is 0 if m = 0.
    Preconditions: Let n = len(plants). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= plants[i] <= 1000000; capacity <= 1000000000; and max_{0 <= i < n} plants[i] <= capacity. All indices are 0-based. -/
  theorem spec_1 (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
      (hpre : GoodInput plants capacity) :
      ∃ r : Aeneas.Std.I64,
        Aegis.WateringPlants.watering_plants plants capacity = ok r ∧
          ∃ b : List Nat, IsBlockPartition (heights plants) capacity.val b ∧
            (∀ b' : List Nat, IsBlockPartition (heights plants) capacity.val b' → b' = b) ∧
            r.val = (plants.val.length : Int) + 2 * innerSum b := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
        (hpre : GoodInput plants capacity), ∃ r : Aeneas.Std.I64,
          Aegis.WateringPlants.watering_plants plants capacity = ok r ∧
            ∃ b : List Nat, IsBlockPartition (heights plants) capacity.val b ∧
              (∀ b' : List Nat, IsBlockPartition (heights plants) capacity.val b' → b' = b) ∧
              r.val = (plants.val.length : Int) + 2 * innerSum b) := by
    sorry

  /-- The function returns a result r; in particular, the call does not fail, panic, overflow, or access the slice out of bounds.
    Preconditions: Let n = len(plants). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= plants[i] <= 1000000; capacity <= 1000000000; and max_{0 <= i < n} plants[i] <= capacity. All indices are 0-based. -/
  theorem spec_2 (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
      (hpre : GoodInput plants capacity) :
      ∃ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
        (hpre : GoodInput plants capacity), ∃ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r) := by
    sorry

  /-- Whenever the function returns a result r, n <= r <= n * n.
    Preconditions: Let n = len(plants). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= plants[i] <= 1000000; capacity <= 1000000000; and max_{0 <= i < n} plants[i] <= capacity. All indices are 0-based. -/
  theorem spec_3 (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
      (hpre : GoodInput plants capacity) :
      ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
        (plants.val.length : Int) ≤ r.val ∧
          r.val ≤ (plants.val.length : Int) * (plants.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
        (hpre : GoodInput plants capacity), ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
          (plants.val.length : Int) ≤ r.val ∧
            r.val ≤ (plants.val.length : Int) * (plants.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r - n is even.
    Preconditions: Let n = len(plants). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= plants[i] <= 1000000; capacity <= 1000000000; and max_{0 <= i < n} plants[i] <= capacity. All indices are 0-based. -/
  theorem spec_4 (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
      (hpre : GoodInput plants capacity) :
      ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
        ∃ k : Int, r.val - (plants.val.length : Int) = 2 * k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
        (hpre : GoodInput plants capacity), ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
          ∃ k : Int, r.val - (plants.val.length : Int) = 2 * k) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: Let n = len(plants). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= plants[i] <= 1000000; capacity <= 1000000000; and max_{0 <= i < n} plants[i] <= capacity. All indices are 0-based. Additionally n = 1. -/
  theorem spec_5 (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
      (hpre : GoodInput plants capacity) (hn : plants.val.length = 1) :
      ∃ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r ∧
        r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
        (hpre : GoodInput plants capacity) (hn : plants.val.length = 1), ∃ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r ∧
          r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r = n if and only if sum_{i=0}^{n-1} plants[i] <= capacity.
    Preconditions: Let n = len(plants). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= plants[i] <= 1000000; capacity <= 1000000000; and max_{0 <= i < n} plants[i] <= capacity. All indices are 0-based. -/
  theorem spec_6 (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
      (hpre : GoodInput plants capacity) :
      ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
        (r.val = (plants.val.length : Int) ↔ totalSum (heights plants) ≤ capacity.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
        (hpre : GoodInput plants capacity), ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
          (r.val = (plants.val.length : Int) ↔ totalSum (heights plants) ≤ capacity.val)) := by
    sorry

  /-- Whenever the function returns a result r, r = n * n if and only if for every i with 1 <= i < n, plants[i-1] + plants[i] > capacity.
    Preconditions: Let n = len(plants). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= plants[i] <= 1000000; capacity <= 1000000000; and max_{0 <= i < n} plants[i] <= capacity. All indices are 0-based. -/
  theorem spec_7 (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
      (hpre : GoodInput plants capacity) :
      ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
        (r.val = (plants.val.length : Int) * (plants.val.length : Int) ↔
          NeighboursExceed (heights plants) capacity.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
        (hpre : GoodInput plants capacity), ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
          (r.val = (plants.val.length : Int) * (plants.val.length : Int) ↔
            NeighboursExceed (heights plants) capacity.val)) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} plants[i] and let m = ceil(S / capacity) - 1. Whenever the function returns a result r, r >= n + m * (m + 1).
    Preconditions: Let n = len(plants). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= plants[i] <= 1000000; capacity <= 1000000000; and max_{0 <= i < n} plants[i] <= capacity. All indices are 0-based. -/
  theorem spec_8 (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
      (hpre : GoodInput plants capacity) :
      ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
        (let m : Int := ceilDiv (totalSum (heights plants)) capacity.val - 1
         (plants.val.length : Int) + m * (m + 1) ≤ r.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
        (hpre : GoodInput plants capacity), ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
          (let m : Int := ceilDiv (totalSum (heights plants)) capacity.val - 1
           (plants.val.length : Int) + m * (m + 1) ≤ r.val)) := by
    sorry

  /-- For every i with 1 <= i < n, if plants[i] = capacity, then whenever the function returns a result r, r >= n + 2 * i.
    Preconditions: Let n = len(plants). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= plants[i] <= 1000000; capacity <= 1000000000; and max_{0 <= i < n} plants[i] <= capacity. All indices are 0-based. -/
  theorem spec_9 (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
      (hpre : GoodInput plants capacity) :
      ∀ i, (h1 : 1 ≤ i) → (h2 : i < (heights plants).length) →
        (heights plants)[i] = capacity.val →
          ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
            (plants.val.length : Int) + 2 * (i : Int) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (plants : Aeneas.Std.Slice Aeneas.Std.I64) (capacity : Aeneas.Std.I64)
        (hpre : GoodInput plants capacity), ∀ i, (h1 : 1 ≤ i) → (h2 : i < (heights plants).length) →
          (heights plants)[i] = capacity.val →
            ∀ r : Aeneas.Std.I64, Aegis.WateringPlants.watering_plants plants capacity = ok r →
              (plants.val.length : Int) + 2 * (i : Int) ≤ r.val) := by
    sorry

  end AegisSpec.WateringPlants
