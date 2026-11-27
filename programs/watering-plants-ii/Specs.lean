import Aegis.MinimumRefill.Code.Funs

/-!
# Specifications of `Aegis.MinimumRefill.minimum_refill`

LeetCode problem `watering-plants-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumRefill

  namespace AegisSpec.MinimumRefill

  def amounts (plants : Slice Std.I64) : List ℤ := plants.val.map (fun x => x.val)

  def nthD (l : List ℤ) (i : ℕ) : ℤ := (l[i]?).getD 0

  def maxAmount (l : List ℤ) : ℤ := l.foldr max 0

  def EvenN (n : ℕ) : Prop := n % 2 = 0

  def OddN (n : ℕ) : Prop := n % 2 = 1

  instance (n : ℕ) : Decidable (EvenN n) := by unfold EvenN; infer_instance

  instance (n : ℕ) : Decidable (OddN n) := by unfold OddN; infer_instance

  def step (C : ℤ) (st : ℤ × ℤ) (a : ℤ) : ℤ × ℤ :=
    if a > st.1 then (C - a, st.2 + 1) else (st.1 - a, st.2)

  def process (C : ℤ) (S : List ℤ) : ℤ × ℤ := S.foldl (step C) (C, 0)

  def refills (C : ℤ) (S : List ℤ) : ℤ := (process C S).2

  def rem (C : ℤ) (S : List ℤ) : ℤ := (process C S).1

  def front (plants : List ℤ) (m : ℕ) : List ℤ := plants.take m

  def back (plants : List ℤ) (n m : ℕ) : List ℤ := (plants.drop (n - m)).reverse

  def middle (plants : List ℤ) (n : ℕ) : ℤ := nthD plants (n / 2)

  def remA (plants : List ℤ) (capacityA : ℤ) (n : ℕ) : ℤ := rem capacityA (front plants (n / 2))

  def remB (plants : List ℤ) (capacityB : ℤ) (n : ℕ) : ℤ := rem capacityB (back plants n (n / 2))

  def baseRefills (plants : List ℤ) (capacityA capacityB : ℤ) (n : ℕ) : ℤ :=
    refills capacityA (front plants (n / 2)) + refills capacityB (back plants n (n / 2))

  def sumFront (plants : List ℤ) (n : ℕ) : ℤ := (front plants (n / 2)).sum

  def sumBack (plants : List ℤ) (n : ℕ) : ℤ := (back plants n (n / 2)).sum

  def middleRefill (plants : List ℤ) (capacityA capacityB : ℤ) (n : ℕ) : ℤ :=
    if (remA plants capacityA n ≥ remB plants capacityB n ∧ middle plants n > remA plants capacityA n) ∨
       (remA plants capacityA n < remB plants capacityB n ∧ middle plants n > remB plants capacityB n)
    then 1 else 0

  def totalRefills (plants : List ℤ) (capacityA capacityB : ℤ) (n : ℕ) : ℤ :=
    baseRefills plants capacityA capacityB n +
      (if EvenN n then 0 else middleRefill plants capacityA capacityB n)

  inductive Waterer where
    | alice
    | bob
    deriving DecidableEq, Repr

  def middleOwner (a b : ℤ) : Waterer × ℤ :=
    if a ≥ b then (Waterer.alice, a) else (Waterer.bob, b)

  /-- Let m = n / 2 (integer division). Let A be the sequence [plants[0], plants[1], ..., plants[m-1]] (empty if m=0). Let B be the sequence [plants[n-1], plants[n-2], ..., plants[n-m]] (empty if m=0). For any integer sequence S and capacity C, define refills(C,S) and rem(C,S) by starting with current water C and count 0, and for each amount a in S from left to right: if a > current water then increase count by 1 and set current water to C, then subtract a from current water; finally output the count and current water. Let base = refills(capacityA,A) + refills(capacityB,B). If n is even, let total_refills = base. If n is odd, let a = rem(capacityA,A) and b = rem(capacityB,B); total_refills = base + 1 if (a >= b and plants[m] > a) or (a < b and plants[m] > b), and total_refills = base otherwise. Whenever the function returns a result r, r = total_refills.
    Preconditions: n = len(plants); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= plants[i] <= 1000000; let M = max{plants[i] | 0 <= i < n}; M <= capacityA, capacityB <= 1000000000. -/
  theorem spec_1 (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
      (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
      (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
      (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
      (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
      (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
        r.val = totalRefills (amounts plants) capacityA.val capacityB.val n := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
        (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
        (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
        (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
        (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
        (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000), ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
          r.val = totalRefills (amounts plants) capacityA.val capacityB.val n) := by
    sorry

  /-- The function returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: Same as spec_1. -/
  theorem spec_2 (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
      (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
      (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
      (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
      (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
      (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000) :
      ∃ r : Std.I64, minimum_refill plants capacityA capacityB = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
        (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
        (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
        (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
        (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
        (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000), ∃ r : Std.I64, minimum_refill plants capacityA capacityB = ok r) := by
    sorry

  /-- Whenever the function returns r, 0 <= r <= max(0, n-2), where max is over integers. In particular, if n=1 then r=0, and if n>=2 then r <= n-2.
    Preconditions: Same as spec_1. -/
  theorem spec_3 (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
      (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
      (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
      (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
      (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
      (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
        0 ≤ r.val ∧ r.val ≤ max 0 ((n : ℤ) - 2) ∧
          (n = 1 → r.val = 0) ∧ (2 ≤ n → r.val ≤ (n : ℤ) - 2) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
        (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
        (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
        (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
        (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
        (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000), ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
          0 ≤ r.val ∧ r.val ≤ max 0 ((n : ℤ) - 2) ∧
            (n = 1 → r.val = 0) ∧ (2 ≤ n → r.val ≤ (n : ℤ) - 2)) := by
    sorry

  /-- Let m = n / 2, and let A and B be as in spec_1. Let sumA = sum of all entries of A, and sumB = sum of all entries of B. Whenever the function returns r, r = 0 if and only if sumA <= capacityA and sumB <= capacityB and, when n is odd, plants[m] <= max(capacityA - sumA, capacityB - sumB). For n even, the last condition is omitted.
    Preconditions: Same as spec_1. -/
  theorem spec_4 (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
      (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
      (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
      (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
      (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
      (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
        (r.val = 0 ↔
          sumFront (amounts plants) n ≤ capacityA.val ∧
          sumBack (amounts plants) n ≤ capacityB.val ∧
            (OddN n →
              middle (amounts plants) n ≤
                max (capacityA.val - sumFront (amounts plants) n)
                  (capacityB.val - sumBack (amounts plants) n))) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
        (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
        (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
        (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
        (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
        (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000), ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
          (r.val = 0 ↔
            sumFront (amounts plants) n ≤ capacityA.val ∧
            sumBack (amounts plants) n ≤ capacityB.val ∧
              (OddN n →
                middle (amounts plants) n ≤
                  max (capacityA.val - sumFront (amounts plants) n)
                    (capacityB.val - sumBack (amounts plants) n)))) := by
    sorry

  /-- If n is even, then in the watering process that determines r, Alice waters exactly the plants with indices 0 <= i < n/2 in increasing order, and Bob waters exactly the plants with indices n/2 <= i < n in decreasing order. No plant is watered by both, and no plant is left unwatered. Consequently r = refills(capacityA, [plants[0],...,plants[n/2-1]]) + refills(capacityB, [plants[n-1],...,plants[n/2]]).
    Preconditions: Same as spec_1, and n is even. -/
  theorem spec_5 (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
      (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
      (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
      (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
      (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
      (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
      (h_even : EvenN n) :
      ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
        r.val = refills capacityA.val (front (amounts plants) (n / 2)) +
                  refills capacityB.val (back (amounts plants) n (n / 2)) ∧
          (front (amounts plants) (n / 2)).length = n / 2 ∧
            (back (amounts plants) n (n / 2)).length = n / 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
        (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
        (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
        (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
        (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
        (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
        (h_even : EvenN n), ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
          r.val = refills capacityA.val (front (amounts plants) (n / 2)) +
                    refills capacityB.val (back (amounts plants) n (n / 2)) ∧
            (front (amounts plants) (n / 2)).length = n / 2 ∧
              (back (amounts plants) n (n / 2)).length = n / 2) := by
    sorry

  /-- If n is odd, let m = n/2. Let A = [plants[0], plants[1], ..., plants[m-1]] and B = [plants[n-1], plants[n-2], ..., plants[m+1]], where empty sequences are allowed when m = 0. Define refills(C,S) and rem(C,S) as in spec_1. Let a = rem(capacityA,A), b = rem(capacityB,B), and base = refills(capacityA,A) + refills(capacityB,B). In the watering process, Alice waters exactly the plants with indices 0 <= i < m in increasing order, Bob waters exactly the plants with indices m+1 <= i < n in decreasing order, and plant m is watered by exactly one of them: Alice if a >= b, and Bob if a < b. Let d = 1 if (a >= b and plants[m] > a) or (a < b and plants[m] > b), and d = 0 otherwise. Whenever the function returns r, r = base + d.
    Preconditions: n = len(plants); 1 <= n <= 100000; n is odd; for every i with 0 <= i < n, 1 <= plants[i] <= 1000000; let M = max{plants[i] | 0 <= i < n}; M <= capacityA, capacityB <= 1000000000. -/
  theorem spec_6 (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
      (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
      (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
      (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
      (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
      (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
      (h_odd : OddN n) :
      ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
        r.val = baseRefills (amounts plants) capacityA.val capacityB.val n +
                  middleRefill (amounts plants) capacityA.val capacityB.val n ∧
          (middleOwner (remA (amounts plants) capacityA.val n)
              (remB (amounts plants) capacityB.val n)).1 =
            (if remA (amounts plants) capacityA.val n ≥ remB (amounts plants) capacityB.val n
              then Waterer.alice else Waterer.bob) ∧
            (front (amounts plants) (n / 2)).length = n / 2 ∧
              (back (amounts plants) n (n / 2)).length = n / 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
        (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
        (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
        (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
        (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
        (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
        (h_odd : OddN n), ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
          r.val = baseRefills (amounts plants) capacityA.val capacityB.val n +
                    middleRefill (amounts plants) capacityA.val capacityB.val n ∧
            (middleOwner (remA (amounts plants) capacityA.val n)
                (remB (amounts plants) capacityB.val n)).1 =
              (if remA (amounts plants) capacityA.val n ≥ remB (amounts plants) capacityB.val n
                then Waterer.alice else Waterer.bob) ∧
              (front (amounts plants) (n / 2)).length = n / 2 ∧
                (back (amounts plants) n (n / 2)).length = n / 2) := by
    sorry

  /-- Let a = rem(capacityA,A) and b = rem(capacityB,B). The middle plant m is watered by Alice if a >= b, and by Bob if a < b. Whichever person waters it refills exactly once for plant m if and only if plants[m] exceeds that person's remaining water (a for Alice, b for Bob); otherwise no refill is caused by plant m.
    Preconditions: Same as spec_1, and n is odd. Let m = n/2, and let A and B be as in spec_6. -/
  theorem spec_7 (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
      (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
      (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
      (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
      (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
      (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
      (h_odd : OddN n) :
      ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
        (remA (amounts plants) capacityA.val n ≥ remB (amounts plants) capacityB.val n →
            (middleOwner (remA (amounts plants) capacityA.val n)
              (remB (amounts plants) capacityB.val n)).1 = Waterer.alice) ∧
          (remA (amounts plants) capacityA.val n < remB (amounts plants) capacityB.val n →
            (middleOwner (remA (amounts plants) capacityA.val n)
              (remB (amounts plants) capacityB.val n)).1 = Waterer.bob) ∧
            (middle (amounts plants) n >
                (middleOwner (remA (amounts plants) capacityA.val n)
                  (remB (amounts plants) capacityB.val n)).2 ↔
              r.val = baseRefills (amounts plants) capacityA.val capacityB.val n + 1) ∧
              (¬ middle (amounts plants) n >
                  (middleOwner (remA (amounts plants) capacityA.val n)
                    (remB (amounts plants) capacityB.val n)).2 ↔
                r.val = baseRefills (amounts plants) capacityA.val capacityB.val n) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (plants : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
        (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
        (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
        (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
        (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
        (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
        (h_odd : OddN n), ∀ r : Std.I64, minimum_refill plants capacityA capacityB = ok r →
          (remA (amounts plants) capacityA.val n ≥ remB (amounts plants) capacityB.val n →
              (middleOwner (remA (amounts plants) capacityA.val n)
                (remB (amounts plants) capacityB.val n)).1 = Waterer.alice) ∧
            (remA (amounts plants) capacityA.val n < remB (amounts plants) capacityB.val n →
              (middleOwner (remA (amounts plants) capacityA.val n)
                (remB (amounts plants) capacityB.val n)).1 = Waterer.bob) ∧
              (middle (amounts plants) n >
                  (middleOwner (remA (amounts plants) capacityA.val n)
                    (remB (amounts plants) capacityB.val n)).2 ↔
                r.val = baseRefills (amounts plants) capacityA.val capacityB.val n + 1) ∧
                (¬ middle (amounts plants) n >
                    (middleOwner (remA (amounts plants) capacityA.val n)
                      (remB (amounts plants) capacityB.val n)).2 ↔
                  r.val = baseRefills (amounts plants) capacityA.val capacityB.val n)) := by
    sorry

  /-- Whenever the first call returns r1 and the second call returns r2, r1 <= r2.
    Preconditions: Two valid inputs satisfy the constraints of spec_1, have the same n, the same plants at all indices except possibly m, where n is odd and m = n/2. Let their middle amounts be w1 and w2 with w1 <= w2; all other parameters capacityA and capacityB are the same, and both inputs satisfy max(plants) <= capacityA, capacityB. -/
  theorem spec_8 (plants1 plants2 : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
      (h_n1 : n = plants1.val.length) (h_n2 : n = plants2.val.length)
      (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
      (h_bounds1 : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants1) i ∧ nthD (amounts plants1) i ≤ 1000000)
      (h_bounds2 : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants2) i ∧ nthD (amounts plants2) i ≤ 1000000)
      (h_maxA1 : maxAmount (amounts plants1) ≤ capacityA.val)
      (h_maxB1 : maxAmount (amounts plants1) ≤ capacityB.val)
      (h_maxA2 : maxAmount (amounts plants2) ≤ capacityA.val)
      (h_maxB2 : maxAmount (amounts plants2) ≤ capacityB.val)
      (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
      (h_odd : OddN n)
      (h_same : ∀ i : ℕ, i < n → i ≠ n / 2 →
        nthD (amounts plants1) i = nthD (amounts plants2) i)
      (h_mid : nthD (amounts plants1) (n / 2) ≤ nthD (amounts plants2) (n / 2)) :
      ∀ r1 r2 : Std.I64, minimum_refill plants1 capacityA capacityB = ok r1 →
        minimum_refill plants2 capacityA capacityB = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (plants1 plants2 : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
        (h_n1 : n = plants1.val.length) (h_n2 : n = plants2.val.length)
        (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
        (h_bounds1 : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants1) i ∧ nthD (amounts plants1) i ≤ 1000000)
        (h_bounds2 : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants2) i ∧ nthD (amounts plants2) i ≤ 1000000)
        (h_maxA1 : maxAmount (amounts plants1) ≤ capacityA.val)
        (h_maxB1 : maxAmount (amounts plants1) ≤ capacityB.val)
        (h_maxA2 : maxAmount (amounts plants2) ≤ capacityA.val)
        (h_maxB2 : maxAmount (amounts plants2) ≤ capacityB.val)
        (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
        (h_odd : OddN n)
        (h_same : ∀ i : ℕ, i < n → i ≠ n / 2 →
          nthD (amounts plants1) i = nthD (amounts plants2) i)
        (h_mid : nthD (amounts plants1) (n / 2) ≤ nthD (amounts plants2) (n / 2)), ∀ r1 r2 : Std.I64, minimum_refill plants1 capacityA capacityB = ok r1 →
          minimum_refill plants2 capacityA capacityB = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- Whenever the two calls return r1 and r2, |r1 - r2| <= 1.
    Preconditions: Two valid inputs satisfy the constraints of spec_1, have the same n, the same plants at all indices except possibly m, where n is odd and m = n/2, and have the same capacityA and capacityB. Let their middle amounts be w1 and w2; both inputs satisfy max(plants) <= capacityA, capacityB. -/
  theorem spec_9 (plants1 plants2 : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
      (h_n1 : n = plants1.val.length) (h_n2 : n = plants2.val.length)
      (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
      (h_bounds1 : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants1) i ∧ nthD (amounts plants1) i ≤ 1000000)
      (h_bounds2 : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants2) i ∧ nthD (amounts plants2) i ≤ 1000000)
      (h_maxA1 : maxAmount (amounts plants1) ≤ capacityA.val)
      (h_maxB1 : maxAmount (amounts plants1) ≤ capacityB.val)
      (h_maxA2 : maxAmount (amounts plants2) ≤ capacityA.val)
      (h_maxB2 : maxAmount (amounts plants2) ≤ capacityB.val)
      (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
      (h_odd : OddN n)
      (h_same : ∀ i : ℕ, i < n → i ≠ n / 2 →
        nthD (amounts plants1) i = nthD (amounts plants2) i) :
      ∀ r1 r2 : Std.I64, minimum_refill plants1 capacityA capacityB = ok r1 →
        minimum_refill plants2 capacityA capacityB = ok r2 → |r1.val - r2.val| ≤ 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (plants1 plants2 : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
        (h_n1 : n = plants1.val.length) (h_n2 : n = plants2.val.length)
        (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
        (h_bounds1 : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants1) i ∧ nthD (amounts plants1) i ≤ 1000000)
        (h_bounds2 : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants2) i ∧ nthD (amounts plants2) i ≤ 1000000)
        (h_maxA1 : maxAmount (amounts plants1) ≤ capacityA.val)
        (h_maxB1 : maxAmount (amounts plants1) ≤ capacityB.val)
        (h_maxA2 : maxAmount (amounts plants2) ≤ capacityA.val)
        (h_maxB2 : maxAmount (amounts plants2) ≤ capacityB.val)
        (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
        (h_odd : OddN n)
        (h_same : ∀ i : ℕ, i < n → i ≠ n / 2 →
          nthD (amounts plants1) i = nthD (amounts plants2) i), ∀ r1 r2 : Std.I64, minimum_refill plants1 capacityA capacityB = ok r1 →
          minimum_refill plants2 capacityA capacityB = ok r2 → |r1.val - r2.val| ≤ 1) := by
    sorry

  /-- Whenever both calls return results r1 and r2, r2 <= r1. That is, increasing a can's capacity cannot increase the total number of refills.
    Preconditions: Two valid inputs satisfy the constraints of spec_1 and have the same plants. Either (capacityA1 <= capacityA2 and capacityB1 = capacityB2) or (capacityA1 = capacityA2 and capacityB1 <= capacityB2). Let r1 and r2 be the results on the two inputs. -/
  theorem spec_10 (plants : Slice Std.I64) (capacityA1 capacityA2 capacityB1 capacityB2 : Std.I64)
      (n : ℕ)
      (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
      (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
      (h_maxA1 : maxAmount (amounts plants) ≤ capacityA1.val)
      (h_maxB1 : maxAmount (amounts plants) ≤ capacityB1.val)
      (h_capA1 : capacityA1.val ≤ 1000000000) (h_capB1 : capacityB1.val ≤ 1000000000)
      (h_maxA2 : maxAmount (amounts plants) ≤ capacityA2.val)
      (h_maxB2 : maxAmount (amounts plants) ≤ capacityB2.val)
      (h_capA2 : capacityA2.val ≤ 1000000000) (h_capB2 : capacityB2.val ≤ 1000000000)
      (h_cmp : (capacityA1.val ≤ capacityA2.val ∧ capacityB1 = capacityB2) ∨
        (capacityA1 = capacityA2 ∧ capacityB1.val ≤ capacityB2.val)) :
      ∀ r1 r2 : Std.I64, minimum_refill plants capacityA1 capacityB1 = ok r1 →
        minimum_refill plants capacityA2 capacityB2 = ok r2 → r2.val ≤ r1.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (plants : Slice Std.I64) (capacityA1 capacityA2 capacityB1 capacityB2 : Std.I64)
        (n : ℕ)
        (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
        (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
        (h_maxA1 : maxAmount (amounts plants) ≤ capacityA1.val)
        (h_maxB1 : maxAmount (amounts plants) ≤ capacityB1.val)
        (h_capA1 : capacityA1.val ≤ 1000000000) (h_capB1 : capacityB1.val ≤ 1000000000)
        (h_maxA2 : maxAmount (amounts plants) ≤ capacityA2.val)
        (h_maxB2 : maxAmount (amounts plants) ≤ capacityB2.val)
        (h_capA2 : capacityA2.val ≤ 1000000000) (h_capB2 : capacityB2.val ≤ 1000000000)
        (h_cmp : (capacityA1.val ≤ capacityA2.val ∧ capacityB1 = capacityB2) ∨
          (capacityA1 = capacityA2 ∧ capacityB1.val ≤ capacityB2.val)), ∀ r1 r2 : Std.I64, minimum_refill plants capacityA1 capacityB1 = ok r1 →
          minimum_refill plants capacityA2 capacityB2 = ok r2 → r2.val ≤ r1.val) := by
    sorry

  /-- Whenever the first call returns r and the second call returns r', r = r'.
    Preconditions: The input (plants, capacityA, capacityB) satisfies the constraints of spec_1. Let rev(plants) be the sequence with rev(plants)[i] = plants[n-1-i] for 0 <= i < n. The input (rev(plants), capacityB, capacityA) also satisfies the constraints. -/
  theorem spec_11 (plants plants' : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
      (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
      (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
      (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
      (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
      (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
      (h_rev : plants'.val = plants.val.reverse) :
      ∀ r r' : Std.I64, minimum_refill plants capacityA capacityB = ok r →
        minimum_refill plants' capacityB capacityA = ok r' → r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (plants plants' : Slice Std.I64) (capacityA capacityB : Std.I64) (n : ℕ)
        (h_n : n = plants.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
        (h_bounds : ∀ i : ℕ, i < n → 1 ≤ nthD (amounts plants) i ∧ nthD (amounts plants) i ≤ 1000000)
        (h_maxA : maxAmount (amounts plants) ≤ capacityA.val)
        (h_maxB : maxAmount (amounts plants) ≤ capacityB.val)
        (h_capA : capacityA.val ≤ 1000000000) (h_capB : capacityB.val ≤ 1000000000)
        (h_rev : plants'.val = plants.val.reverse), ∀ r r' : Std.I64, minimum_refill plants capacityA capacityB = ok r →
          minimum_refill plants' capacityB capacityA = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.MinimumRefill
