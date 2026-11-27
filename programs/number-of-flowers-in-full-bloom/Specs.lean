import Aegis.FullBloomFlowers.Code.Funs

/-!
# Specifications of `Aegis.FullBloomFlowers.full_bloom_flowers`

LeetCode problem `number-of-flowers-in-full-bloom`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FullBloomFlowers

namespace AegisSpec.FullBloomFlowers

def intAt (l : List Std.I64) (i : Nat) : Int := ((l[i]?).map (·.val)).getD 0

def flowerStart (fl : alloc.vec.Vec Std.I64) : Int := intAt fl.val 0

def flowerEnd (fl : alloc.vec.Vec Std.I64) : Int := intAt fl.val 1

def Covers (fl : alloc.vec.Vec Std.I64) (p : Int) : Prop :=
  flowerStart fl ≤ p ∧ p ≤ flowerEnd fl

instance instDecidableCovers (fl : alloc.vec.Vec Std.I64) (p : Int) :
    Decidable (Covers fl p) := by
  unfold Covers
  infer_instance

def bloomCount (flowers : Slice (alloc.vec.Vec Std.I64)) (p : Int) : Nat :=
  (flowers.val.filter (fun fl => decide (Covers fl p))).length

def countStartLe (flowers : Slice (alloc.vec.Vec Std.I64)) (p : Int) : Nat :=
  (flowers.val.filter (fun fl => decide (flowerStart fl ≤ p))).length

def countEndLt (flowers : Slice (alloc.vec.Vec Std.I64)) (p : Int) : Nat :=
  (flowers.val.filter (fun fl => decide (flowerEnd fl < p))).length

def countInFlower (people : Slice Std.I64) (fl : alloc.vec.Vec Std.I64) : Nat :=
  (people.val.filter (fun p => decide (flowerStart fl ≤ p.val ∧ p.val ≤ flowerEnd fl))).length

def ValidFlower (fl : alloc.vec.Vec Std.I64) : Prop :=
  fl.val.length = 2 ∧ 1 ≤ flowerStart fl ∧ flowerStart fl ≤ flowerEnd fl ∧
    flowerEnd fl ≤ 1000000000

def ValidFlowers (flowers : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ flowers.val.length ∧
    ∀ (j : Nat) (hj : j < flowers.val.length), ValidFlower (flowers.val[j]'hj)

def ValidPeople (people : Slice Std.I64) : Prop :=
  1 ≤ people.val.length ∧
    ∀ (i : Nat) (hi : i < people.val.length),
      1 ≤ (people.val[i]'hi).val ∧ (people.val[i]'hi).val ≤ 1000000000

/-- The function returns a result r and len(r) = len(people), and for every i with 0 <= i < len(people), r[i] is the number of indices j with 0 <= j < len(flowers) such that flowers[j][0] <= people[i] <= flowers[j][1]. Both endpoints of each bloom interval are inclusive.
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_1 (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people) :
    ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length),
        intAt r.val i = (bloomCount flowers (people.val[i]'hi).val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people), ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length),
        intAt r.val i = (bloomCount flowers (people.val[i]'hi).val : Int)) := by
  sorry

/-- The function returns a result r and len(r) = len(people).
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_2 (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people) :
    ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people), ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < len(people), 0 <= r[i].
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_3 (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people) :
    ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length), 0 ≤ intAt r.val i := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people), ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length), 0 ≤ intAt r.val i) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < len(people), r[i] <= len(flowers).
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_4 (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people) :
    ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length),
        intAt r.val i ≤ (flowers.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people), ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length),
        intAt r.val i ≤ (flowers.val.length : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail: there is no arithmetic overflow, panic, out-of-bounds access, or other runtime failure.
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_5 (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people) :
    ∃ r, full_bloom_flowers flowers people = ok r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people), ∃ r, full_bloom_flowers flowers people = ok r) := by
  sorry

/-- The function returns a result r and for every i and k with 0 <= i < len(people) and 0 <= k < len(people), if people[i] = people[k], then r[i] = r[k].
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_6 (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people) :
    ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i k : Nat) (hi : i < people.val.length) (hk : k < people.val.length),
        (people.val[i]'hi).val = (people.val[k]'hk).val → intAt r.val i = intAt r.val k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people), ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i k : Nat) (hi : i < people.val.length) (hk : k < people.val.length),
        (people.val[i]'hi).val = (people.val[k]'hk).val → intAt r.val i = intAt r.val k) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < len(people), r[i] > 0 if and only if there exists j with 0 <= j < len(flowers) and flowers[j][0] <= people[i] <= flowers[j][1].
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_7 (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people) :
    ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length),
        0 < intAt r.val i ↔
          ∃ (j : Nat) (hj : j < flowers.val.length),
            Covers (flowers.val[j]'hj) (people.val[i]'hi).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people), ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length),
        0 < intAt r.val i ↔
          ∃ (j : Nat) (hj : j < flowers.val.length),
            Covers (flowers.val[j]'hj) (people.val[i]'hi).val) := by
  sorry

/-- The function returns a result r and for every i and j with 0 <= i < len(people) and 0 <= j < len(flowers), if people[i] = flowers[j][0] or people[i] = flowers[j][1], then r[i] >= 1.
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_8 (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people) :
    ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i j : Nat) (hi : i < people.val.length) (hj : j < flowers.val.length),
        ((people.val[i]'hi).val = flowerStart (flowers.val[j]'hj) ∨
          (people.val[i]'hi).val = flowerEnd (flowers.val[j]'hj)) →
          1 ≤ intAt r.val i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people), ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i j : Nat) (hi : i < people.val.length) (hj : j < flowers.val.length),
        ((people.val[i]'hi).val = flowerStart (flowers.val[j]'hj) ∨
          (people.val[i]'hi).val = flowerEnd (flowers.val[j]'hj)) →
          1 ≤ intAt r.val i) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < len(people), if for every j with 0 <= j < len(flowers) we have flowers[j][0] <= people[i] <= flowers[j][1], then r[i] = len(flowers).
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_9 (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people) :
    ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length),
        (∀ (j : Nat) (hj : j < flowers.val.length),
          Covers (flowers.val[j]'hj) (people.val[i]'hi).val) →
          intAt r.val i = (flowers.val.length : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people), ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length),
        (∀ (j : Nat) (hj : j < flowers.val.length),
          Covers (flowers.val[j]'hj) (people.val[i]'hi).val) →
          intAt r.val i = (flowers.val.length : Int)) := by
  sorry

/-- Whenever the function returns r for (flowers, people) and r2 for (flowers2, people), it holds that r = r2.
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. flowers2 is another valid flower list with len(flowers2) = len(flowers), each entry has length 2, and 1 <= flowers2[j][0] <= flowers2[j][1] <= 1000000000 for every j; there is a bijection p from the indices of flowers to the indices of flowers2 such that flowers2[p(j)] = flowers[j] for every j with 0 <= j < len(flowers). All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_10 (flowers flowers2 : Slice (alloc.vec.Vec Std.I64))
    (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people)
    (hflowers2 : ValidFlowers flowers2)
    (hlen : flowers2.val.length = flowers.val.length)
    (hperm : ∃ p : Fin flowers.val.length → Fin flowers2.val.length,
      Function.Bijective p ∧
        ∀ (j : Fin flowers.val.length), flowers2.val.get (p j) = flowers.val.get j) :
    ∀ (r r2 : alloc.vec.Vec Std.I64),
      full_bloom_flowers flowers people = ok r →
      full_bloom_flowers flowers2 people = ok r2 → r = r2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (flowers flowers2 : Slice (alloc.vec.Vec Std.I64))
    (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people)
    (hflowers2 : ValidFlowers flowers2)
    (hlen : flowers2.val.length = flowers.val.length)
    (hperm : ∃ p : Fin flowers.val.length → Fin flowers2.val.length,
      Function.Bijective p ∧
        ∀ (j : Fin flowers.val.length), flowers2.val.get (p j) = flowers.val.get j), ∀ (r r2 : alloc.vec.Vec Std.I64),
      full_bloom_flowers flowers people = ok r →
      full_bloom_flowers flowers2 people = ok r2 → r = r2) := by
  sorry

/-- Whenever the function returns r for (flowers, people) and r2 for (flowers, people2), then for every i with 0 <= i < len(people2), r2[i] = r[q(i)].
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. people2 is another valid person list with len(people2) = len(people) and 1 <= people2[i] <= 1000000000 for every i; there is a bijection q from the indices of people2 to the indices of people such that people2[i] = people[q(i)] for every i with 0 <= i < len(people2). All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_11 (flowers : Slice (alloc.vec.Vec Std.I64))
    (people people2 : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people)
    (hpeople2 : ValidPeople people2)
    (q : Fin people2.val.length → Fin people.val.length)
    (hbij : Function.Bijective q)
    (hmap : ∀ (i : Fin people2.val.length), people2.val.get i = people.val.get (q i)) :
    ∀ (r r2 : alloc.vec.Vec Std.I64),
      full_bloom_flowers flowers people = ok r →
      full_bloom_flowers flowers people2 = ok r2 →
        ∀ (i : Nat) (hi : i < people2.val.length),
          intAt r2.val i = intAt r.val (q ⟨i, hi⟩).val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64))
    (people people2 : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people)
    (hpeople2 : ValidPeople people2)
    (q : Fin people2.val.length → Fin people.val.length)
    (hbij : Function.Bijective q)
    (hmap : ∀ (i : Fin people2.val.length), people2.val.get i = people.val.get (q i)), ∀ (r r2 : alloc.vec.Vec Std.I64),
      full_bloom_flowers flowers people = ok r →
      full_bloom_flowers flowers people2 = ok r2 →
        ∀ (i : Nat) (hi : i < people2.val.length),
          intAt r2.val i = intAt r.val (q ⟨i, hi⟩).val) := by
  sorry

/-- The function returns a result r and let C_j be the number of indices i with 0 <= i < len(people) and flowers[j][0] <= people[i] <= flowers[j][1]. Then the sum of r[i] over 0 <= i < len(people) equals the sum of C_j over 0 <= j < len(flowers).
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_12 (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people) :
    ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      (r.val.map (fun x => x.val)).sum =
        (flowers.val.map (fun fl => (countInFlower people fl : Int))).sum := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people), ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      (r.val.map (fun x => x.val)).sum =
        (flowers.val.map (fun fl => (countInFlower people fl : Int))).sum) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < len(people), r[i] = A_i - B_i, where A_i is the number of indices j with 0 <= j < len(flowers) and flowers[j][0] <= people[i], and B_i is the number of indices j with 0 <= j < len(flowers) and flowers[j][1] < people[i].
  Preconditions: flowers is a valid flower list for the problem: len(flowers) >= 1; for every j with 0 <= j < len(flowers), len(flowers[j]) = 2 and 1 <= flowers[j][0] <= flowers[j][1] <= 1000000000. people is a valid person list: len(people) >= 1; for every i with 0 <= i < len(people), 1 <= people[i] <= 1000000000. All integers are 64-bit machine integers within the stated bounds. -/
theorem spec_13 (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people) :
    ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length),
        intAt r.val i =
          (countStartLe flowers (people.val[i]'hi).val : Int) -
            (countEndLt flowers (people.val[i]'hi).val : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (flowers : Slice (alloc.vec.Vec Std.I64)) (people : Slice Std.I64)
    (hflowers : ValidFlowers flowers) (hpeople : ValidPeople people), ∃ r, full_bloom_flowers flowers people = ok r ∧
      r.val.length = people.val.length ∧
      ∀ (i : Nat) (hi : i < people.val.length),
        intAt r.val i =
          (countStartLe flowers (people.val[i]'hi).val : Int) -
            (countEndLt flowers (people.val[i]'hi).val : Int)) := by
  sorry

end AegisSpec.FullBloomFlowers
