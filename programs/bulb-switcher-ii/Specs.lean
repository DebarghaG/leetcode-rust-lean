import Aegis.FlipLights.Code.Funs

/-!
# Specifications of `Aegis.FlipLights.flip_lights`

LeetCode problem `bulb-switcher-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FlipLights

  namespace AegisSpec.FlipLights

  abbrev Status (n : Nat) : Type := Fin n → ZMod 2

  def indEven (j : Nat) : ZMod 2 := if j % 2 = 0 then 1 else 0

  def indOdd (j : Nat) : ZMod 2 := if j % 2 = 1 then 1 else 0

  def indOneModThree (j : Nat) : ZMod 2 := if j % 3 = 1 then 1 else 0

  def producedStatus (n c1 c2 c3 c4 : Nat) : Status n :=
    fun i =>
      (1 : ZMod 2) + (c1 : ZMod 2) + (c2 : ZMod 2) * indEven (i.val + 1) +
        (c3 : ZMod 2) * indOdd (i.val + 1) + (c4 : ZMod 2) * indOneModThree (i.val + 1)

  def IsProducedStatus (n presses : Nat) (b : Status n) : Prop :=
    ∃ c1 c2 c3 c4 : Nat, c1 + c2 + c3 + c4 = presses ∧ b = producedStatus n c1 c2 c3 c4

  def producedStatuses (n presses : Nat) : Set (Status n) :=
    { b | IsProducedStatus n presses b }

  /-- Define a status to be a function b : {1,...,n} -> {0,1}, where b(j)=1 means bulb j is on and b(j)=0 means it is off. For nonnegative integers c1,c2,c3,c4, say they produce b if c1+c2+c3+c4 = presses and, for every j with 1 <= j <= n, b(j) ≡ 1 + (c1 mod 2) + ((c2 mod 2) * [j is even]) + ((c3 mod 2) * [j is odd]) + ((c4 mod 2) * [j ≡ 1 mod 3]) (mod 2), where [P]=1 if P holds and 0 otherwise. Let S be the set of all statuses produced by some such (c1,c2,c3,c4). Then the function returns r = |S|, the number of distinct possible statuses after exactly presses presses.
    Preconditions: 1 ≤ n ≤ 1000 and 0 ≤ presses ≤ 1000. -/
  theorem spec_1 (n presses : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hp_lo : 0 ≤ presses.val) (hp_hi : presses.val ≤ 1000) :
      ∃ r : Std.I64, flip_lights n presses = ok r ∧
        r.val = ((producedStatuses n.val.toNat presses.val.toNat).ncard : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n presses : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hp_lo : 0 ≤ presses.val) (hp_hi : presses.val ≤ 1000), ∃ r : Std.I64, flip_lights n presses = ok r ∧
          r.val = ((producedStatuses n.val.toNat presses.val.toNat).ncard : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r and does not fail: there is no overflow, panic, or out-of-bounds failure.
    Preconditions: 1 ≤ n ≤ 1000 and 0 ≤ presses ≤ 1000. -/
  theorem spec_2 (n presses : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hp_lo : 0 ≤ presses.val) (hp_hi : presses.val ≤ 1000) :
      ∃ r : Std.I64, flip_lights n presses = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n presses : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hp_lo : 0 ≤ presses.val) (hp_hi : presses.val ≤ 1000), ∃ r : Std.I64, flip_lights n presses = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 ≤ r ≤ min(8, 2^n).
    Preconditions: 1 ≤ n ≤ 1000 and 0 ≤ presses ≤ 1000. -/
  theorem spec_3 (n presses : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hp_lo : 0 ≤ presses.val) (hp_hi : presses.val ≤ 1000) :
      ∀ r : Std.I64, flip_lights n presses = ok r →
        1 ≤ r.val ∧ r.val ≤ min (8 : Int) ((2 : Int) ^ n.val.toNat) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n presses : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hp_lo : 0 ≤ presses.val) (hp_hi : presses.val ≤ 1000), ∀ r : Std.I64, flip_lights n presses = ok r →
          1 ≤ r.val ∧ r.val ≤ min (8 : Int) ((2 : Int) ^ n.val.toNat)) := by
    sorry

  /-- The function returns r and r = 1.
    Preconditions: 1 ≤ n ≤ 1000 and presses = 0. -/
  theorem spec_4 (n presses : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hp : presses.val = 0) :
      ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n presses : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hp : presses.val = 0), ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns r and r = 2.
    Preconditions: n = 1 and 1 ≤ presses ≤ 1000. -/
  theorem spec_5 (n presses : Std.I64)
      (hn : n.val = 1)
      (hp_lo : 1 ≤ presses.val) (hp_hi : presses.val ≤ 1000) :
      ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n presses : Std.I64)
        (hn : n.val = 1)
        (hp_lo : 1 ≤ presses.val) (hp_hi : presses.val ≤ 1000), ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 2) := by
    sorry

  /-- The function returns r and r = 3.
    Preconditions: n = 2 and presses = 1. -/
  theorem spec_6 (n presses : Std.I64)
      (hn : n.val = 2)
      (hp : presses.val = 1) :
      ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 3 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n presses : Std.I64)
        (hn : n.val = 2)
        (hp : presses.val = 1), ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 3) := by
    sorry

  /-- The function returns r and r = 4.
    Preconditions: n = 2 and 2 ≤ presses ≤ 1000. -/
  theorem spec_7 (n presses : Std.I64)
      (hn : n.val = 2)
      (hp_lo : 2 ≤ presses.val) (hp_hi : presses.val ≤ 1000) :
      ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 4 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n presses : Std.I64)
        (hn : n.val = 2)
        (hp_lo : 2 ≤ presses.val) (hp_hi : presses.val ≤ 1000), ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 4) := by
    sorry

  /-- The function returns r and r = 7.
    Preconditions: 3 ≤ n ≤ 1000 and presses = 2. -/
  theorem spec_8 (n presses : Std.I64)
      (hn_lo : 3 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hp : presses.val = 2) :
      ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 7 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n presses : Std.I64)
        (hn_lo : 3 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hp : presses.val = 2), ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 7) := by
    sorry

  /-- The function returns r and r = 8.
    Preconditions: 3 ≤ n ≤ 1000 and 3 ≤ presses ≤ 1000. -/
  theorem spec_9 (n presses : Std.I64)
      (hn_lo : 3 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hp_lo : 3 ≤ presses.val) (hp_hi : presses.val ≤ 1000) :
      ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 8 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n presses : Std.I64)
        (hn_lo : 3 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hp_lo : 3 ≤ presses.val) (hp_hi : presses.val ≤ 1000), ∃ r : Std.I64, flip_lights n presses = ok r ∧ r.val = 8) := by
    sorry

  /-- The calls flip_lights(n, presses) and flip_lights(min(n, 3), presses) both return successfully, and their returned integers are equal.
    Preconditions: 1 ≤ n ≤ 1000 and 0 ≤ presses ≤ 1000. -/
  theorem spec_10 (n presses : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hp_lo : 0 ≤ presses.val) (hp_hi : presses.val ≤ 1000) :
      ∃ r1 r2 : Std.I64,
        flip_lights n presses = ok r1 ∧ flip_lights (min n 3#i64) presses = ok r2 ∧
          r1.val = r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n presses : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hp_lo : 0 ≤ presses.val) (hp_hi : presses.val ≤ 1000), ∃ r1 r2 : Std.I64,
          flip_lights n presses = ok r1 ∧ flip_lights (min n 3#i64) presses = ok r2 ∧
            r1.val = r2.val) := by
    sorry

  /-- Let r_p be the result of flip_lights(n, p) and r_q be the result of flip_lights(n, q). Both calls return successfully and r_p ≤ r_q.
    Preconditions: 1 ≤ n ≤ 1000 and 0 ≤ p ≤ q ≤ 1000. -/
  theorem spec_11 (n p q : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hp_lo : 0 ≤ p.val) (hpq : p.val ≤ q.val) (hq_hi : q.val ≤ 1000) :
      ∃ rp rq : Std.I64,
        flip_lights n p = ok rp ∧ flip_lights n q = ok rq ∧ rp.val ≤ rq.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n p q : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hp_lo : 0 ≤ p.val) (hpq : p.val ≤ q.val) (hq_hi : q.val ≤ 1000), ∃ rp rq : Std.I64,
          flip_lights n p = ok rp ∧ flip_lights n q = ok rq ∧ rp.val ≤ rq.val) := by
    sorry

  end AegisSpec.FlipLights
