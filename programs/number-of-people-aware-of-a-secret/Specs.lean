import Aegis.PeopleAwareOfSecret.Code.Funs

/-!
# Specifications of `Aegis.PeopleAwareOfSecret.people_aware_of_secret`

LeetCode problem `number-of-people-aware-of-a-secret`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PeopleAwareOfSecret

def specM : ℤ := 1000000007

def isumFrom (f : ℤ → ℤ) : ℕ → ℤ → ℤ
  | 0, _ => 0
  | m + 1, lo => f lo + isumFrom f m (lo + 1)

def isum (lo hi : ℤ) (f : ℤ → ℤ) : ℤ :=
  if lo > hi then 0 else isumFrom f (hi - lo + 1).toNat lo

def newPrefix (delay forget : ℤ) : ℕ → List ℤ
  | 0 => [0]
  | m + 1 =>
      let l := newPrefix delay forget m
      let d : ℤ := (m : ℤ) + 1
      let v : ℤ :=
        if d < 1 then 0
        else if d = 1 then 1
        else isum (max 1 (d - forget + 1)) (d - delay) (fun k => l.getD k.toNat 0)
      l ++ [v]

def newSeq (delay forget : ℤ) (d : ℤ) : ℤ :=
  if d < 1 then 0 else (newPrefix delay forget d.toNat).getD d.toNat 0

def newModPrefix (delay forget : ℤ) : ℕ → List ℤ
  | 0 => [0]
  | m + 1 =>
      let l := newModPrefix delay forget m
      let d : ℤ := (m : ℤ) + 1
      let v : ℤ :=
        if d < 1 then 0
        else if d = 1 then 1
        else
          isum (max 1 (d - forget + 1)) (d - delay) (fun k => l.getD k.toNat 0) % specM
      l ++ [v]

def newModSeq (delay forget : ℤ) (d : ℤ) : ℤ :=
  if d < 1 then 0 else (newModPrefix delay forget d.toNat).getD d.toNat 0

def SatisfiesRecurrence (g : ℤ → ℤ) (delay forget : ℤ) : Prop :=
  (∀ d : ℤ, d < 1 → g d = 0) ∧ g 1 = 1 ∧
    ∀ d : ℤ, 2 ≤ d → g d = isum (max 1 (d - forget + 1)) (d - delay) g

def aware (n delay forget : ℤ) : ℤ :=
  isum (max 1 (n - forget + 1)) n (newSeq delay forget)

def totalDiscovered (n delay forget : ℤ) : ℤ := isum 1 n (newSeq delay forget)

def totalForgotten (n delay forget : ℤ) : ℤ :=
  isum 1 (max 0 (n - forget)) (newSeq delay forget)

/-- Let M = 10^9 + 7. Define the integer sequence new: Z -> Z by: new(d) = 0 for d < 1; new(1) = 1; and for d >= 2, new(d) = sum_{k = max(1, d - forget + 1)}^{d - delay} new(k), where the sum is 0 if max(1, d - forget + 1) > d - delay. Let aware = sum_{d = max(1, n - forget + 1)}^{n} new(d). Then the function returns a result r such that 0 <= r < M and r ≡ aware (mod M).
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n. -/
theorem spec_1 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) :
    ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      0 ≤ r.val ∧ r.val < specM ∧
      r.val % specM = aware n.val delay.val forget.val % specM := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val), ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      0 ≤ r.val ∧ r.val < specM ∧
      r.val % specM = aware n.val delay.val forget.val % specM) := by
  sorry

/-- The function returns a result r such that 0 <= r < 10^9 + 7.
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n. -/
theorem spec_2 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) :
    ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      0 ≤ r.val ∧ r.val < specM := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val), ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      0 ≤ r.val ∧ r.val < specM) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow).
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n. -/
theorem spec_3 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) :
    ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val), ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r) := by
  sorry

/-- The function returns a result r such that r = 2 if (n - 1) mod delay = 0, and r = 1 otherwise. (Here mod is the non-negative remainder; for delay = 1, (n - 1) mod 1 = 0.)
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n, and forget = delay + 1. -/
theorem spec_4 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) (hedge : forget.val = delay.val + 1) :
    ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      r.val = (if (n.val - 1) % delay.val = 0 then 2 else 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) (hedge : forget.val = delay.val + 1), ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      r.val = (if (n.val - 1) % delay.val = 0 then 2 else 1)) := by
  sorry

/-- The function returns a result r such that r ≡ 2^{n-1} (mod 10^9+7) and 0 <= r < 10^9+7.
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n, and delay = 1 and forget = n. -/
theorem spec_5 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) (hd1 : delay.val = 1) (hf : forget.val = n.val) :
    ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      0 ≤ r.val ∧ r.val < specM ∧
      r.val % specM = (2 : ℤ) ^ (n.val - 1).toNat % specM := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) (hd1 : delay.val = 1) (hf : forget.val = n.val), ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      0 ≤ r.val ∧ r.val < specM ∧
      r.val % specM = (2 : ℤ) ^ (n.val - 1).toNat % specM) := by
  sorry

/-- Let new: Z -> Z be the sequence defined in spec_1. Then new(1) = 1, new(2) = 1, and for all d >= 3, new(d) = new(d-1) + new(d-2). Moreover, the function returns a result r such that 0 <= r < 10^9+7 and r ≡ sum_{d = max(1, n-2)}^{n} new(d) (mod 10^9+7).
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n, and delay = 1 and forget = 3. -/
theorem spec_6 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) (hd1 : delay.val = 1) (hf : forget.val = 3) :
    newSeq delay.val forget.val 1 = 1 ∧
      newSeq delay.val forget.val 2 = 1 ∧
      (∀ d : ℤ, 3 ≤ d →
        newSeq delay.val forget.val d =
          newSeq delay.val forget.val (d - 1) + newSeq delay.val forget.val (d - 2)) ∧
      ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
        0 ≤ r.val ∧ r.val < specM ∧
        r.val % specM = isum (max 1 (n.val - 2)) n.val (newSeq delay.val forget.val) % specM := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) (hd1 : delay.val = 1) (hf : forget.val = 3), newSeq delay.val forget.val 1 = 1 ∧
      newSeq delay.val forget.val 2 = 1 ∧
      (∀ d : ℤ, 3 ≤ d →
        newSeq delay.val forget.val d =
          newSeq delay.val forget.val (d - 1) + newSeq delay.val forget.val (d - 2)) ∧
      ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
        0 ≤ r.val ∧ r.val < specM ∧
        r.val % specM = isum (max 1 (n.val - 2)) n.val (newSeq delay.val forget.val) % specM) := by
  sorry

/-- There exists a sequence new: Z -> Z satisfying the recurrence in spec_1 such that new(1) = 1, new(d) = 0 for all d with 2 <= d <= delay, and new(delay + 1) = 1. (And the function returns r as defined in spec_1.)
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n. -/
theorem spec_7 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) :
    (∃ g : ℤ → ℤ, SatisfiesRecurrence g delay.val forget.val ∧
        g 1 = 1 ∧
        (∀ d : ℤ, 2 ≤ d → d ≤ delay.val → g d = 0) ∧
        g (delay.val + 1) = 1) ∧
      ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
        0 ≤ r.val ∧ r.val < specM ∧
        r.val % specM = aware n.val delay.val forget.val % specM := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val), (∃ g : ℤ → ℤ, SatisfiesRecurrence g delay.val forget.val ∧
        g 1 = 1 ∧
        (∀ d : ℤ, 2 ≤ d → d ≤ delay.val → g d = 0) ∧
        g (delay.val + 1) = 1) ∧
      ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
        0 ≤ r.val ∧ r.val < specM ∧
        r.val % specM = aware n.val delay.val forget.val % specM) := by
  sorry

/-- Let M = 10^9+7. Define new_mod: Z -> Z by new_mod(d) = 0 for d < 1; new_mod(1) = 1; and for d >= 2, new_mod(d) = (sum_{k = max(1, d - forget + 1)}^{d - delay} new_mod(k)) mod M, where the sum is 0 if the lower bound exceeds the upper bound. Then the function returns a result r such that r = (sum_{d = max(1, n - forget + 1)}^{n} new_mod(d)) mod M.
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n. -/
theorem spec_8 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) :
    ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      r.val =
        isum (max 1 (n.val - forget.val + 1)) n.val (newModSeq delay.val forget.val) % specM := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val), ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      r.val =
        isum (max 1 (n.val - forget.val + 1)) n.val (newModSeq delay.val forget.val) % specM) := by
  sorry

/-- Let new: Z -> Z be the sequence defined in spec_1. Let total_discovered = sum_{d=1}^{n} new(d) and total_forgotten = sum_{d=1}^{max(0, n - forget)} new(d). Then the function returns a result r such that 0 <= r < 10^9+7 and r ≡ total_discovered - total_forgotten (mod 10^9+7).
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n. -/
theorem spec_9 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) :
    ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      0 ≤ r.val ∧ r.val < specM ∧
      r.val % specM =
        (totalDiscovered n.val delay.val forget.val -
          totalForgotten n.val delay.val forget.val) % specM := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val), ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      0 ≤ r.val ∧ r.val < specM ∧
      r.val % specM =
        (totalDiscovered n.val delay.val forget.val -
          totalForgotten n.val delay.val forget.val) % specM) := by
  sorry

/-- Let aware be the integer defined in spec_1. Then aware >= 1. Equivalently, there exists an integer A with A >= 1 such that A = aware and the function returns r with 0 <= r < 10^9+7 and r ≡ A (mod 10^9+7).
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n. -/
theorem spec_10 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) :
    1 ≤ aware n.val delay.val forget.val ∧
      ∃ A : ℤ, 1 ≤ A ∧ A = aware n.val delay.val forget.val ∧
        ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
          0 ≤ r.val ∧ r.val < specM ∧ r.val % specM = A % specM := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val), 1 ≤ aware n.val delay.val forget.val ∧
      ∃ A : ℤ, 1 ≤ A ∧ A = aware n.val delay.val forget.val ∧
        ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
          0 ≤ r.val ∧ r.val < specM ∧ r.val % specM = A % specM) := by
  sorry

/-- Let new: Z -> Z be the sequence defined in spec_1. Then for all integers d with d >= delay + 1, new(d) >= new(d - delay). The function returns r as defined in spec_1.
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n. -/
theorem spec_11 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) :
    (∀ d : ℤ, delay.val + 1 ≤ d →
      newSeq delay.val forget.val d ≥ newSeq delay.val forget.val (d - delay.val)) ∧
      ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
        0 ≤ r.val ∧ r.val < specM ∧
        r.val % specM = aware n.val delay.val forget.val % specM := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val), (∀ d : ℤ, delay.val + 1 ≤ d →
      newSeq delay.val forget.val d ≥ newSeq delay.val forget.val (d - delay.val)) ∧
      ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
        0 ≤ r.val ∧ r.val < specM ∧
        r.val % specM = aware n.val delay.val forget.val % specM) := by
  sorry

/-- Let aware be the integer defined in spec_1. The function returns r = 0 if and only if 10^9+7 divides aware.
  Preconditions: n, delay, forget are integers satisfying 2 <= n <= 1000, 1 <= delay < forget <= n. -/
theorem spec_12 (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val) :
    ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      (r.val = 0 ↔ specM ∣ aware n.val delay.val forget.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n delay forget : I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000)
    (hdelay : 1 ≤ delay.val) (hlt : delay.val < forget.val)
    (hforget : forget.val ≤ n.val), ∃ r : I64, Aegis.PeopleAwareOfSecret.people_aware_of_secret n delay forget = ok r ∧
      (r.val = 0 ↔ specM ∣ aware n.val delay.val forget.val)) := by
  sorry

end AegisSpec.PeopleAwareOfSecret
