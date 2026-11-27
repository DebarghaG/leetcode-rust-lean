import Aegis.FillCups.Code.Funs

/-!
# Specifications of `Aegis.FillCups.fill_cups`

LeetCode problem `minimum-amount-of-time-to-fill-cups`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FillCups

  def entry (l : List Aeneas.Std.I64) (i : Nat) : ℤ := (l[i]!).val

  def total (l : List Aeneas.Std.I64) : ℤ := entry l 0 + entry l 1 + entry l 2

  def maxAmount (l : List Aeneas.Std.I64) : ℤ := max (max (entry l 0) (entry l 1)) (entry l 2)

  def otherTwoSum (l : List Aeneas.Std.I64) (i : Nat) : ℤ :=
    ((l.eraseIdx i).map (fun x => x.val)).sum

  def IsFillSecond (s : List (Fin 3)) : Prop :=
    (s.length = 1 ∨ s.length = 2) ∧ s.Nodup

  def countType (sch : List (List (Fin 3))) (i : Fin 3) : ℕ :=
    (sch.map (fun s => (s.filter (fun t => t = i)).length)).sum

  def IsFillingSchedule (amount : List Aeneas.Std.I64) (sch : List (List (Fin 3))) : Prop :=
    (∀ s ∈ sch, IsFillSecond s) ∧
      ∀ i : Fin 3, (countType sch i : ℤ) = entry amount i.val

  def IsPerm3 (l l' : List Aeneas.Std.I64) : Prop :=
    ∃ π : Equiv.Perm (Fin 3), ∀ i : Fin 3, entry l' i.val = entry l (π i).val

  /-- The function returns a result r and does not fail. Let S = amount[0] + amount[1] + amount[2] and M = max(amount[0], amount[1], amount[2]). Then r = max(M, (S + 1) / 2), where / is integer division. Equivalently, r is the least integer t such that t >= amount[0], t >= amount[1], t >= amount[2], and 2*t >= S.
    Preconditions: len(amount) = 3 and for every i with 0 <= i < 3, 0 <= amount[i] <= 100. -/
  theorem spec_1 (amount : Slice I64)
      (hlen : amount.val.length = 3)
      (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100) :
      ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
        r.val = max (maxAmount amount.val) ((total amount.val + 1) / 2) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (amount : Slice I64)
        (hlen : amount.val.length = 3)
        (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100), ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
          r.val = max (maxAmount amount.val) ((total amount.val + 1) / 2)) := by
    sorry

  /-- The function returns a result r and does not fail: under these preconditions there is no arithmetic overflow, no out-of-bounds access, and no panic.
    Preconditions: len(amount) = 3 and for every i with 0 <= i < 3, 0 <= amount[i] <= 100. -/
  theorem spec_2 (amount : Slice I64)
      (hlen : amount.val.length = 3)
      (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100) :
      ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (amount : Slice I64)
        (hlen : amount.val.length = 3)
        (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100), ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r) := by
    sorry

  /-- The function returns a result r and for every i with 0 <= i < 3, r >= amount[i].
    Preconditions: len(amount) = 3 and for every i with 0 <= i < 3, 0 <= amount[i] <= 100. -/
  theorem spec_3 (amount : Slice I64)
      (hlen : amount.val.length = 3)
      (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100) :
      ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
        ∀ i : Nat, i < 3 → r.val ≥ entry amount.val i := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (amount : Slice I64)
        (hlen : amount.val.length = 3)
        (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100), ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
          ∀ i : Nat, i < 3 → r.val ≥ entry amount.val i) := by
    sorry

  /-- The function returns a result r and 2*r >= amount[0] + amount[1] + amount[2].
    Preconditions: len(amount) = 3 and for every i with 0 <= i < 3, 0 <= amount[i] <= 100. -/
  theorem spec_4 (amount : Slice I64)
      (hlen : amount.val.length = 3)
      (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100) :
      ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
        2 * r.val ≥ total amount.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (amount : Slice I64)
        (hlen : amount.val.length = 3)
        (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100), ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
          2 * r.val ≥ total amount.val) := by
    sorry

  /-- The function returns a result r and r <= amount[0] + amount[1] + amount[2].
    Preconditions: len(amount) = 3 and for every i with 0 <= i < 3, 0 <= amount[i] <= 100. -/
  theorem spec_5 (amount : Slice I64)
      (hlen : amount.val.length = 3)
      (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100) :
      ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
        r.val ≤ total amount.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (amount : Slice I64)
        (hlen : amount.val.length = 3)
        (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100), ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
          r.val ≤ total amount.val) := by
    sorry

  /-- The function returns a result r and for every i with 0 <= i < 3, if amount[i] >= amount[j] + amount[k] where {j,k} = {0,1,2} \ {i}, then r = amount[i].
    Preconditions: len(amount) = 3 and for every i with 0 <= i < 3, 0 <= amount[i] <= 100. -/
  theorem spec_6 (amount : Slice I64)
      (hlen : amount.val.length = 3)
      (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100) :
      ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
        ∀ i : Nat, i < 3 → entry amount.val i ≥ otherTwoSum amount.val i →
          r.val = entry amount.val i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (amount : Slice I64)
        (hlen : amount.val.length = 3)
        (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100), ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
          ∀ i : Nat, i < 3 → entry amount.val i ≥ otherTwoSum amount.val i →
            r.val = entry amount.val i) := by
    sorry

  /-- The function returns a result r and if for every i with 0 <= i < 3, 2*amount[i] <= amount[0] + amount[1] + amount[2], then r = (amount[0] + amount[1] + amount[2] + 1) / 2, where / is integer division.
    Preconditions: len(amount) = 3 and for every i with 0 <= i < 3, 0 <= amount[i] <= 100. -/
  theorem spec_7 (amount : Slice I64)
      (hlen : amount.val.length = 3)
      (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100)
      (hbal : ∀ i : Nat, i < 3 → 2 * entry amount.val i ≤ total amount.val) :
      ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
        r.val = (total amount.val + 1) / 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (amount : Slice I64)
        (hlen : amount.val.length = 3)
        (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100)
        (hbal : ∀ i : Nat, i < 3 → 2 * entry amount.val i ≤ total amount.val), ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
          r.val = (total amount.val + 1) / 2) := by
    sorry

  /-- The function returns a result r and there exists a valid filling schedule lasting exactly r seconds that fills all cups, where a schedule is a sequence of r seconds, each second filling either one cup of a single type or two cups of two distinct types among {0,1,2}, such that for each i with 0 <= i < 3 the total number of type-i cups filled over all seconds equals amount[i].
    Preconditions: len(amount) = 3 and for every i with 0 <= i < 3, 0 <= amount[i] <= 100. -/
  theorem spec_8 (amount : Slice I64)
      (hlen : amount.val.length = 3)
      (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100) :
      ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
        ∃ sch : List (List (Fin 3)), IsFillingSchedule amount.val sch ∧ (sch.length : ℤ) = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (amount : Slice I64)
        (hlen : amount.val.length = 3)
        (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100), ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
          ∃ sch : List (List (Fin 3)), IsFillingSchedule amount.val sch ∧ (sch.length : ℤ) = r.val) := by
    sorry

  /-- The function returns a result r and there is no valid filling schedule lasting t seconds with 0 <= t < r that fills all cups, where a schedule is a sequence of t seconds, each second filling either one cup of a single type or two cups of two distinct types among {0,1,2}, such that for each i with 0 <= i < 3 the total number of type-i cups filled over all seconds equals amount[i].
    Preconditions: len(amount) = 3 and for every i with 0 <= i < 3, 0 <= amount[i] <= 100. -/
  theorem spec_9 (amount : Slice I64)
      (hlen : amount.val.length = 3)
      (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100) :
      ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
        ∀ t : Nat, (t : ℤ) < r.val →
          ¬ ∃ sch : List (List (Fin 3)), IsFillingSchedule amount.val sch ∧ sch.length = t := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (amount : Slice I64)
        (hlen : amount.val.length = 3)
        (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100), ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
          ∀ t : Nat, (t : ℤ) < r.val →
            ¬ ∃ sch : List (List (Fin 3)), IsFillingSchedule amount.val sch ∧ sch.length = t) := by
    sorry

  /-- The function returns a result r and, with M = max(amount[0], amount[1], amount[2]) and S = amount[0] + amount[1] + amount[2], either r = M or r = (S + 1) / 2 (integer division). In other words, the optimum is one of the two natural lower bounds.
    Preconditions: len(amount) = 3 and for every i with 0 <= i < 3, 0 <= amount[i] <= 100. -/
  theorem spec_10 (amount : Slice I64)
      (hlen : amount.val.length = 3)
      (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100) :
      ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
        (r.val = maxAmount amount.val ∨ r.val = (total amount.val + 1) / 2) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (amount : Slice I64)
        (hlen : amount.val.length = 3)
        (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100), ∃ r : I64, Aegis.FillCups.fill_cups amount = ok r ∧
          (r.val = maxAmount amount.val ∨ r.val = (total amount.val + 1) / 2)) := by
    sorry

  /-- The function returns a result r for the input amount and a result r' for the input amount', and r = r'.
    Preconditions: len(amount) = 3 and for every i with 0 <= i < 3, 0 <= amount[i] <= 100. Also amount' is a slice with len(amount') = 3, for every i with 0 <= i < 3, 0 <= amount'[i] <= 100, and amount' is a permutation of amount (there exists a permutation pi of {0,1,2} such that amount'[i] = amount[pi(i)] for every i). -/
  theorem spec_11 (amount amount' : Slice I64)
      (hlen : amount.val.length = 3)
      (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100)
      (hlen' : amount'.val.length = 3)
      (hrange' : ∀ i : Nat, i < 3 → 0 ≤ entry amount'.val i ∧ entry amount'.val i ≤ 100)
      (hperm : IsPerm3 amount.val amount'.val) :
      ∃ r r' : I64, Aegis.FillCups.fill_cups amount = ok r ∧
        Aegis.FillCups.fill_cups amount' = ok r' ∧ r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (amount amount' : Slice I64)
        (hlen : amount.val.length = 3)
        (hrange : ∀ i : Nat, i < 3 → 0 ≤ entry amount.val i ∧ entry amount.val i ≤ 100)
        (hlen' : amount'.val.length = 3)
        (hrange' : ∀ i : Nat, i < 3 → 0 ≤ entry amount'.val i ∧ entry amount'.val i ≤ 100)
        (hperm : IsPerm3 amount.val amount'.val), ∃ r r' : I64, Aegis.FillCups.fill_cups amount = ok r ∧
          Aegis.FillCups.fill_cups amount' = ok r' ∧ r = r') := by
    sorry

  end AegisSpec.FillCups
