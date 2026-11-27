import Aegis.NumberOfEmployeesWhoMetTarget.Code.Funs

/-!
# Specifications of `Aegis.NumberOfEmployeesWhoMetTarget.number_of_employees_who_met_target`

LeetCode problem `number-of-employees-who-met-the-target`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfEmployeesWhoMetTarget

open Aegis.NumberOfEmployeesWhoMetTarget

def countGE (l : List Std.I64) (t : Int) : Nat :=
  (l.filter (fun x => decide (t ≤ x.val))).length

def countLT (l : List Std.I64) (t : Int) : Nat :=
  (l.filter (fun x => decide (x.val < t))).length

def countEQ (l : List Std.I64) (t : Int) : Nat :=
  (l.filter (fun x => decide (x.val = t))).length

/-- The function returns a result r, and r is the number of indices i with 0 <= i < n and hours[i] >= target.
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; 0 <= target <= 100000. -/
theorem spec_1
    (hours : Slice Std.I64) (target : Std.I64) (n : Nat)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000) :
    ∃ r : Std.I64,
      number_of_employees_who_met_target hours target = ok r ∧
        r.val = (countGE hours.val target.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (hours : Slice Std.I64) (target : Std.I64) (n : Nat)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000), ∃ r : Std.I64,
      number_of_employees_who_met_target hours target = ok r ∧
        r.val = (countGE hours.val target.val : Int)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, overflow, or access out of bounds) for every input satisfying the preconditions.
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; 0 <= target <= 100000. -/
theorem spec_2
    (hours : Slice Std.I64) (target : Std.I64) (n : Nat)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000) :
    ∃ r : Std.I64, number_of_employees_who_met_target hours target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (hours : Slice Std.I64) (target : Std.I64) (n : Nat)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000), ∃ r : Std.I64, number_of_employees_who_met_target hours target = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(hours).
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; 0 <= target <= 100000. -/
theorem spec_3
    (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r) :
    0 ≤ r.val ∧ r.val ≤ (hours.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r), 0 ≤ r.val ∧ r.val ≤ (hours.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = len(hours) if and only if for every i with 0 <= i < len(hours), hours[i] >= target.
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; 0 <= target <= 100000. -/
theorem spec_4
    (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r) :
    r.val = (hours.val.length : Int) ↔
      ∀ (i : Nat) (hi : i < hours.val.length), target.val ≤ (hours.val[i]).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r), r.val = (hours.val.length : Int) ↔
      ∀ (i : Nat) (hi : i < hours.val.length), target.val ≤ (hours.val[i]).val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(hours), hours[i] < target.
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; 0 <= target <= 100000. -/
theorem spec_5
    (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r) :
    r.val = 0 ↔
      ∀ (i : Nat) (hi : i < hours.val.length), (hours.val[i]).val < target.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r), r.val = 0 ↔
      ∀ (i : Nat) (hi : i < hours.val.length), (hours.val[i]).val < target.val) := by
  sorry

/-- If target = 0, then the function returns a result r and r = len(hours).
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; target = 0. -/
theorem spec_6
    (hours : Slice Std.I64) (target : Std.I64) (n : Nat)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : target.val = 0) :
    ∃ r : Std.I64,
      number_of_employees_who_met_target hours target = ok r ∧
        r.val = (hours.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (hours : Slice Std.I64) (target : Std.I64) (n : Nat)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : target.val = 0), ∃ r : Std.I64,
      number_of_employees_who_met_target hours target = ok r ∧
        r.val = (hours.val.length : Int)) := by
  sorry

/-- If len(hours) = 1, then whenever the function returns a result r, r = 1 if hours[0] >= target, and r = 0 otherwise.
  Preconditions: n = len(hours); len(hours) = 1; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; 0 <= target <= 100000. -/
theorem spec_7
    (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hlen1 : hours.val.length = 1)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r) :
    (target.val ≤ (hours.val[0]).val → r.val = 1) ∧
      ((hours.val[0]).val < target.val → r.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hlen1 : hours.val.length = 1)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r), (target.val ≤ (hours.val[0]).val → r.val = 1) ∧
      ((hours.val[0]).val < target.val → r.val = 0)) := by
  sorry

/-- Let r1 be the result of the function on hours and t1, and let r2 be the result on hours and t2. Whenever both calls return results, r1 >= r2.
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; t1 and t2 are integers with 0 <= t1 <= t2 <= 100000. -/
theorem spec_8
    (hours : Slice Std.I64) (n : Nat) (t1 t2 : Std.I64) (r1 r2 : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht1_0 : 0 ≤ t1.val) (ht12 : t1.val ≤ t2.val) (ht2 : t2.val ≤ 100000)
    (hr1 : number_of_employees_who_met_target hours t1 = ok r1)
    (hr2 : number_of_employees_who_met_target hours t2 = ok r2) :
    r1.val ≥ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (t1 t2 : Std.I64) (r1 r2 : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht1_0 : 0 ≤ t1.val) (ht12 : t1.val ≤ t2.val) (ht2 : t2.val ≤ 100000)
    (hr1 : number_of_employees_who_met_target hours t1 = ok r1)
    (hr2 : number_of_employees_who_met_target hours t2 = ok r2), r1.val ≥ r2.val) := by
  sorry

/-- Let r1 be the result on hours1 and target, and let r2 be the result on hours2 and target. Whenever both calls return results, r1 <= r2.
  Preconditions: hours1 and hours2 both satisfy 1 <= len <= 50 and all entries are in 0..100000; len(hours1) = len(hours2); for every i with 0 <= i < len(hours1), hours1[i] <= hours2[i]; 0 <= target <= 100000. -/
theorem spec_9
    (hours1 hours2 : Slice Std.I64) (target : Std.I64) (r1 r2 : Std.I64)
    (h1_1 : 1 ≤ hours1.val.length) (h1_50 : hours1.val.length ≤ 50)
    (h1_val : ∀ (i : Nat) (hi : i < hours1.val.length),
      0 ≤ (hours1.val[i]).val ∧ (hours1.val[i]).val ≤ 100000)
    (h2_1 : 1 ≤ hours2.val.length) (h2_50 : hours2.val.length ≤ 50)
    (h2_val : ∀ (i : Nat) (hi : i < hours2.val.length),
      0 ≤ (hours2.val[i]).val ∧ (hours2.val[i]).val ≤ 100000)
    (hlen : hours1.val.length = hours2.val.length)
    (hle : ∀ (i : Nat) (hi : i < hours1.val.length),
      (hours1.val[i]).val ≤ (hours2.val.get ⟨i, by rw [← hlen]; exact hi⟩).val)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr1 : number_of_employees_who_met_target hours1 target = ok r1)
    (hr2 : number_of_employees_who_met_target hours2 target = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (hours1 hours2 : Slice Std.I64) (target : Std.I64) (r1 r2 : Std.I64)
    (h1_1 : 1 ≤ hours1.val.length) (h1_50 : hours1.val.length ≤ 50)
    (h1_val : ∀ (i : Nat) (hi : i < hours1.val.length),
      0 ≤ (hours1.val[i]).val ∧ (hours1.val[i]).val ≤ 100000)
    (h2_1 : 1 ≤ hours2.val.length) (h2_50 : hours2.val.length ≤ 50)
    (h2_val : ∀ (i : Nat) (hi : i < hours2.val.length),
      0 ≤ (hours2.val[i]).val ∧ (hours2.val[i]).val ≤ 100000)
    (hlen : hours1.val.length = hours2.val.length)
    (hle : ∀ (i : Nat) (hi : i < hours1.val.length),
      (hours1.val[i]).val ≤ (hours2.val.get ⟨i, by rw [← hlen]; exact hi⟩).val)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr1 : number_of_employees_who_met_target hours1 target = ok r1)
    (hr2 : number_of_employees_who_met_target hours2 target = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns a result r, r + c = len(hours), where c is the number of indices i with 0 <= i < len(hours) and hours[i] < target.
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; 0 <= target <= 100000. -/
theorem spec_10
    (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r) :
    r.val + (countLT hours.val target.val : Int) = (hours.val.length : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r), r.val + (countLT hours.val target.val : Int) = (hours.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, if r > 0 then there exists an index i with 0 <= i < len(hours) and hours[i] >= target.
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; 0 <= target <= 100000. -/
theorem spec_11
    (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r) :
    r.val > 0 → ∃ (i : Nat) (hi : i < hours.val.length),
      target.val ≤ (hours.val[i]).val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r), r.val > 0 → ∃ (i : Nat) (hi : i < hours.val.length),
      target.val ≤ (hours.val[i]).val) := by
  sorry

/-- Whenever the function returns a result r, if r < len(hours) then there exists an index i with 0 <= i < len(hours) and hours[i] < target.
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; 0 <= target <= 100000. -/
theorem spec_12
    (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r) :
    r.val < (hours.val.length : Int) →
      ∃ (i : Nat) (hi : i < hours.val.length), (hours.val[i]).val < target.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (hours : Slice Std.I64) (target : Std.I64) (n : Nat) (r : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hr : number_of_employees_who_met_target hours target = ok r), r.val < (hours.val.length : Int) →
      ∃ (i : Nat) (hi : i < hours.val.length), (hours.val[i]).val < target.val) := by
  sorry

/-- Let r1 be the result on hours1 and target, and let r2 be the result on hours2 and target. Whenever both calls return results, r1 = r2.
  Preconditions: hours1 and hours2 both satisfy 1 <= len <= 50 and all entries are in 0..100000; len(hours1) = len(hours2); 0 <= target <= 100000; for every i with 0 <= i < len(hours1), (hours1[i] >= target) if and only if (hours2[i] >= target). -/
theorem spec_13
    (hours1 hours2 : Slice Std.I64) (target : Std.I64) (r1 r2 : Std.I64)
    (h1_1 : 1 ≤ hours1.val.length) (h1_50 : hours1.val.length ≤ 50)
    (h1_val : ∀ (i : Nat) (hi : i < hours1.val.length),
      0 ≤ (hours1.val[i]).val ∧ (hours1.val[i]).val ≤ 100000)
    (h2_1 : 1 ≤ hours2.val.length) (h2_50 : hours2.val.length ≤ 50)
    (h2_val : ∀ (i : Nat) (hi : i < hours2.val.length),
      0 ≤ (hours2.val[i]).val ∧ (hours2.val[i]).val ≤ 100000)
    (hlen : hours1.val.length = hours2.val.length)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hiff : ∀ (i : Nat) (hi : i < hours1.val.length),
      (target.val ≤ (hours1.val[i]).val ↔
        target.val ≤ (hours2.val.get ⟨i, by rw [← hlen]; exact hi⟩).val))
    (hr1 : number_of_employees_who_met_target hours1 target = ok r1)
    (hr2 : number_of_employees_who_met_target hours2 target = ok r2) :
    r1.val = r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (hours1 hours2 : Slice Std.I64) (target : Std.I64) (r1 r2 : Std.I64)
    (h1_1 : 1 ≤ hours1.val.length) (h1_50 : hours1.val.length ≤ 50)
    (h1_val : ∀ (i : Nat) (hi : i < hours1.val.length),
      0 ≤ (hours1.val[i]).val ∧ (hours1.val[i]).val ≤ 100000)
    (h2_1 : 1 ≤ hours2.val.length) (h2_50 : hours2.val.length ≤ 50)
    (h2_val : ∀ (i : Nat) (hi : i < hours2.val.length),
      0 ≤ (hours2.val[i]).val ∧ (hours2.val[i]).val ≤ 100000)
    (hlen : hours1.val.length = hours2.val.length)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (hiff : ∀ (i : Nat) (hi : i < hours1.val.length),
      (target.val ≤ (hours1.val[i]).val ↔
        target.val ≤ (hours2.val.get ⟨i, by rw [← hlen]; exact hi⟩).val))
    (hr1 : number_of_employees_who_met_target hours1 target = ok r1)
    (hr2 : number_of_employees_who_met_target hours2 target = ok r2), r1.val = r2.val) := by
  sorry

/-- Let r_t be the result of the function on hours and target t, and let r_{t+1} be the result on hours and target t+1. Whenever both calls return results, r_t - r_{t+1} equals the number of indices i with 0 <= i < len(hours) and hours[i] = t.
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; t is an integer with 0 <= t <= 99999, so t and t+1 are admissible target values. -/
theorem spec_14
    (hours : Slice Std.I64) (n : Nat) (t t1 : Std.I64) (rt rt1 : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ t.val) (ht100 : t.val ≤ 99999)
    (ht1 : t1.val = t.val + 1)
    (hr1 : number_of_employees_who_met_target hours t = ok rt)
    (hr2 : number_of_employees_who_met_target hours t1 = ok rt1) :
    rt.val - rt1.val = (countEQ hours.val t.val : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (t t1 : Std.I64) (rt rt1 : Std.I64)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ t.val) (ht100 : t.val ≤ 99999)
    (ht1 : t1.val = t.val + 1)
    (hr1 : number_of_employees_who_met_target hours t = ok rt)
    (hr2 : number_of_employees_who_met_target hours t1 = ok rt1), rt.val - rt1.val = (countEQ hours.val t.val : Int)) := by
  sorry

/-- For every index i with 0 <= i < len(hours) and hours[i] = target, whenever the function returns a result r, r = 1 + the number of indices j with 0 <= j < len(hours), j != i, and hours[j] >= target.
  Preconditions: n = len(hours); 1 <= n <= 50; for every i with 0 <= i < n, 0 <= hours[i] <= 100000; 0 <= target <= 100000. -/
theorem spec_15
    (hours : Slice Std.I64) (target : Std.I64) (n : Nat)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (i : Nat) (hi : i < hours.val.length) (heq : (hours.val[i]).val = target.val)
    (r : Std.I64)
    (hr : number_of_employees_who_met_target hours target = ok r) :
    r.val = 1 + (countGE (hours.val.eraseIdx i) target.val : Int) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (hours : Slice Std.I64) (target : Std.I64) (n : Nat)
    (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < hours.val.length),
      0 ≤ (hours.val[i]).val ∧ (hours.val[i]).val ≤ 100000)
    (ht0 : 0 ≤ target.val) (ht100 : target.val ≤ 100000)
    (i : Nat) (hi : i < hours.val.length) (heq : (hours.val[i]).val = target.val)
    (r : Std.I64)
    (hr : number_of_employees_who_met_target hours target = ok r), r.val = 1 + (countGE (hours.val.eraseIdx i) target.val : Int)) := by
  sorry

end AegisSpec.NumberOfEmployeesWhoMetTarget
