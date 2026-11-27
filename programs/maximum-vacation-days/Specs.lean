import Aegis.MaxVacationDays.Code.Funs

/-!
# Specifications of `Aegis.MaxVacationDays.max_vacation_days`

LeetCode problem `maximum-vacation-days`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxVacationDays (max_vacation_days)

namespace AegisSpec.MaxVacationDays

def row (m : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  (m.val[i]?).map (fun r => r.val.map (fun x => x.val)) |>.getD []

def cell (m : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  (row m i)[j]?.getD 0

def total (days : Slice (alloc.vec.Vec Std.I64)) (k : Nat) (c : Nat → Nat) : Int :=
  ∑ j ∈ Finset.range k, cell days (c j) j

def Feasible (flights : Slice (alloc.vec.Vec Std.I64)) (n k : Nat) (c : Nat → Nat) : Prop :=
  (∀ j, j < k → c j < n) ∧
    (c 0 = 0 ∨ cell flights 0 (c 0) = 1) ∧
    (∀ j, 0 < j → j < k → c j = c (j - 1) ∨ cell flights (c (j - 1)) (c j) = 1)

def colMax (days : Slice (alloc.vec.Vec Std.I64)) (n j : Nat) : Int :=
  match n with
  | 0 => 0
  | m + 1 =>
    Finset.sup' (Finset.range (m + 1)) ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩
      (fun i => cell days i j)

def achievable (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat) : Set Int :=
  {v : Int | ∃ c : Nat → Nat, Feasible flights n k c ∧ total days k c = v}

/-- The function returns a result r (it does not fail), and r = max { sum_{j=0}^{k-1} days[c_j][j] : (c_0,...,c_{k-1}) is a sequence of city indices with 0 <= c_j < n for all j, c_0 = 0 or flights[0][c_0] = 1, and for every j with 1 <= j < k, c_j = c_{j-1} or flights[c_{j-1}][c_j] = 1 }.
  Preconditions: Let n = len(flights) and k = len(days[0]). The inputs satisfy the problem constraints: 1 <= n <= 100; 1 <= k <= 100; len(days) = n; for every i with 0 <= i < n, len(flights[i]) = n and len(days[i]) = k; for every i, j with 0 <= i < n and 0 <= j < n, flights[i][j] is 0 or 1; for every i with 0 <= i < n, flights[i][i] = 0; for every i, j with 0 <= i < n and 0 <= j < k, 0 <= days[i][j] <= 7. -/
theorem spec_1 (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7) :
    ∃ r : Std.I64,
      max_vacation_days flights days = ok r ∧ IsGreatest (achievable flights days n k) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7), ∃ r : Std.I64,
      max_vacation_days flights days = ok r ∧ IsGreatest (achievable flights days n k) r.val) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: Let n = len(flights) and k = len(days[0]). The inputs satisfy the problem constraints: 1 <= n <= 100; 1 <= k <= 100; len(days) = n; for every i with 0 <= i < n, len(flights[i]) = n and len(days[i]) = k; for every i, j with 0 <= i < n and 0 <= j < n, flights[i][j] is 0 or 1; for every i with 0 <= i < n, flights[i][i] = 0; for every i, j with 0 <= i < n and 0 <= j < k, 0 <= days[i][j] <= 7. -/
theorem spec_2 (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7) :
    ∃ r : Std.I64, max_vacation_days flights days = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7), ∃ r : Std.I64, max_vacation_days flights days = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= sum_{j=0}^{k-1} (max_{0 <= i < n} days[i][j]).
  Preconditions: Let n = len(flights) and k = len(days[0]). The inputs satisfy the problem constraints: 1 <= n <= 100; 1 <= k <= 100; len(days) = n; for every i with 0 <= i < n, len(flights[i]) = n and len(days[i]) = k; for every i, j with 0 <= i < n and 0 <= j < n, flights[i][j] is 0 or 1; for every i with 0 <= i < n, flights[i][i] = 0; for every i, j with 0 <= i < n and 0 <= j < k, 0 <= days[i][j] <= 7. -/
theorem spec_3 (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (r : Std.I64) (hr : max_vacation_days flights days = ok r) :
    0 ≤ r.val ∧ r.val ≤ ∑ j ∈ Finset.range k, colMax days n j := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (r : Std.I64) (hr : max_vacation_days flights days = ok r), 0 ≤ r.val ∧ r.val ≤ ∑ j ∈ Finset.range k, colMax days n j) := by
  sorry

/-- Whenever the function returns a result r, there exists a feasible city sequence (c_0,...,c_{k-1}) such that r = sum_{j=0}^{k-1} days[c_j][j]. Here feasible means: 0 <= c_j < n for every j; c_0 = 0 or flights[0][c_0] = 1; and for every j with 1 <= j < k, c_j = c_{j-1} or flights[c_{j-1}][c_j] = 1.
  Preconditions: Let n = len(flights) and k = len(days[0]). The inputs satisfy the problem constraints: 1 <= n <= 100; 1 <= k <= 100; len(days) = n; for every i with 0 <= i < n, len(flights[i]) = n and len(days[i]) = k; for every i, j with 0 <= i < n and 0 <= j < n, flights[i][j] is 0 or 1; for every i with 0 <= i < n, flights[i][i] = 0; for every i, j with 0 <= i < n and 0 <= j < k, 0 <= days[i][j] <= 7. -/
theorem spec_4 (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (r : Std.I64) (hr : max_vacation_days flights days = ok r) :
    ∃ c : Nat → Nat, Feasible flights n k c ∧ r.val = total days k c := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (r : Std.I64) (hr : max_vacation_days flights days = ok r), ∃ c : Nat → Nat, Feasible flights n k c ∧ r.val = total days k c) := by
  sorry

/-- Whenever the function returns a result r, for every feasible city sequence (c_0,...,c_{k-1}) (where feasible means: 0 <= c_j < n for every j; c_0 = 0 or flights[0][c_0] = 1; and for every j with 1 <= j < k, c_j = c_{j-1} or flights[c_{j-1}][c_j] = 1), we have sum_{j=0}^{k-1} days[c_j][j] <= r.
  Preconditions: Let n = len(flights) and k = len(days[0]). The inputs satisfy the problem constraints: 1 <= n <= 100; 1 <= k <= 100; len(days) = n; for every i with 0 <= i < n, len(flights[i]) = n and len(days[i]) = k; for every i, j with 0 <= i < n and 0 <= j < n, flights[i][j] is 0 or 1; for every i with 0 <= i < n, flights[i][i] = 0; for every i, j with 0 <= i < n and 0 <= j < k, 0 <= days[i][j] <= 7. -/
theorem spec_5 (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (r : Std.I64) (hr : max_vacation_days flights days = ok r) :
    ∀ c : Nat → Nat, Feasible flights n k c → total days k c ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (r : Std.I64) (hr : max_vacation_days flights days = ok r), ∀ c : Nat → Nat, Feasible flights n k c → total days k c ≤ r.val) := by
  sorry

/-- If for every i, j with 0 <= i < n and 0 <= j < n we have flights[i][j] <= flights'[i][j], then whenever max_vacation_days(flights, days) returns r and max_vacation_days(flights', days) returns r', we have r <= r'.
  Preconditions: Let n = len(flights) = len(flights') and k = len(days[0]). Both (flights, days) and (flights', days) satisfy the problem constraints: 1 <= n <= 100; 1 <= k <= 100; len(days) = n; every row of flights and flights' has length n; every row of days has length k; all entries of flights and flights' are 0 or 1; flights[i][i] = 0 and flights'[i][i] = 0 for every i; 0 <= days[i][j] <= 7 for every i, j. -/
theorem spec_6 (flights flights' days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_flights' : flights'.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_flights' : ∀ i, i < n → (row flights' i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights'_bool : ∀ i j, i < n → j < n → cell flights' i j = 0 ∨ cell flights' i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hflights'_diag : ∀ i, i < n → cell flights' i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (hle : ∀ i j, i < n → j < n → cell flights i j ≤ cell flights' i j)
    (r r' : Std.I64)
    (hr : max_vacation_days flights days = ok r)
    (hr' : max_vacation_days flights' days = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (flights flights' days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_flights' : flights'.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_flights' : ∀ i, i < n → (row flights' i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights'_bool : ∀ i j, i < n → j < n → cell flights' i j = 0 ∨ cell flights' i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hflights'_diag : ∀ i, i < n → cell flights' i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (hle : ∀ i j, i < n → j < n → cell flights i j ≤ cell flights' i j)
    (r r' : Std.I64)
    (hr : max_vacation_days flights days = ok r)
    (hr' : max_vacation_days flights' days = ok r'), r.val ≤ r'.val) := by
  sorry

/-- If for every i, j with 0 <= i < n and 0 <= j < k we have days[i][j] <= days'[i][j], then whenever max_vacation_days(flights, days) returns r and max_vacation_days(flights, days') returns r', we have r <= r'.
  Preconditions: Let n = len(flights) and k = len(days[0]) = len(days'[0]). Both (flights, days) and (flights, days') satisfy the problem constraints: 1 <= n <= 100; 1 <= k <= 100; len(days) = len(days') = n; flights has n rows of length n with entries 0 or 1 and flights[i][i] = 0 for every i; every row of days and days' has length k; 0 <= days[i][j] <= 7 and 0 <= days'[i][j] <= 7 for every i, j. -/
theorem spec_7 (flights days days' : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hlen_days' : days'.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hrow_days' : ∀ i, i < n → (row days' i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (hdays'_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days' i j ∧ cell days' i j ≤ 7)
    (hle : ∀ i j, i < n → j < k → cell days i j ≤ cell days' i j)
    (r r' : Std.I64)
    (hr : max_vacation_days flights days = ok r)
    (hr' : max_vacation_days flights days' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (flights days days' : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hlen_days' : days'.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hrow_days' : ∀ i, i < n → (row days' i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (hdays'_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days' i j ∧ cell days' i j ≤ 7)
    (hle : ∀ i j, i < n → j < k → cell days i j ≤ cell days' i j)
    (r r' : Std.I64)
    (hr : max_vacation_days flights days = ok r)
    (hr' : max_vacation_days flights days' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns a result r, r >= sum_{j=0}^{k-1} days[0][j].
  Preconditions: Let n = len(flights) and k = len(days[0]). The inputs satisfy the problem constraints: 1 <= n <= 100; 1 <= k <= 100; len(days) = n; for every i with 0 <= i < n, len(flights[i]) = n and len(days[i]) = k; for every i, j with 0 <= i < n and 0 <= j < n, flights[i][j] is 0 or 1; for every i with 0 <= i < n, flights[i][i] = 0; for every i, j with 0 <= i < n and 0 <= j < k, 0 <= days[i][j] <= 7. -/
theorem spec_8 (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (r : Std.I64) (hr : max_vacation_days flights days = ok r) :
    (∑ j ∈ Finset.range k, cell days 0 j) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (flights days : Slice (alloc.vec.Vec Std.I64)) (n k : Nat)
    (hn1 : 1 ≤ n) (hn100 : n ≤ 100) (hk1 : 1 ≤ k) (hk100 : k ≤ 100)
    (hlen_flights : flights.val.length = n)
    (hlen_days : days.val.length = n)
    (hrow_flights : ∀ i, i < n → (row flights i).length = n)
    (hrow_days : ∀ i, i < n → (row days i).length = k)
    (hflights_bool : ∀ i j, i < n → j < n → cell flights i j = 0 ∨ cell flights i j = 1)
    (hflights_diag : ∀ i, i < n → cell flights i i = 0)
    (hdays_bounds : ∀ i j, i < n → j < k → 0 ≤ cell days i j ∧ cell days i j ≤ 7)
    (r : Std.I64) (hr : max_vacation_days flights days = ok r), (∑ j ∈ Finset.range k, cell days 0 j) ≤ r.val) := by
  sorry

end AegisSpec.MaxVacationDays
