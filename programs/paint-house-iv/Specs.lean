import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `paint-house-iv`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinCost

def row (cost : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List Std.I64 :=
  ((cost.val[i]?).map (fun r => r.val)).getD []

def cell (cost : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
  (((row cost i)[j]?).map (fun x => x.val)).getD 0

def IsBeautiful {m : ℕ} (c : Fin m → Fin 3) : Prop :=
  (∀ (i : ℕ) (h : i + 1 < m), c ⟨i, Nat.lt_of_succ_lt h⟩ ≠ c ⟨i + 1, h⟩) ∧
    ∀ (i : ℕ) (h : i < m / 2),
      c ⟨i, Nat.lt_of_lt_of_le h (Nat.div_le_self m 2)⟩ ≠
        c ⟨m - 1 - i, by have := Nat.div_le_self m 2; omega⟩

noncomputable def coloringCost (cost : Slice (alloc.vec.Vec Std.I64)) {m : ℕ}
    (c : Fin m → Fin 3) : ℤ :=
  ∑ i : Fin m, cell cost i (c i)

noncomputable def sumMin (cost : Slice (alloc.vec.Vec Std.I64)) (m : ℕ) : ℤ :=
  ∑ i : Fin m, min (cell cost i 0) (min (cell cost i 1) (cell cost i 2))

noncomputable def sumMax (cost : Slice (alloc.vec.Vec Std.I64)) (m : ℕ) : ℤ :=
  ∑ i : Fin m, max (cell cost i 0) (max (cell cost i 1) (cell cost i 2))

/-- For a sequence c of length n with c[i] in {0,1,2} for each i, call c beautiful if c[i] != c[i+1] for every 0 <= i < n-1 and c[i] != c[n-1-i] for every 0 <= i < n/2; its cost is sum_{i=0}^{n-1} cost[i][c[i]]. The function returns a result r and r = min { cost(c) | c is beautiful }.
  Preconditions: Assume the problem constraints hold: n, interpreted as an integer, satisfies 2 <= n <= 100000 and n is even; len(cost) = n; every row cost[i] has length 3; and 0 <= cost[i][j] <= 100000 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_1 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MinCost.min_cost n cost = ok r ∧
        IsLeast {v : ℤ | ∃ c : Fin n.val.toNat → Fin 3, IsBeautiful c ∧ coloringCost cost c = v}
          r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000), ∃ r : Std.I64,
      Aegis.MinCost.min_cost n cost = ok r ∧
        IsLeast {v : ℤ | ∃ c : Fin n.val.toNat → Fin 3, IsBeautiful c ∧ coloringCost cost c = v}
          r.val) := by
  sorry

/-- The function returns a result r and does not fail (no panic, out-of-bounds access, or arithmetic overflow) for every input satisfying the preconditions.
  Preconditions: Assume the problem constraints hold: n, interpreted as an integer, satisfies 2 <= n <= 100000 and n is even; len(cost) = n; every row cost[i] has length 3; and 0 <= cost[i][j] <= 100000 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_2 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000) :
    ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000), ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r) := by
  sorry

/-- The function returns a result r and r >= sum_{i=0}^{n-1} min(cost[i][0], cost[i][1], cost[i][2]).
  Preconditions: Assume the problem constraints hold: n, interpreted as an integer, satisfies 2 <= n <= 100000 and n is even; len(cost) = n; every row cost[i] has length 3; and 0 <= cost[i][j] <= 100000 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_3 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000) :
    ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      sumMin cost n.val.toNat ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000), ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      sumMin cost n.val.toNat ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= sum_{i=0}^{n-1} max(cost[i][0], cost[i][1], cost[i][2]).
  Preconditions: Assume the problem constraints hold: n, interpreted as an integer, satisfies 2 <= n <= 100000 and n is even; len(cost) = n; every row cost[i] has length 3; and 0 <= cost[i][j] <= 100000 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_4 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000) :
    ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      r.val ≤ sumMax cost n.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000), ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      r.val ≤ sumMax cost n.val.toNat) := by
  sorry

/-- For a sequence c of length n with c[i] in {0,1,2} for each i, call c beautiful if c[i] != c[i+1] for every 0 <= i < n-1 and c[i] != c[n-1-i] for every 0 <= i < n/2; its cost is sum_{i=0}^{n-1} cost[i][c[i]]. Whenever the function returns a result r, for every beautiful coloring c, r <= cost(c).
  Preconditions: Assume the problem constraints hold: n, interpreted as an integer, satisfies 2 <= n <= 100000 and n is even; len(cost) = n; every row cost[i] has length 3; and 0 <= cost[i][j] <= 100000 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_5 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000) :
    ∀ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r →
      ∀ c : Fin n.val.toNat → Fin 3, IsBeautiful c → r.val ≤ coloringCost cost c := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000), ∀ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r →
      ∀ c : Fin n.val.toNat → Fin 3, IsBeautiful c → r.val ≤ coloringCost cost c) := by
  sorry

/-- For a sequence c of length n with c[i] in {0,1,2} for each i, call c beautiful if c[i] != c[i+1] for every 0 <= i < n-1 and c[i] != c[n-1-i] for every 0 <= i < n/2; its cost is sum_{i=0}^{n-1} cost[i][c[i]]. The function returns a result r and there exists a beautiful coloring c such that cost(c) = r.
  Preconditions: Assume the problem constraints hold: n, interpreted as an integer, satisfies 2 <= n <= 100000 and n is even; len(cost) = n; every row cost[i] has length 3; and 0 <= cost[i][j] <= 100000 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_6 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000) :
    ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      ∃ c : Fin n.val.toNat → Fin 3, IsBeautiful c ∧ coloringCost cost c = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000), ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      ∃ c : Fin n.val.toNat → Fin 3, IsBeautiful c ∧ coloringCost cost c = r.val) := by
  sorry

/-- The function returns a result r and r = sum_{i=0}^{n-1} cost[i][0].
  Preconditions: Assume the problem constraints hold: n, interpreted as an integer, satisfies 2 <= n <= 100000 and n is even; len(cost) = n; every row cost[i] has length 3; and 0 <= cost[i][j] <= 100000 for every 0 <= i < n and 0 <= j < 3. Also cost[i][0] = cost[i][1] = cost[i][2] for every 0 <= i < n. -/
theorem spec_7 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (hconst : ∀ (i : ℕ), i < n.val.toNat →
      cell cost i 0 = cell cost i 1 ∧ cell cost i 1 = cell cost i 2) :
    ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      r.val = ∑ i : Fin n.val.toNat, cell cost i 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (hconst : ∀ (i : ℕ), i < n.val.toNat →
      cell cost i 0 = cell cost i 1 ∧ cell cost i 1 = cell cost i 2), ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      r.val = ∑ i : Fin n.val.toNat, cell cost i 0) := by
  sorry

/-- Let r be the result returned by the function on (n,cost) and r' the result returned on (n,cost'). Then r' = r + n*t.
  Preconditions: Assume the problem constraints hold: n, interpreted as an integer, satisfies 2 <= n <= 100000 and n is even; len(cost) = n; every row cost[i] has length 3; and 0 <= cost[i][j] <= 100000 for every 0 <= i < n and 0 <= j < 3. Let t be an integer with 0 <= t and cost[i][j] + t <= 100000 for all i,j, and define cost'[i][j] = cost[i][j] + t. -/
theorem spec_8 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (t : ℤ) (ht : 0 ≤ t)
    (hbound : ∀ (i j : ℕ), i < n.val.toNat → j < 3 → cell cost i j + t ≤ 100000)
    (cost' : Slice (alloc.vec.Vec Std.I64))
    (hlen' : cost'.val.length = n.val.toNat)
    (hrows' : ∀ (i : ℕ) (hi : i < cost'.val.length), (cost'.val[i]'hi).val.length = 3)
    (hcost' : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      cell cost' i j = cell cost i j + t) :
    ∀ r r' : Std.I64, Aegis.MinCost.min_cost n cost = ok r →
      Aegis.MinCost.min_cost n cost' = ok r' → r'.val = r.val + n.val * t := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (t : ℤ) (ht : 0 ≤ t)
    (hbound : ∀ (i j : ℕ), i < n.val.toNat → j < 3 → cell cost i j + t ≤ 100000)
    (cost' : Slice (alloc.vec.Vec Std.I64))
    (hlen' : cost'.val.length = n.val.toNat)
    (hrows' : ∀ (i : ℕ) (hi : i < cost'.val.length), (cost'.val[i]'hi).val.length = 3)
    (hcost' : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      cell cost' i j = cell cost i j + t), ∀ r r' : Std.I64, Aegis.MinCost.min_cost n cost = ok r →
      Aegis.MinCost.min_cost n cost' = ok r' → r'.val = r.val + n.val * t) := by
  sorry

/-- Let r be the result returned by the function on (n,cost) and r' the result returned on (n,cost'). Then r' = r.
  Preconditions: Assume the problem constraints hold: n, interpreted as an integer, satisfies 2 <= n <= 100000 and n is even; len(cost) = n; every row cost[i] has length 3; and 0 <= cost[i][j] <= 100000 for every 0 <= i < n and 0 <= j < 3. Let pi be a permutation of {0,1,2} and let cost' be a matrix with len(cost') = n, each row length 3, and cost'[i][pi(j)] = cost[i][j] for all i,j. -/
theorem spec_9 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (pi : Fin 3 ≃ Fin 3)
    (cost' : Slice (alloc.vec.Vec Std.I64))
    (hlen' : cost'.val.length = n.val.toNat)
    (hrows' : ∀ (i : ℕ) (hi : i < cost'.val.length), (cost'.val[i]'hi).val.length = 3)
    (hcost' : ∀ (i j : ℕ) (hj : j < 3),
      i < n.val.toNat → cell cost' i ((pi ⟨j, hj⟩ : Fin 3) : ℕ) = cell cost i j) :
    ∀ r r' : Std.I64, Aegis.MinCost.min_cost n cost = ok r →
      Aegis.MinCost.min_cost n cost' = ok r' → r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (pi : Fin 3 ≃ Fin 3)
    (cost' : Slice (alloc.vec.Vec Std.I64))
    (hlen' : cost'.val.length = n.val.toNat)
    (hrows' : ∀ (i : ℕ) (hi : i < cost'.val.length), (cost'.val[i]'hi).val.length = 3)
    (hcost' : ∀ (i j : ℕ) (hj : j < 3),
      i < n.val.toNat → cell cost' i ((pi ⟨j, hj⟩ : Fin 3) : ℕ) = cell cost i j), ∀ r r' : Std.I64, Aegis.MinCost.min_cost n cost = ok r →
      Aegis.MinCost.min_cost n cost' = ok r' → r'.val = r.val) := by
  sorry

/-- Let r be the result returned by the function on (n,cost) and r' the result returned on (n,cost'). Then r' >= r.
  Preconditions: Assume the problem constraints hold for both cost and cost' with the same n: n is even, 2 <= n <= 100000, len(cost) = len(cost') = n, every row has length 3, and all entries are between 0 and 100000. Also cost'[i][j] >= cost[i][j] for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_10 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (cost' : Slice (alloc.vec.Vec Std.I64))
    (hlen' : cost'.val.length = n.val.toNat)
    (hrows' : ∀ (i : ℕ) (hi : i < cost'.val.length), (cost'.val[i]'hi).val.length = 3)
    (hentries' : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost' i j ∧ cell cost' i j ≤ 100000)
    (hmono : ∀ (i j : ℕ), i < n.val.toNat → j < 3 → cell cost i j ≤ cell cost' i j) :
    ∀ r r' : Std.I64, Aegis.MinCost.min_cost n cost = ok r →
      Aegis.MinCost.min_cost n cost' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (cost' : Slice (alloc.vec.Vec Std.I64))
    (hlen' : cost'.val.length = n.val.toNat)
    (hrows' : ∀ (i : ℕ) (hi : i < cost'.val.length), (cost'.val[i]'hi).val.length = 3)
    (hentries' : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost' i j ∧ cell cost' i j ≤ 100000)
    (hmono : ∀ (i j : ℕ), i < n.val.toNat → j < 3 → cell cost i j ≤ cell cost' i j), ∀ r r' : Std.I64, Aegis.MinCost.min_cost n cost = ok r →
      Aegis.MinCost.min_cost n cost' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r and r = sum_{i=0}^{n-1} min(cost[i][0], cost[i][1], cost[i][2]).
  Preconditions: Assume the problem constraints hold: n, interpreted as an integer, satisfies 2 <= n <= 100000 and n is even; len(cost) = n; every row cost[i] has length 3; and 0 <= cost[i][j] <= 100000 for every 0 <= i < n and 0 <= j < 3. Moreover, there is a sequence c of length n with c[i] in {0,1,2} for every i, such that c[i] != c[i+1] for every 0 <= i < n-1, c[i] != c[n-1-i] for every 0 <= i < n/2, and cost[i][c[i]] = min(cost[i][0], cost[i][1], cost[i][2]) for every 0 <= i < n. -/
theorem spec_11 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (hmin : ∃ c : Fin n.val.toNat → Fin 3, IsBeautiful c ∧
      ∀ i : Fin n.val.toNat,
        cell cost i (c i) = min (cell cost i 0) (min (cell cost i 1) (cell cost i 2))) :
    ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      r.val = sumMin cost n.val.toNat := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (hmin : ∃ c : Fin n.val.toNat → Fin 3, IsBeautiful c ∧
      ∀ i : Fin n.val.toNat,
        cell cost i (c i) = min (cell cost i 0) (min (cell cost i 1) (cell cost i 2))), ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      r.val = sumMin cost n.val.toNat) := by
  sorry

/-- The function returns a result r and r <= sum_{i=0}^{n-1} cost[i][i mod 2].
  Preconditions: Assume the problem constraints hold: n, interpreted as an integer, satisfies 2 <= n <= 100000 and n is even; len(cost) = n; every row cost[i] has length 3; and 0 <= cost[i][j] <= 100000 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_12 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000) :
    ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      r.val ≤ ∑ i : Fin n.val.toNat, cell cost i ((i : ℕ) % 2) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000), ∃ r : Std.I64, Aegis.MinCost.min_cost n cost = ok r ∧
      r.val ≤ ∑ i : Fin n.val.toNat, cell cost i ((i : ℕ) % 2)) := by
  sorry

/-- Let r be the result returned by the function on (n,cost) and r' the result returned on (n,cost'). Then r' = r + sum_{i=0}^{n-1} a[i].
  Preconditions: Assume the problem constraints hold for cost: n is even, 2 <= n <= 100000, len(cost) = n, every row has length 3, and 0 <= cost[i][j] <= 100000. Let a be a sequence of integers indexed 0..n-1 such that 0 <= cost[i][j] + a[i] <= 100000 for all i,j, and define cost'[i][j] = cost[i][j] + a[i]. -/
theorem spec_13 (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (a : Fin n.val.toNat → ℤ)
    (ha : ∀ (i : Fin n.val.toNat) (j : ℕ), j < 3 →
      0 ≤ cell cost i j + a i ∧ cell cost i j + a i ≤ 100000)
    (cost' : Slice (alloc.vec.Vec Std.I64))
    (hlen' : cost'.val.length = n.val.toNat)
    (hrows' : ∀ (i : ℕ) (hi : i < cost'.val.length), (cost'.val[i]'hi).val.length = 3)
    (hcost' : ∀ (i : Fin n.val.toNat) (j : ℕ), j < 3 →
      cell cost' i j = cell cost i j + a i) :
    ∀ r r' : Std.I64, Aegis.MinCost.min_cost n cost = ok r →
      Aegis.MinCost.min_cost n cost' = ok r' →
      r'.val = r.val + ∑ i : Fin n.val.toNat, a i := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (cost : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000) (hn_even : n.val % 2 = 0)
    (hlen : cost.val.length = n.val.toNat)
    (hrows : ∀ (i : ℕ) (hi : i < cost.val.length), (cost.val[i]'hi).val.length = 3)
    (hentries : ∀ (i j : ℕ), i < n.val.toNat → j < 3 →
      0 ≤ cell cost i j ∧ cell cost i j ≤ 100000)
    (a : Fin n.val.toNat → ℤ)
    (ha : ∀ (i : Fin n.val.toNat) (j : ℕ), j < 3 →
      0 ≤ cell cost i j + a i ∧ cell cost i j + a i ≤ 100000)
    (cost' : Slice (alloc.vec.Vec Std.I64))
    (hlen' : cost'.val.length = n.val.toNat)
    (hrows' : ∀ (i : ℕ) (hi : i < cost'.val.length), (cost'.val[i]'hi).val.length = 3)
    (hcost' : ∀ (i : Fin n.val.toNat) (j : ℕ), j < 3 →
      cell cost' i j = cell cost i j + a i), ∀ r r' : Std.I64, Aegis.MinCost.min_cost n cost = ok r →
      Aegis.MinCost.min_cost n cost' = ok r' →
      r'.val = r.val + ∑ i : Fin n.val.toNat, a i) := by
  sorry

end AegisSpec.MinCost
