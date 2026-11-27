import Aegis.MinimumMoney.Code.Funs

/-!
# Specifications of `Aegis.MinimumMoney.minimum_money`

LeetCode problem `minimum-money-required-before-transactions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumMoney

open Aegis.MinimumMoney

def entry (transactions : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
  match transactions.val[i]? with
  | none => 0
  | some v =>
    match v.val[j]? with
    | none => 0
    | some x => x.val

def cost (transactions : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
  entry transactions i 0

def cash (transactions : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
  entry transactions i 1

def txnLen (transactions : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℕ :=
  match transactions.val[i]? with
  | none => 0
  | some v => v.val.length

def IsPerm (n : ℕ) (p : List ℕ) : Prop :=
  p.Perm (List.range n)

def prefixNet (transactions : Slice (alloc.vec.Vec Std.I64)) (p : List ℕ) (k : ℕ) : ℤ :=
  ((p.take k).map (fun j => cash transactions j - cost transactions j)).sum

def prefixLoss (transactions : Slice (alloc.vec.Vec Std.I64)) (p : List ℕ) (k : ℕ) : ℤ :=
  ((p.take k).map (fun j => cost transactions j - cash transactions j)).sum

def Succeeds (transactions : Slice (alloc.vec.Vec Std.I64)) (M : ℤ) (p : List ℕ) : Prop :=
  ∀ k (hk : k < p.length), M + prefixNet transactions p k ≥ cost transactions (p.get ⟨k, hk⟩)

def listMax (l : List ℤ) : ℤ :=
  l.foldr max 0

def need (transactions : Slice (alloc.vec.Vec Std.I64)) (p : List ℕ) : ℤ :=
  listMax (p.zipIdx.map (fun ik => cost transactions ik.1 + prefixLoss transactions p ik.2))

def totalLoss (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : ℤ :=
  ((List.range n).map (fun i => max 0 (cost transactions i - cash transactions i))).sum

def maxMin (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : ℤ :=
  listMax ((List.range n).map (fun i => min (cost transactions i) (cash transactions i)))

def sumCost (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : ℤ :=
  ((List.range n).map (fun i => cost transactions i)).sum

def permute (transactions : Slice (alloc.vec.Vec Std.I64)) (q : List ℕ) :
    List (alloc.vec.Vec Std.I64) :=
  q.filterMap (fun i => transactions.val[i]?)

/-- The function returns a result r and r is the least nonnegative integer with the following property: for every permutation p of the transactions (a sequence of length n containing each index 0,1,...,n-1 exactly once), the order p succeeds from initial amount r, meaning that for every k with 0 <= k < n, r + Σ_{j=0}^{k-1} (cash_{p[j]} - cost_{p[j]}) >= cost_{p[k]}, where the sum for k = 0 is empty and equals 0. Equivalently, r >= 0, every permutation succeeds from r, and for every integer M with 0 <= M < r there exists a permutation p that does not succeed from M.
  Preconditions: Let n = len(transactions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(transactions[i]) = 2, and if cost_i = transactions[i][0] and cash_i = transactions[i][1], then 0 <= cost_i <= 1000000000 and 0 <= cash_i <= 1000000000. All stated arithmetic is mathematical integer arithmetic; under these assumptions the quantities mentioned are within signed 64-bit range. -/
theorem spec_1 (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000) :
    ∃ r : Std.I64,
      minimum_money transactions = Result.ok r ∧
        0 ≤ r.val ∧
          (∀ p, IsPerm n p → Succeeds transactions r.val p) ∧
            (∀ M : ℤ, 0 ≤ M → M < r.val →
              ∃ p, IsPerm n p ∧ ¬ Succeeds transactions M p) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000), ∃ r : Std.I64,
      minimum_money transactions = Result.ok r ∧
        0 ≤ r.val ∧
          (∀ p, IsPerm n p → Succeeds transactions r.val p) ∧
            (∀ M : ℤ, 0 ≤ M → M < r.val →
              ∃ p, IsPerm n p ∧ ¬ Succeeds transactions M p)) := by
  sorry

/-- For every input satisfying the preconditions, the function does not fail: it returns a result r (a Std.I64 value).
  Preconditions: Let n = len(transactions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(transactions[i]) = 2, and if cost_i = transactions[i][0] and cash_i = transactions[i][1], then 0 <= cost_i <= 1000000000 and 0 <= cash_i <= 1000000000. -/
theorem spec_2 (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000) :
    ∃ r : Std.I64, minimum_money transactions = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000), ∃ r : Std.I64, minimum_money transactions = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, for every permutation p of the transactions (a sequence of length n containing each index exactly once), the order p succeeds from initial amount r; that is, for every k with 0 <= k < n, r + Σ_{j=0}^{k-1} (cash_{p[j]} - cost_{p[j]}) >= cost_{p[k]}, with empty sum 0 for k=0.
  Preconditions: Let n = len(transactions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(transactions[i]) = 2, and if cost_i = transactions[i][0] and cash_i = transactions[i][1], then 0 <= cost_i <= 1000000000 and 0 <= cash_i <= 1000000000. -/
theorem spec_3 (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r) :
    ∀ p, IsPerm n p → Succeeds transactions r.val p := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r), ∀ p, IsPerm n p → Succeeds transactions r.val p) := by
  sorry

/-- Whenever the function returns a result r, for every integer M with 0 <= M < r there exists a permutation p of the transactions such that the order p does not succeed from M; explicitly, there is some k with 0 <= k < n for which M + Σ_{j=0}^{k-1} (cash_{p[j]} - cost_{p[j]}) < cost_{p[k]}.
  Preconditions: Let n = len(transactions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(transactions[i]) = 2, and if cost_i = transactions[i][0] and cash_i = transactions[i][1], then 0 <= cost_i <= 1000000000 and 0 <= cash_i <= 1000000000. -/
theorem spec_4 (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r) :
    ∀ M : ℤ, 0 ≤ M → M < r.val → ∃ p, IsPerm n p ∧ ¬ Succeeds transactions M p := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r), ∀ M : ℤ, 0 ≤ M → M < r.val → ∃ p, IsPerm n p ∧ ¬ Succeeds transactions M p) := by
  sorry

/-- Whenever the function returns a result r, r = (Σ_{i=0}^{n-1} max(0, cost_i - cash_i)) + max_{0 <= i < n} min(cost_i, cash_i).
  Preconditions: Let n = len(transactions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(transactions[i]) = 2, and if cost_i = transactions[i][0] and cash_i = transactions[i][1], then 0 <= cost_i <= 1000000000 and 0 <= cash_i <= 1000000000. -/
theorem spec_5 (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r) :
    r.val = totalLoss transactions n + maxMin transactions n := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r), r.val = totalLoss transactions n + maxMin transactions n) := by
  sorry

/-- Whenever the function returns a result r, there exists a permutation p of the transactions such that need(p) = r, where need(p) = max_{0 <= k < n} ( cost_{p[k]} + Σ_{j=0}^{k-1} (cost_{p[j]} - cash_{p[j]}) ), with the empty sum for k=0 equal to 0.
  Preconditions: Let n = len(transactions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(transactions[i]) = 2, and if cost_i = transactions[i][0] and cash_i = transactions[i][1], then 0 <= cost_i <= 1000000000 and 0 <= cash_i <= 1000000000. -/
theorem spec_6 (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r) :
    ∃ p, IsPerm n p ∧ need transactions p = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r), ∃ p, IsPerm n p ∧ need transactions p = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r >= cost_i.
  Preconditions: Let n = len(transactions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(transactions[i]) = 2, and if cost_i = transactions[i][0] and cash_i = transactions[i][1], then 0 <= cost_i <= 1000000000 and 0 <= cash_i <= 1000000000. -/
theorem spec_7 (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r) :
    ∀ i, i < n → r.val ≥ cost transactions i := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r), ∀ i, i < n → r.val ≥ cost transactions i) := by
  sorry

/-- Whenever the function returns a result r, r <= Σ_{i=0}^{n-1} cost_i.
  Preconditions: Let n = len(transactions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(transactions[i]) = 2, and if cost_i = transactions[i][0] and cash_i = transactions[i][1], then 0 <= cost_i <= 1000000000 and 0 <= cash_i <= 1000000000. -/
theorem spec_8 (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r) :
    r.val ≤ sumCost transactions n := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r), r.val ≤ sumCost transactions n) := by
  sorry

/-- Let q be any permutation of the index set {0,1,...,n-1}, and let transactions2 be the slice of length n defined by transactions2[i] = transactions[q[i]] for 0 <= i < n. Whenever minimum_money(transactions) returns r and minimum_money(transactions2) returns r2, we have r = r2.
  Preconditions: Let n = len(transactions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(transactions[i]) = 2, and if cost_i = transactions[i][0] and cash_i = transactions[i][1], then 0 <= cost_i <= 1000000000 and 0 <= cash_i <= 1000000000. -/
theorem spec_9 (transactions transactions2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (q : List ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (hq : IsPerm n q) (h2 : transactions2.val = permute transactions q)
    (r r2 : Std.I64) (hr : minimum_money transactions = Result.ok r)
    (hr2 : minimum_money transactions2 = Result.ok r2) :
    r = r2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (transactions transactions2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (q : List ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (hq : IsPerm n q) (h2 : transactions2.val = permute transactions q)
    (r r2 : Std.I64) (hr : minimum_money transactions = Result.ok r)
    (hr2 : minimum_money transactions2 = Result.ok r2), r = r2) := by
  sorry

/-- Whenever the function returns a result r, for every integer M with M >= r and every permutation p of the transactions, the order p succeeds from M; that is, for every k with 0 <= k < n, M + Σ_{j=0}^{k-1} (cash_{p[j]} - cost_{p[j]}) >= cost_{p[k]}, with empty sum 0 for k=0.
  Preconditions: Let n = len(transactions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(transactions[i]) = 2, and if cost_i = transactions[i][0] and cash_i = transactions[i][1], then 0 <= cost_i <= 1000000000 and 0 <= cash_i <= 1000000000. -/
theorem spec_10 (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r) :
    ∀ M : ℤ, r.val ≤ M → ∀ p, IsPerm n p → Succeeds transactions M p := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (transactions : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : transactions.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len : ∀ i, i < n → txnLen transactions i = 2)
    (h_cost : ∀ i, i < n → 0 ≤ cost transactions i ∧ cost transactions i ≤ 1000000000)
    (h_cash : ∀ i, i < n → 0 ≤ cash transactions i ∧ cash transactions i ≤ 1000000000)
    (r : Std.I64) (hr : minimum_money transactions = Result.ok r), ∀ M : ℤ, r.val ≤ M → ∀ p, IsPerm n p → Succeeds transactions M p) := by
  sorry

end AegisSpec.MinimumMoney
