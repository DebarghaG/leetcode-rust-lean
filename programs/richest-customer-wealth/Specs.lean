import Aegis.MaximumWealth.Code.Funs

/-!
# Specifications of `Aegis.MaximumWealth.maximum_wealth`

LeetCode problem `richest-customer-wealth`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumWealth

  def rowWealth (row : alloc.vec.Vec Std.I64) : Int :=
    (row.val.map (fun x => x.val)).sum

  def wealths (accounts : Slice (alloc.vec.Vec Std.I64)) : List Int :=
    accounts.val.map rowWealth

  def rowLengths (accounts : Slice (alloc.vec.Vec Std.I64)) : List Nat :=
    accounts.val.map (fun row => row.val.length)

  def intMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl (fun acc y => max acc y) x

  def natMax : List Nat → Nat
    | [] => 0
    | x :: xs => xs.foldl (fun acc y => max acc y) x

  def AppendsRow (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
      (w : alloc.vec.Vec Std.I64) : Prop :=
    accounts'.val = accounts.val ++ [w]

  def IsRowPermutation (accounts accounts' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    accounts'.val.Perm accounts.val

  def RowsPointwiseLe (accounts accounts' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    List.Forall₂
      (fun r r' => List.Forall₂ (fun (a b : Std.I64) => a.val ≤ b.val) r.val r'.val)
      accounts.val accounts'.val

  def RowsSameWealth (accounts accounts' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    List.Forall₂ (fun r r' => r.val.length = r'.val.length ∧ rowWealth r = rowWealth r')
      accounts.val accounts'.val

  /-- Let wealth(i) = sum_{j=0}^{len(accounts[i])-1} accounts[i][j] for 0 <= i < len(accounts). Whenever maximum_wealth(accounts) returns a result r, r = max { wealth(i) | 0 <= i < len(accounts) }.
    Preconditions: 1 <= len(accounts) <= 50; for every i with 0 <= i < len(accounts), 1 <= len(accounts[i]) <= 50; for every i and j with 0 <= i < len(accounts) and 0 <= j < len(accounts[i]), 1 <= accounts[i][j] <= 100. -/
  theorem spec_1 (accounts : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (r : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r) :
      r.val = intMax (wealths accounts) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (accounts : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (r : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r), r.val = intMax (wealths accounts)) := by
    sorry

  /-- For every accounts satisfying the preconditions, maximum_wealth(accounts) returns a result r; it does not fail, overflow, or go out of bounds.
    Preconditions: 1 <= len(accounts) <= 50; for every i with 0 <= i < len(accounts), 1 <= len(accounts[i]) <= 50; for every i and j with 0 <= i < len(accounts) and 0 <= j < len(accounts[i]), 1 <= accounts[i][j] <= 100. -/
  theorem spec_2 (accounts : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r : Std.I64, Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (accounts : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100), ∃ r : Std.I64, Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r) := by
    sorry

  /-- Let wealth(i) = sum_{j=0}^{len(accounts[i])-1} accounts[i][j] for 0 <= i < len(accounts). Whenever maximum_wealth(accounts) returns a result r, for every i with 0 <= i < len(accounts), r >= wealth(i).
    Preconditions: 1 <= len(accounts) <= 50; for every i with 0 <= i < len(accounts), 1 <= len(accounts[i]) <= 50; for every i and j with 0 <= i < len(accounts) and 0 <= j < len(accounts[i]), 1 <= accounts[i][j] <= 100. -/
  theorem spec_3 (accounts : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (r : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r) :
      ∀ row ∈ accounts.val, rowWealth row ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (accounts : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (r : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r), ∀ row ∈ accounts.val, rowWealth row ≤ r.val) := by
    sorry

  /-- Whenever maximum_wealth(accounts) returns a result r, r <= sum_{i=0}^{len(accounts)-1} sum_{j=0}^{len(accounts[i])-1} accounts[i][j].
    Preconditions: 1 <= len(accounts) <= 50; for every i with 0 <= i < len(accounts), 1 <= len(accounts[i]) <= 50; for every i and j with 0 <= i < len(accounts) and 0 <= j < len(accounts[i]), 1 <= accounts[i][j] <= 100. -/
  theorem spec_4 (accounts : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (r : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r) :
      r.val ≤ (wealths accounts).sum := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (accounts : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (r : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r), r.val ≤ (wealths accounts).sum) := by
    sorry

  /-- Whenever maximum_wealth(accounts) returns a result r, r <= 100 * max_{0 <= i < len(accounts)} len(accounts[i]).
    Preconditions: 1 <= len(accounts) <= 50; for every i with 0 <= i < len(accounts), 1 <= len(accounts[i]) <= 50; for every i and j with 0 <= i < len(accounts) and 0 <= j < len(accounts[i]), 1 <= accounts[i][j] <= 100. -/
  theorem spec_5 (accounts : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (r : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r) :
      r.val ≤ 100 * ((natMax (rowLengths accounts) : Nat) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (accounts : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (r : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r), r.val ≤ 100 * ((natMax (rowLengths accounts) : Nat) : Int)) := by
    sorry

  /-- Whenever maximum_wealth(accounts) returns a result r, r > 0.
    Preconditions: 1 <= len(accounts) <= 50; for every i with 0 <= i < len(accounts), 1 <= len(accounts[i]) <= 50; for every i and j with 0 <= i < len(accounts) and 0 <= j < len(accounts[i]), 1 <= accounts[i][j] <= 100. -/
  theorem spec_6 (accounts : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (r : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r) :
      0 < r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (accounts : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (r : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r), 0 < r.val) := by
    sorry

  /-- Let wealth(i) = sum_{j=0}^{len(accounts[i])-1} accounts[i][j] for 0 <= i < len(accounts). Whenever maximum_wealth(accounts) returns a result r, there exists an index i with 0 <= i < len(accounts) such that r = wealth(i).
    Preconditions: 1 <= len(accounts) <= 50; for every i with 0 <= i < len(accounts), 1 <= len(accounts[i]) <= 50; for every i and j with 0 <= i < len(accounts) and 0 <= j < len(accounts[i]), 1 <= accounts[i][j] <= 100. -/
  theorem spec_7 (accounts : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (r : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r) :
      ∃ row ∈ accounts.val, r.val = rowWealth row := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (accounts : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (r : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r), ∃ row ∈ accounts.val, r.val = rowWealth row) := by
    sorry

  /-- If accounts' is a permutation of the rows of accounts, meaning there is a bijection p from {0, ..., len(accounts')-1} to {0, ..., len(accounts)-1} such that accounts'[i] = accounts[p(i)] for every i with 0 <= i < len(accounts'), and maximum_wealth(accounts) returns r and maximum_wealth(accounts') returns r', then r = r'.
    Preconditions: For every pair of account lists accounts and accounts' such that 1 <= len(accounts) <= 50, 1 <= len(accounts') <= 50, every row of either list has length between 1 and 50, and every entry of either list is between 1 and 100. -/
  theorem spec_8 (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
      (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (h_perm : IsRowPermutation accounts accounts')
      (r r' : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
      (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r') :
      r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
        (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (h_perm : IsRowPermutation accounts accounts')
        (r r' : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
        (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r'), r = r') := by
    sorry

  /-- If accounts[i][j] <= accounts'[i][j] for every i with 0 <= i < len(accounts) and every j with 0 <= j < len(accounts[i]), and maximum_wealth(accounts) returns r and maximum_wealth(accounts') returns r', then r <= r'.
    Preconditions: For every pair of account lists accounts and accounts' such that 1 <= len(accounts) = len(accounts') <= 50, for every i with 0 <= i < len(accounts), len(accounts[i]) = len(accounts'[i]) and 1 <= len(accounts[i]) <= 50, and every entry of either list is between 1 and 100. -/
  theorem spec_9 (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
      (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (h_le : RowsPointwiseLe accounts accounts')
      (r r' : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
      (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
        (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (h_le : RowsPointwiseLe accounts accounts')
        (r r' : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
        (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r'), r.val ≤ r'.val) := by
    sorry

  /-- If accounts' is obtained from accounts by appending one additional row that equals some existing row of accounts, meaning len(accounts') = len(accounts) + 1 and there exists k with 0 <= k < len(accounts) such that accounts'[len(accounts)] = accounts[k] and accounts'[i] = accounts[i] for every i with 0 <= i < len(accounts), and maximum_wealth(accounts) returns r and maximum_wealth(accounts') returns r', then r = r'.
    Preconditions: For every pair of account lists accounts and accounts' such that 1 <= len(accounts) <= 50, 1 <= len(accounts') <= 50, every row of either list has length between 1 and 50, and every entry of either list is between 1 and 100. -/
  theorem spec_10 (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
      (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (k : Nat) (hk : k < accounts.val.length)
      (h_app : accounts'.val = accounts.val ++ [accounts.val[k]'hk])
      (r r' : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
      (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r') :
      r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
        (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (k : Nat) (hk : k < accounts.val.length)
        (h_app : accounts'.val = accounts.val ++ [accounts.val[k]'hk])
        (r r' : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
        (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r'), r = r') := by
    sorry

  /-- Let wealth(i) = sum_{j=0}^{len(accounts[i])-1} accounts[i][j] and wealth'(i) = sum_{j=0}^{len(accounts'[i])-1} accounts'[i][j]. If wealth(i) = wealth'(i) for every i with 0 <= i < len(accounts), and maximum_wealth(accounts) returns r and maximum_wealth(accounts') returns r', then r = r'.
    Preconditions: For every pair of account lists accounts and accounts' such that 1 <= len(accounts) = len(accounts') <= 50, every row of either list has length between 1 and 50, every entry of either list is between 1 and 100, and for every i with 0 <= i < len(accounts), sum_{j=0}^{len(accounts[i])-1} accounts[i][j] = sum_{j=0}^{len(accounts'[i])-1} accounts'[i][j]. -/
  theorem spec_11 (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
      (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (h_same : RowsSameWealth accounts accounts')
      (r r' : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
      (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r') :
      r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 50)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
        (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (h_same : RowsSameWealth accounts accounts')
        (r r' : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
        (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r'), r = r') := by
    sorry

  /-- If maximum_wealth(accounts) returns r and maximum_wealth(accounts') returns r', then r' >= r.
    Preconditions: For every pair of account lists accounts and accounts' such that accounts' is obtained from accounts by appending one extra row: 1 <= len(accounts) <= 49, len(accounts') = len(accounts) + 1, accounts'[i] = accounts[i] for every i with 0 <= i < len(accounts), every row of either list has length between 1 and 50, and every entry of either list is between 1 and 100. -/
  theorem spec_12 (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 49)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
      (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (w : alloc.vec.Vec Std.I64)
      (h_app : AppendsRow accounts accounts' w)
      (r r' : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
      (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 49)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
        (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (w : alloc.vec.Vec Std.I64)
        (h_app : AppendsRow accounts accounts' w)
        (r r' : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
        (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r'), r.val ≤ r'.val) := by
    sorry

  /-- If maximum_wealth(accounts) returns r and maximum_wealth(accounts') returns r', then r = r'.
    Preconditions: For every pair of account lists accounts and accounts' such that accounts' is obtained from accounts by appending one extra row w = accounts'[len(accounts)]: 1 <= len(accounts) <= 49, len(accounts') = len(accounts) + 1, accounts'[i] = accounts[i] for every i with 0 <= i < len(accounts), every row of either list has length between 1 and 50, every entry of either list is between 1 and 100, and sum_{j=0}^{len(w)-1} w[j] <= max_{0 <= i < len(accounts)} sum_{j=0}^{len(accounts[i])-1} accounts[i][j]. -/
  theorem spec_13 (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
      (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 49)
      (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
      (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
      (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
      (w : alloc.vec.Vec Std.I64)
      (h_app : AppendsRow accounts accounts' w)
      (h_bound : rowWealth w ≤ intMax (wealths accounts))
      (r r' : Std.I64)
      (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
      (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r') :
      r = r' := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (accounts accounts' : Slice (alloc.vec.Vec Std.I64))
        (h_len_lb : 1 ≤ accounts.val.length) (h_len_ub : accounts.val.length ≤ 49)
        (h_rows : ∀ row ∈ accounts.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries : ∀ row ∈ accounts.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (h_len_lb' : 1 ≤ accounts'.val.length) (h_len_ub' : accounts'.val.length ≤ 50)
        (h_rows' : ∀ row ∈ accounts'.val, 1 ≤ row.val.length ∧ row.val.length ≤ 50)
        (h_entries' : ∀ row ∈ accounts'.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 100)
        (w : alloc.vec.Vec Std.I64)
        (h_app : AppendsRow accounts accounts' w)
        (h_bound : rowWealth w ≤ intMax (wealths accounts))
        (r r' : Std.I64)
        (hres : Aegis.MaximumWealth.maximum_wealth accounts = Result.ok r)
        (hres' : Aegis.MaximumWealth.maximum_wealth accounts' = Result.ok r'), r = r') := by
    sorry

  end AegisSpec.MaximumWealth
