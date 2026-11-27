import Aegis.MaximumAmount.Code.Funs

/-!
# Specifications of `Aegis.MaximumAmount.maximum_amount`

LeetCode problem `maximum-amount-of-money-robot-can-earn`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumAmount (maximum_amount)

namespace AegisSpec.MaximumAmount

def nrows (coins : Slice (alloc.vec.Vec I64)) : ℕ := coins.val.length

def ncols (coins : Slice (alloc.vec.Vec I64)) : ℕ :=
  match coins.val with
  | [] => 0
  | row :: _ => row.val.length

def pathLen (coins : Slice (alloc.vec.Vec I64)) : ℕ := nrows coins + ncols coins - 1

def entry (coins : Slice (alloc.vec.Vec I64)) (i j : ℕ) : ℤ :=
  match coins.val[i]? with
  | none => 0
  | some row =>
    match row.val[j]? with
    | none => 0
    | some x => x.val

def ValidGrid (coins : Slice (alloc.vec.Vec I64)) : Prop :=
  1 ≤ nrows coins ∧ nrows coins ≤ 500 ∧
  1 ≤ ncols coins ∧ ncols coins ≤ 500 ∧
  (∀ row ∈ coins.val, row.val.length = ncols coins) ∧
  (∀ row ∈ coins.val, ∀ x ∈ row.val, -1000 ≤ x.val ∧ x.val ≤ 1000)

def IsPath (coins : Slice (alloc.vec.Vec I64)) (P : List (ℕ × ℕ)) : Prop :=
  P.head? = some (0, 0) ∧
  P.getLast? = some (nrows coins - 1, ncols coins - 1) ∧
  (∀ p ∈ P, p.1 < nrows coins ∧ p.2 < ncols coins) ∧
  (∀ (k : ℕ) (p q : ℕ × ℕ), P[k]? = some p → P[k + 1]? = some q →
    q = (p.1, p.2 + 1) ∨ q = (p.1 + 1, p.2))

def pathVals (coins : Slice (alloc.vec.Vec I64)) (P : List (ℕ × ℕ)) : List ℤ :=
  P.map (fun p => entry coins p.1 p.2)

def ValidT (coins : Slice (alloc.vec.Vec I64)) (P : List (ℕ × ℕ)) (T : Finset ℕ) : Prop :=
  T.card ≤ 2 ∧
  (∀ k ∈ T, k < P.length) ∧
  (∀ k ∈ T, ∃ p, P[k]? = some p ∧ entry coins p.1 p.2 < 0)

def sumZeros (vals : List ℤ) (T : Finset ℕ) : ℤ :=
  ((List.range vals.length).map (fun k => if k ∈ T then 0 else (vals[k]?).getD 0)).sum

def score (coins : Slice (alloc.vec.Vec I64)) (P : List (ℕ × ℕ)) (T : Finset ℕ) : ℤ :=
  sumZeros (pathVals coins P) T

def IsOptimal (coins : Slice (alloc.vec.Vec I64)) (r : ℤ) : Prop :=
  (∀ (P : List (ℕ × ℕ)) (T : Finset ℕ), IsPath coins P → ValidT coins P T →
      score coins P T ≤ r) ∧
    (∃ (P : List (ℕ × ℕ)) (T : Finset ℕ), IsPath coins P ∧ ValidT coins P T ∧
      score coins P T = r)

def IsOptimalPathSum (coins : Slice (alloc.vec.Vec I64)) (r : ℤ) : Prop :=
  (∀ P : List (ℕ × ℕ), IsPath coins P → (pathVals coins P).sum ≤ r) ∧
    (∃ P : List (ℕ × ℕ), IsPath coins P ∧ (pathVals coins P).sum = r)

def linePath (coins : Slice (alloc.vec.Vec I64)) : List (ℕ × ℕ) :=
  if nrows coins = 1 then (List.range (ncols coins)).map (fun j => (0, j))
  else (List.range (nrows coins)).map (fun i => (i, 0))

def negSum (l : List ℤ) : ℤ :=
  ((l.filter (fun x => x < 0)).insertionSort (fun a b => a ≤ b)).take 2 |>.sum

def IsTranspose (coins coinsT : Slice (alloc.vec.Vec I64)) : Prop :=
  nrows coinsT = ncols coins ∧ ncols coinsT = nrows coins ∧
  (∀ i j, i < nrows coins → j < ncols coins → entry coinsT j i = entry coins i j)

/-- The function returns a result r, and r is the maximum, over all monotone paths P = (p_0,...,p_{m+n-2}) from (0,0) to (m-1,n-1) (each step moves one cell right or one cell down) and over all sets T of indices in {0,...,m+n-2} with |T| <= 2 and coins[p_k.row][p_k.col] < 0 for every k in T, of score(P,T) = sum_{k=0}^{m+n-2} (0 if k is in T else coins[p_k.row][p_k.col]).
  Preconditions: Let m = len(coins) and n = len(coins[0]). The input is a valid grid: 1 <= m <= 500, 1 <= n <= 500, len(coins[i]) = n for every 0 <= i < m, and -1000 <= coins[i][j] <= 1000 for every 0 <= i < m, 0 <= j < n. -/
theorem spec_1 (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins) :
    ∃ r : I64, maximum_amount coins = ok r ∧ IsOptimal coins r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins), ∃ r : I64, maximum_amount coins = ok r ∧ IsOptimal coins r.val) := by
  sorry

/-- For every valid input, the function returns a result r; it does not fail (no overflow, out-of-bounds, or panic).
  Preconditions: Let m = len(coins) and n = len(coins[0]). The input is a valid grid: 1 <= m <= 500, 1 <= n <= 500, len(coins[i]) = n for every 0 <= i < m, and -1000 <= coins[i][j] <= 1000 for every 0 <= i < m, 0 <= j < n. -/
theorem spec_2 (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins) :
    ∃ r : I64, maximum_amount coins = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins), ∃ r : I64, maximum_amount coins = ok r) := by
  sorry

/-- Let L = m + n - 1. The function returns a result r and -1000 * L <= r <= 1000 * L.
  Preconditions: Let m = len(coins) and n = len(coins[0]). The input is a valid grid: 1 <= m <= 500, 1 <= n <= 500, len(coins[i]) = n for every 0 <= i < m, and -1000 <= coins[i][j] <= 1000 for every 0 <= i < m, 0 <= j < n. -/
theorem spec_3 (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins) :
    ∃ r : I64, maximum_amount coins = ok r ∧
      -1000 * (pathLen coins : ℤ) ≤ r.val ∧
      r.val ≤ 1000 * (pathLen coins : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins), ∃ r : I64, maximum_amount coins = ok r ∧
      -1000 * (pathLen coins : ℤ) ≤ r.val ∧
      r.val ≤ 1000 * (pathLen coins : ℤ)) := by
  sorry

/-- The function returns a result r and r <= sum_{i=0}^{m-1} sum_{j=0}^{n-1} max(coins[i][j], 0).
  Preconditions: Let m = len(coins) and n = len(coins[0]). The input is a valid grid: 1 <= m <= 500, 1 <= n <= 500, len(coins[i]) = n for every 0 <= i < m, and -1000 <= coins[i][j] <= 1000 for every 0 <= i < m, 0 <= j < n. -/
theorem spec_4 (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins) :
    ∃ r : I64, maximum_amount coins = ok r ∧
      r.val ≤ ∑ i ∈ Finset.range (nrows coins), ∑ j ∈ Finset.range (ncols coins),
        max (entry coins i j) 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins), ∃ r : I64, maximum_amount coins = ok r ∧
      r.val ≤ ∑ i ∈ Finset.range (nrows coins), ∑ j ∈ Finset.range (ncols coins),
        max (entry coins i j) 0) := by
  sorry

/-- The function returns a result r, and for every monotone path P = (p_0,...,p_{m+n-2}) from (0,0) to (m-1,n-1) and every set T of indices in {0,...,m+n-2} with |T| <= 2 and coins[p_k.row][p_k.col] < 0 for every k in T, score(P,T) <= r, where score(P,T) = sum_{k=0}^{m+n-2} (0 if k is in T else coins[p_k.row][p_k.col]).
  Preconditions: Let m = len(coins) and n = len(coins[0]). The input is a valid grid: 1 <= m <= 500, 1 <= n <= 500, len(coins[i]) = n for every 0 <= i < m, and -1000 <= coins[i][j] <= 1000 for every 0 <= i < m, 0 <= j < n. -/
theorem spec_5 (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins) :
    ∃ r : I64, maximum_amount coins = ok r ∧
      ∀ (P : List (ℕ × ℕ)) (T : Finset ℕ), IsPath coins P → ValidT coins P T →
        score coins P T ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins), ∃ r : I64, maximum_amount coins = ok r ∧
      ∀ (P : List (ℕ × ℕ)) (T : Finset ℕ), IsPath coins P → ValidT coins P T →
        score coins P T ≤ r.val) := by
  sorry

/-- The function returns a result r, and there exist a monotone path P = (p_0,...,p_{m+n-2}) from (0,0) to (m-1,n-1) and a set T of indices in {0,...,m+n-2} with |T| <= 2 and coins[p_k.row][p_k.col] < 0 for every k in T such that score(P,T) = r, where score(P,T) = sum_{k=0}^{m+n-2} (0 if k is in T else coins[p_k.row][p_k.col]).
  Preconditions: Let m = len(coins) and n = len(coins[0]). The input is a valid grid: 1 <= m <= 500, 1 <= n <= 500, len(coins[i]) = n for every 0 <= i < m, and -1000 <= coins[i][j] <= 1000 for every 0 <= i < m, 0 <= j < n. -/
theorem spec_6 (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins) :
    ∃ r : I64, maximum_amount coins = ok r ∧
      ∃ (P : List (ℕ × ℕ)) (T : Finset ℕ), IsPath coins P ∧ ValidT coins P T ∧
        score coins P T = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins), ∃ r : I64, maximum_amount coins = ok r ∧
      ∃ (P : List (ℕ × ℕ)) (T : Finset ℕ), IsPath coins P ∧ ValidT coins P T ∧
        score coins P T = r.val) := by
  sorry

/-- Let c_0,...,c_{m+n-2} be the coin values along the unique monotone path from (0,0) to (m-1,n-1), in order. The function returns a result r and r = (sum_{k=0}^{m+n-2} c_k) - S, where S is the sum of the min(2,q) smallest values, counting multiplicity, among the q values c_k with c_k < 0; if q = 0 then S = 0.
  Preconditions: Let m = len(coins) and n = len(coins[0]). The input is a valid grid: 1 <= m <= 500, 1 <= n <= 500, len(coins[i]) = n for every 0 <= i < m, and -1000 <= coins[i][j] <= 1000 for every 0 <= i < m, 0 <= j < n. Additionally, m = 1 or n = 1. -/
theorem spec_7 (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins)
    (hline : nrows coins = 1 ∨ ncols coins = 1) :
    ∃ r : I64, maximum_amount coins = ok r ∧
      r.val = (pathVals coins (linePath coins)).sum - negSum (pathVals coins (linePath coins)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins)
    (hline : nrows coins = 1 ∨ ncols coins = 1), ∃ r : I64, maximum_amount coins = ok r ∧
      r.val = (pathVals coins (linePath coins)).sum - negSum (pathVals coins (linePath coins))) := by
  sorry

/-- The function returns a result r and r = max { sum_{k=0}^{m+n-2} coins[p_k.row][p_k.col] : P=(p_0,...,p_{m+n-2}) is a monotone path from (0,0) to (m-1,n-1) }.
  Preconditions: Let m = len(coins) and n = len(coins[0]). The input is a valid grid: 1 <= m <= 500, 1 <= n <= 500, len(coins[i]) = n for every 0 <= i < m, and -1000 <= coins[i][j] <= 1000 for every 0 <= i < m, 0 <= j < n. Additionally, coins[i][j] >= 0 for every 0 <= i < m, 0 <= j < n. -/
theorem spec_8 (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins)
    (hnn : ∀ i j, i < nrows coins → j < ncols coins → 0 ≤ entry coins i j) :
    ∃ r : I64, maximum_amount coins = ok r ∧ IsOptimalPathSum coins r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins)
    (hnn : ∀ i j, i < nrows coins → j < ncols coins → 0 ≤ entry coins i j), ∃ r : I64, maximum_amount coins = ok r ∧ IsOptimalPathSum coins r.val) := by
  sorry

/-- The function returns a result r and -1000 * (L - 2) <= r <= -(L - 2), where L = m + n - 1.
  Preconditions: Let m = len(coins) and n = len(coins[0]). The input is a valid grid: 1 <= m <= 500, 1 <= n <= 500, len(coins[i]) = n for every 0 <= i < m, and -1000 <= coins[i][j] <= 1000 for every 0 <= i < m, 0 <= j < n. Additionally, coins[i][j] < 0 for every 0 <= i < m, 0 <= j < n, and L = m + n - 1 >= 3. -/
theorem spec_9 (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins)
    (hneg : ∀ i j, i < nrows coins → j < ncols coins → entry coins i j < 0)
    (hL : 3 ≤ pathLen coins) :
    ∃ r : I64, maximum_amount coins = ok r ∧
      -1000 * ((pathLen coins - 2 : ℕ) : ℤ) ≤ r.val ∧
      r.val ≤ -((pathLen coins - 2 : ℕ) : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (coins : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid coins)
    (hneg : ∀ i j, i < nrows coins → j < ncols coins → entry coins i j < 0)
    (hL : 3 ≤ pathLen coins), ∃ r : I64, maximum_amount coins = ok r ∧
      -1000 * ((pathLen coins - 2 : ℕ) : ℤ) ≤ r.val ∧
      r.val ≤ -((pathLen coins - 2 : ℕ) : ℤ)) := by
  sorry

/-- If the function returns r for coins and returns r2 for coins2, then r <= r2.
  Preconditions: Let m = len(coins), n = len(coins[0]), m2 = len(coins2), and n2 = len(coins2[0]). Both coins and coins2 are valid grids: 1 <= m,m2 <= 500, 1 <= n,n2 <= 500, all rows have the stated lengths, and all entries are in [-1000,1000]. Moreover m = m2, n = n2, and coins[i][j] <= coins2[i][j] for every 0 <= i < m, 0 <= j < n. -/
theorem spec_10 (coins coins2 : Slice (alloc.vec.Vec I64))
    (hgrid : ValidGrid coins) (hgrid2 : ValidGrid coins2)
    (hm : nrows coins = nrows coins2) (hn : ncols coins = ncols coins2)
    (hle : ∀ i j, i < nrows coins → j < ncols coins → entry coins i j ≤ entry coins2 i j)
    (r r2 : I64) (hr : maximum_amount coins = ok r) (hr2 : maximum_amount coins2 = ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (coins coins2 : Slice (alloc.vec.Vec I64))
    (hgrid : ValidGrid coins) (hgrid2 : ValidGrid coins2)
    (hm : nrows coins = nrows coins2) (hn : ncols coins = ncols coins2)
    (hle : ∀ i j, i < nrows coins → j < ncols coins → entry coins i j ≤ entry coins2 i j)
    (r r2 : I64) (hr : maximum_amount coins = ok r) (hr2 : maximum_amount coins2 = ok r2), r.val ≤ r2.val) := by
  sorry

/-- If the function returns r for coins and returns rT for coinsT, then r = rT.
  Preconditions: Let m = len(coins) and n = len(coins[0]). The input is a valid grid: 1 <= m <= 500, 1 <= n <= 500, len(coins[i]) = n for every 0 <= i < m, and -1000 <= coins[i][j] <= 1000 for every 0 <= i < m, 0 <= j < n. Let coinsT be the n x m grid defined by coinsT[j][i] = coins[i][j] for every 0 <= i < m, 0 <= j < n. -/
theorem spec_11 (coins coinsT : Slice (alloc.vec.Vec I64))
    (hgrid : ValidGrid coins) (hT : IsTranspose coins coinsT)
    (r rT : I64) (hr : maximum_amount coins = ok r) (hrT : maximum_amount coinsT = ok rT) :
    r.val = rT.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (coins coinsT : Slice (alloc.vec.Vec I64))
    (hgrid : ValidGrid coins) (hT : IsTranspose coins coinsT)
    (r rT : I64) (hr : maximum_amount coins = ok r) (hrT : maximum_amount coinsT = ok rT), r.val = rT.val) := by
  sorry

end AegisSpec.MaximumAmount
