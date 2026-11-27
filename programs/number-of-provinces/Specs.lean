import Aegis.FindCircleNum.Code.Funs

/-!
# Specifications of `Aegis.FindCircleNum.find_circle_num`

LeetCode problem `number-of-provinces`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.FindCircleNum

namespace AegisSpec.FindCircleNum

def row (isConnected : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  ((isConnected.val[i]?).map (fun v => v.val)).getD []

def entry (isConnected : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Option Int :=
  (row isConnected i)[j]?

def Edge (isConnected : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
  entry isConnected i j = some 1

def Reachable (isConnected : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
  Relation.ReflTransGen (Edge isConnected) i j

def IsProvince (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (S : Set Nat) : Prop :=
  S.Nonempty ∧
  (∀ i, i ∈ S → i < n) ∧
  (∀ i, i ∈ S → ∀ j, j ∈ S → Reachable isConnected i j) ∧
  (∀ i, i ∈ S → ∀ j, j < n → j ∉ S → ¬ Reachable isConnected i j ∧ ¬ Reachable isConnected j i)

noncomputable def provinceCount (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Nat :=
  Nat.card {S : Set Nat // IsProvince isConnected n S}

def IsProvinceFirst (isConnected : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Prop :=
  ∀ j, j < i → ¬ Reachable isConnected j i

noncomputable def provinceFirstCount (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Nat :=
  Nat.card {i : Nat // i < n ∧ IsProvinceFirst isConnected i}

def IsProvincePartition (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (P : Finset (Set Nat)) : Prop :=
  (∀ S, S ∈ P → IsProvince isConnected n S) ∧
  (∀ S, S ∈ P → ∀ T, T ∈ P → S ≠ T → Disjoint S T) ∧
  (∀ i, i < n → ∃ S, S ∈ P ∧ i ∈ S)

/-- The function returns a result r (it does not fail), and r equals the number of provinces of the graph on the city indices {0,...,n-1}, defined as follows. For indices i and j, say j is reachable from i if there is an integer m >= 0 and a sequence v_0, v_1, ..., v_m of indices in {0,...,n-1} with v_0 = i, v_m = j, and isConnected[v_t][v_{t+1}] = 1 for every t with 0 <= t < m. A province is a nonempty subset S of {0,...,n-1} such that (a) for every i,j in S, j is reachable from i, and (b) for every i in S and every j not in S, j is not reachable from i and i is not reachable from j. Then r is the number of distinct provinces.
  Preconditions: Let n = len(isConnected). The input is valid: 1 <= n <= 200; for every i with 0 <= i < n, len(isConnected[i]) = n; for every i,j with 0 <= i,j < n, isConnected[i][j] is either 0 or 1; for every i with 0 <= i < n, isConnected[i][i] = 1; and for every i,j with 0 <= i,j < n, isConnected[i][j] = isConnected[j][i]. -/
theorem spec_1 (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i) :
    ∃ r : Std.I64, find_circle_num isConnected = ok r ∧ r.val = (provinceCount isConnected n : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i), ∃ r : Std.I64, find_circle_num isConnected = ok r ∧ r.val = (provinceCount isConnected n : Int)) := by
  sorry

/-- For every valid input isConnected, the call find_circle_num(isConnected) returns a result r; it does not panic, does not access an index outside the slice or outside a row, and does not perform an arithmetic operation whose result leaves the signed 64-bit range.
  Preconditions: Let n = len(isConnected). The input is valid: 1 <= n <= 200; for every i with 0 <= i < n, len(isConnected[i]) = n; for every i,j with 0 <= i,j < n, isConnected[i][j] is either 0 or 1; for every i with 0 <= i < n, isConnected[i][i] = 1; and for every i,j with 0 <= i,j < n, isConnected[i][j] = isConnected[j][i]. -/
theorem spec_2 (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i) :
    ∃ r : Std.I64, find_circle_num isConnected = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i), ∃ r : Std.I64, find_circle_num isConnected = ok r) := by
  sorry

/-- Whenever the function returns a result r on a valid input, the integer r satisfies 1 <= r <= n.
  Preconditions: Let n = len(isConnected). The input is valid: 1 <= n <= 200; for every i with 0 <= i < n, len(isConnected[i]) = n; for every i,j with 0 <= i,j < n, isConnected[i][j] is either 0 or 1; for every i with 0 <= i < n, isConnected[i][i] = 1; and for every i,j with 0 <= i,j < n, isConnected[i][j] = isConnected[j][i]. -/
theorem spec_3 (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r) :
    1 ≤ r.val ∧ r.val ≤ (n : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r), 1 ≤ r.val ∧ r.val ≤ (n : Int)) := by
  sorry

/-- The function returns n.
  Preconditions: Let n = len(isConnected). The input is valid: 1 <= n <= 200; for every i with 0 <= i < n, len(isConnected[i]) = n; for every i,j with 0 <= i,j < n, isConnected[i][j] is either 0 or 1; for every i with 0 <= i < n, isConnected[i][i] = 1; and for every i,j with 0 <= i,j < n, isConnected[i][j] = isConnected[j][i]. Also, for every i,j with 0 <= i,j < n and i != j, isConnected[i][j] = 0. -/
theorem spec_4 (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (hzero : ∀ i j, i < n → j < n → i ≠ j → entry isConnected i j = some 0) :
    ∃ r : Std.I64, find_circle_num isConnected = ok r ∧ r.val = (n : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (hzero : ∀ i j, i < n → j < n → i ≠ j → entry isConnected i j = some 0), ∃ r : Std.I64, find_circle_num isConnected = ok r ∧ r.val = (n : Int)) := by
  sorry

/-- The function returns 1.
  Preconditions: Let n = len(isConnected). The input is valid: 1 <= n <= 200; for every i with 0 <= i < n, len(isConnected[i]) = n; for every i,j with 0 <= i,j < n, isConnected[i][j] is either 0 or 1; for every i with 0 <= i < n, isConnected[i][i] = 1; and for every i,j with 0 <= i,j < n, isConnected[i][j] = isConnected[j][i]. Also, for every i,j with 0 <= i,j < n, isConnected[i][j] = 1. -/
theorem spec_5 (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (hone : ∀ i j, i < n → j < n → entry isConnected i j = some 1) :
    ∃ r : Std.I64, find_circle_num isConnected = ok r ∧ r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (hone : ∀ i j, i < n → j < n → entry isConnected i j = some 1), ∃ r : Std.I64, find_circle_num isConnected = ok r ∧ r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, we have r = 1 if and only if for every pair of indices i,j in {0,...,n-1}, j is reachable from i, where j is reachable from i if there is an integer m >= 0 and a sequence v_0, v_1, ..., v_m of indices in {0,...,n-1} with v_0 = i, v_m = j, and isConnected[v_t][v_{t+1}] = 1 for every t with 0 <= t < m. Equivalently, r = 1 exactly when all n cities lie in a single province.
  Preconditions: Let n = len(isConnected). The input is valid: 1 <= n <= 200; for every i with 0 <= i < n, len(isConnected[i]) = n; for every i,j with 0 <= i,j < n, isConnected[i][j] is either 0 or 1; for every i with 0 <= i < n, isConnected[i][i] = 1; and for every i,j with 0 <= i,j < n, isConnected[i][j] = isConnected[j][i]. -/
theorem spec_6 (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r) :
    (r.val = 1 ↔ ∀ i j, i < n → j < n → Reachable isConnected i j) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r), (r.val = 1 ↔ ∀ i j, i < n → j < n → Reachable isConnected i j)) := by
  sorry

/-- Whenever the function returns a result r and r >= 2, there exist two distinct indices i,j in {0,...,n-1} such that j is not reachable from i, where j is reachable from i if there is an integer m >= 0 and a sequence v_0, v_1, ..., v_m of indices in {0,...,n-1} with v_0 = i, v_m = j, and isConnected[v_t][v_{t+1}] = 1 for every t with 0 <= t < m. Equivalently, at least two different provinces occur.
  Preconditions: Let n = len(isConnected). The input is valid: 1 <= n <= 200; for every i with 0 <= i < n, len(isConnected[i]) = n; for every i,j with 0 <= i,j < n, isConnected[i][j] is either 0 or 1; for every i with 0 <= i < n, isConnected[i][i] = 1; and for every i,j with 0 <= i,j < n, isConnected[i][j] = isConnected[j][i]. -/
theorem spec_7 (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r) (hr2 : 2 ≤ r.val) :
    ∃ i j, i < n ∧ j < n ∧ i ≠ j ∧ ¬ Reachable isConnected i j := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r) (hr2 : 2 ≤ r.val), ∃ i j, i < n ∧ j < n ∧ i ≠ j ∧ ¬ Reachable isConnected i j) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of indices i with 0 <= i < n for which there is no index j with 0 <= j < i such that i is reachable from j, where i is reachable from j if there is an integer m >= 0 and a sequence v_0, v_1, ..., v_m of indices in {0,...,n-1} with v_0 = j, v_m = i, and isConnected[v_t][v_{t+1}] = 1 for every t with 0 <= t < m.
  Preconditions: Let n = len(isConnected). The input is valid: 1 <= n <= 200; for every i with 0 <= i < n, len(isConnected[i]) = n; for every i,j with 0 <= i,j < n, isConnected[i][j] is either 0 or 1; for every i with 0 <= i < n, isConnected[i][i] = 1; and for every i,j with 0 <= i,j < n, isConnected[i][j] = isConnected[j][i]. -/
theorem spec_8 (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r) :
    r.val = (provinceFirstCount isConnected n : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r), r.val = (provinceFirstCount isConnected n : Int)) := by
  sorry

/-- Whenever find_circle_num(A) returns rA and find_circle_num(B) returns rB, we have rB <= rA.
  Preconditions: Let n be an integer with 1 <= n <= 200. Let A and B be two n x n input matrices satisfying the problem constraints: every row has length n; every entry is 0 or 1; A[i][i] = B[i][i] = 1 for all i with 0 <= i < n; and A and B are symmetric. Additionally, for every i,j with 0 <= i,j < n, if A[i][j] = 1 then B[i][j] = 1. -/
theorem spec_9 (A B : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hAn : A.val.length = n) (hBn : B.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hArow : ∀ i, i < n → (row A i).length = n)
    (hBrow : ∀ i, i < n → (row B i).length = n)
    (hAbin : ∀ i j, i < n → j < n → entry A i j = some 0 ∨ entry A i j = some 1)
    (hBbin : ∀ i j, i < n → j < n → entry B i j = some 0 ∨ entry B i j = some 1)
    (hAdiag : ∀ i, i < n → entry A i i = some 1)
    (hBdiag : ∀ i, i < n → entry B i i = some 1)
    (hAsymm : ∀ i j, i < n → j < n → entry A i j = entry A j i)
    (hBsymm : ∀ i j, i < n → j < n → entry B i j = entry B j i)
    (hmono : ∀ i j, i < n → j < n → entry A i j = some 1 → entry B i j = some 1)
    (rA rB : Std.I64)
    (hrA : find_circle_num A = ok rA) (hrB : find_circle_num B = ok rB) :
    rB.val ≤ rA.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hAn : A.val.length = n) (hBn : B.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hArow : ∀ i, i < n → (row A i).length = n)
    (hBrow : ∀ i, i < n → (row B i).length = n)
    (hAbin : ∀ i j, i < n → j < n → entry A i j = some 0 ∨ entry A i j = some 1)
    (hBbin : ∀ i j, i < n → j < n → entry B i j = some 0 ∨ entry B i j = some 1)
    (hAdiag : ∀ i, i < n → entry A i i = some 1)
    (hBdiag : ∀ i, i < n → entry B i i = some 1)
    (hAsymm : ∀ i j, i < n → j < n → entry A i j = entry A j i)
    (hBsymm : ∀ i j, i < n → j < n → entry B i j = entry B j i)
    (hmono : ∀ i j, i < n → j < n → entry A i j = some 1 → entry B i j = some 1)
    (rA rB : Std.I64)
    (hrA : find_circle_num A = ok rA) (hrB : find_circle_num B = ok rB), rB.val ≤ rA.val) := by
  sorry

/-- Whenever find_circle_num(A) returns rA and find_circle_num(B) returns rB, we have rA = rB.
  Preconditions: Let A be a valid n x n input matrix satisfying the problem constraints: 1 <= n <= 200; every row has length n; every entry is 0 or 1; A[i][i] = 1 for all i with 0 <= i < n; and A is symmetric. Let pi be a permutation of {0,...,n-1}. Let B be the n x n matrix defined by B[i][j] = A[pi(i)][pi(j)] for all i,j with 0 <= i,j < n. -/
theorem spec_10 (A B : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (π : Nat → Nat)
    (hAn : A.val.length = n) (hBn : B.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hArow : ∀ i, i < n → (row A i).length = n)
    (hBrow : ∀ i, i < n → (row B i).length = n)
    (hAbin : ∀ i j, i < n → j < n → entry A i j = some 0 ∨ entry A i j = some 1)
    (hBbin : ∀ i j, i < n → j < n → entry B i j = some 0 ∨ entry B i j = some 1)
    (hAdiag : ∀ i, i < n → entry A i i = some 1)
    (hBdiag : ∀ i, i < n → entry B i i = some 1)
    (hAsymm : ∀ i j, i < n → j < n → entry A i j = entry A j i)
    (hBsymm : ∀ i j, i < n → j < n → entry B i j = entry B j i)
    (hπ_lt : ∀ i, i < n → π i < n)
    (hπ_inj : ∀ i j, i < n → j < n → π i = π j → i = j)
    (hπ_surj : ∀ j, j < n → ∃ i, i < n ∧ π i = j)
    (hB : ∀ i j, i < n → j < n → entry B i j = entry A (π i) (π j))
    (rA rB : Std.I64)
    (hrA : find_circle_num A = ok rA) (hrB : find_circle_num B = ok rB) :
    rA.val = rB.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (π : Nat → Nat)
    (hAn : A.val.length = n) (hBn : B.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hArow : ∀ i, i < n → (row A i).length = n)
    (hBrow : ∀ i, i < n → (row B i).length = n)
    (hAbin : ∀ i j, i < n → j < n → entry A i j = some 0 ∨ entry A i j = some 1)
    (hBbin : ∀ i j, i < n → j < n → entry B i j = some 0 ∨ entry B i j = some 1)
    (hAdiag : ∀ i, i < n → entry A i i = some 1)
    (hBdiag : ∀ i, i < n → entry B i i = some 1)
    (hAsymm : ∀ i j, i < n → j < n → entry A i j = entry A j i)
    (hBsymm : ∀ i j, i < n → j < n → entry B i j = entry B j i)
    (hπ_lt : ∀ i, i < n → π i < n)
    (hπ_inj : ∀ i j, i < n → j < n → π i = π j → i = j)
    (hπ_surj : ∀ j, j < n → ∃ i, i < n ∧ π i = j)
    (hB : ∀ i j, i < n → j < n → entry B i j = entry A (π i) (π j))
    (rA rB : Std.I64)
    (hrA : find_circle_num A = ok rA) (hrB : find_circle_num B = ok rB), rA.val = rB.val) := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if for every pair of distinct indices i,j in {0,...,n-1}, j is not reachable from i, where j is reachable from i if there is an integer m >= 0 and a sequence v_0, v_1, ..., v_m of indices in {0,...,n-1} with v_0 = i, v_m = j, and isConnected[v_t][v_{t+1}] = 1 for every t with 0 <= t < m.
  Preconditions: Let n = len(isConnected). The input is valid: 1 <= n <= 200; for every i with 0 <= i < n, len(isConnected[i]) = n; for every i,j with 0 <= i,j < n, isConnected[i][j] is either 0 or 1; for every i with 0 <= i < n, isConnected[i][i] = 1; and for every i,j with 0 <= i,j < n, isConnected[i][j] = isConnected[j][i]. -/
theorem spec_11 (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r) :
    (r.val = (n : Int) ↔
      ∀ i j, i < n → j < n → i ≠ j → ¬ Reachable isConnected i j) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r), (r.val = (n : Int) ↔
      ∀ i j, i < n → j < n → i ≠ j → ¬ Reachable isConnected i j)) := by
  sorry

/-- Whenever the function returns a result r, there exist exactly r sets P_1, ..., P_r such that: each P_k is a nonempty subset of {0,...,n-1}; P_k and P_l are disjoint for k != l; the union P_1 ∪ ... ∪ P_r is {0,...,n-1}; and for each k, P_k is a province, meaning every two cities in P_k are mutually reachable via finite sequences of 1-entries and no city in P_k is reachable from a city outside P_k and no city outside P_k is reachable from a city in P_k. Conversely, any such partition into provinces has exactly r sets.
  Preconditions: Let n = len(isConnected). The input is valid: 1 <= n <= 200; for every i with 0 <= i < n, len(isConnected[i]) = n; for every i,j with 0 <= i,j < n, isConnected[i][j] is either 0 or 1; for every i with 0 <= i < n, isConnected[i][i] = 1; and for every i,j with 0 <= i,j < n, isConnected[i][j] = isConnected[j][i]. -/
theorem spec_12 (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r) :
    (∃ P : Finset (Set Nat), IsProvincePartition isConnected n P ∧ (P.card : Int) = r.val) ∧
    (∀ P : Finset (Set Nat), IsProvincePartition isConnected n P → (P.card : Int) = r.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (isConnected : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = isConnected.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 200)
    (hrow : ∀ i, i < n → (row isConnected i).length = n)
    (hbin : ∀ i j, i < n → j < n →
      entry isConnected i j = some 0 ∨ entry isConnected i j = some 1)
    (hdiag : ∀ i, i < n → entry isConnected i i = some 1)
    (hsymm : ∀ i j, i < n → j < n → entry isConnected i j = entry isConnected j i)
    (r : Std.I64) (hr : find_circle_num isConnected = ok r), (∃ P : Finset (Set Nat), IsProvincePartition isConnected n P ∧ (P.card : Int) = r.val) ∧
    (∀ P : Finset (Set Nat), IsProvincePartition isConnected n P → (P.card : Int) = r.val)) := by
  sorry

end AegisSpec.FindCircleNum
