import Aegis.MergeNodes.Code.Funs

/-!
# Specifications of `Aegis.MergeNodes.merge_nodes`

LeetCode problem `merge-nodes-in-between-zeros`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MergeNodes

def values : Aegis.MergeNodes.List → List Int
  | .Nil => []
  | .Cons v tl => v.val :: values tl

def zeroIndices (xs : List Int) : List Nat :=
  (List.range xs.length).filter (fun i => xs[i]? = some 0)

def blockSum (xs : List Int) (a b : Nat) : Int :=
  (((List.range b).drop (a + 1)).map (fun i => xs.getD i 0)).sum

def S (xs : List Int) (zs : List Nat) (j : Nat) : Int :=
  blockSum xs (zs.getD j 0) (zs.getD (j + 1) 0)

def nonzeroRunCount (xs : List Int) : Nat :=
  ((List.range xs.length).filter
    (fun i => xs.getD i 0 ≠ 0 ∧ (i = 0 ∨ xs.getD (i - 1) 0 = 0))).length

structure Pre (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat) : Prop where

  values_eq : xs = values head

  length_ge : 3 ≤ xs.length

  length_le : xs.length ≤ 200000

  nonneg : ∀ x ∈ xs, 0 ≤ x

  le_thousand : ∀ x ∈ xs, x ≤ 1000

  head_zero : xs[0]? = some 0

  last_zero : xs.getLast? = some 0

  no_adjacent_zeros : ∀ i, i + 1 < xs.length → xs[i]? = some 0 → xs[i + 1]? = some 0 → False

  zeros_eq : zs = zeroIndices xs

  zeros_head : zs[0]? = some 0

  zeros_last : zs.getLast? = some (xs.length - 1)

  zeros_length : 2 ≤ zs.length

  zeros_gaps : ∀ j, j < zs.length - 1 → zs.getD j 0 + 2 ≤ zs.getD (j + 1) 0

/-- The function returns a result r. If the value sequence of r is [r_0,...,r_{L-1}], then L=m and r_j=S_j for every j with 0<=j<m. Thus r is exactly the list of sums of the nonempty blocks of input values lying strictly between consecutive zero-valued nodes.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the value sequence of head, so head=Cons(x_0,Cons(x_1,...Cons(x_{n-1},Nil))). Assume 3<=n<=200000, 0<=x_i<=1000 for every 0<=i<n, x_0=0, x_{n-1}=0, and no two adjacent values are both 0. Let z_0<z_1<...<z_m be all indices i with x_i=0; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2 for every 0<=j<m. For 0<=j<m define S_j=sum_{i=z_j+1}^{z_{j+1}-1} x_i. -/
theorem spec_1 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∃ r, Aegis.MergeNodes.merge_nodes head = .ok r ∧
      (values r).length = zs.length - 1 ∧
      ∀ j, j < zs.length - 1 → (values r).getD j 0 = S xs zs j := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∃ r, Aegis.MergeNodes.merge_nodes head = Result.ok r ∧
      (values r).length = zs.length - 1 ∧
      ∀ j, j < zs.length - 1 → (values r).getD j 0 = S xs zs j) := by
  sorry

/-- Whenever merge_nodes head returns a result r, the number of nodes in r is len(r)=m, which is one less than the number of zero-valued nodes in head. Equivalently, r has exactly one node for each nonempty block of input values between two consecutive zero-valued nodes.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. -/
theorem spec_2 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r → (values r).length = zs.length - 1 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r → (values r).length = zs.length - 1) := by
  sorry

/-- Whenever merge_nodes head returns a result r, every value in r is positive: for every i with 0<=i<len(r), the i-th value of r is at least 1. In particular, r contains no node whose value is 0.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. -/
theorem spec_3 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r →
      ∀ i, i < (values r).length → 1 ≤ (values r).getD i 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r →
      ∀ i, i < (values r).length → 1 ≤ (values r).getD i 0) := by
  sorry

/-- Whenever merge_nodes head returns a result r, for every j with 0<=j<m, the j-th value of r exists and satisfies 1 <= value_j(r) <= 1000*(z_{j+1}-z_j-1).
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. For 0<=j<m define S_j=sum_{i=z_j+1}^{z_{j+1}-1} x_i. -/
theorem spec_4 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r →
      ∀ j, j < zs.length - 1 →
        ∃ v, (values r)[j]? = some v ∧ 1 ≤ v ∧
          v ≤ 1000 * ((zs.getD (j + 1) 0 : Int) - (zs.getD j 0 : Int) - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r →
      ∀ j, j < zs.length - 1 →
        ∃ v, (values r)[j]? = some v ∧ 1 ≤ v ∧
          v ≤ 1000 * ((zs.getD (j + 1) 0 : Int) - (zs.getD j 0 : Int) - 1)) := by
  sorry

/-- Whenever merge_nodes head returns a result r, the sum of all node values in r equals the sum of all node values in head: sum_{i=0}^{len(r)-1} value_i(r) = sum_{i=0}^{n-1} x_i. Since every zero-valued input node contributes 0, this is also the sum of all nonzero input values.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. -/
theorem spec_5 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r → (values r).sum = xs.sum := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r → (values r).sum = xs.sum) := by
  sorry

/-- Whenever merge_nodes head returns a result r, its length satisfies 1 <= len(r) <= floor((n-1)/2).
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. -/
theorem spec_6 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r →
      1 ≤ (values r).length ∧ (values r).length ≤ (xs.length - 1) / 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r →
      1 ≤ (values r).length ∧ (values r).length ≤ (xs.length - 1) / 2) := by
  sorry

/-- Whenever merge_nodes head returns a result r and m=1 (equivalently, the only zero-valued nodes are the first and last nodes), r has exactly one node and its only value is sum_{i=1}^{n-2} x_i.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. -/
theorem spec_7 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r → zs.length = 2 →
      (values r).length = 1 ∧ (values r).head? = some (blockSum xs 0 (xs.length - 1)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r → zs.length = 2 →
      (values r).length = 1 ∧ (values r).head? = some (blockSum xs 0 (xs.length - 1))) := by
  sorry

/-- Whenever merge_nodes head returns a result r and z_{j+1}=z_j+2 for every 0<=j<m (equivalently n=2m+1 and every block between consecutive zeros consists of exactly one node), then for every 0<=j<m the j-th value of r is x_{2j+1}.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. -/
theorem spec_8 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r →
      (∀ j, j < zs.length - 1 → zs.getD (j + 1) 0 = zs.getD j 0 + 2) →
      ∀ j, j < zs.length - 1 → (values r).getD j 0 = xs.getD (2 * j + 1) 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r →
      (∀ j, j < zs.length - 1 → zs.getD (j + 1) 0 = zs.getD j 0 + 2) →
      ∀ j, j < zs.length - 1 → (values r).getD j 0 = xs.getD (2 * j + 1) 0) := by
  sorry

/-- Whenever merge_nodes head returns a result r, len(r)=m; for every output index j with 0<=j<m, the j-th value of r is S_j, so the witness interval for output j is (z_j,z_{j+1}); and every input index i with x_i != 0 lies in exactly one interval (z_k,z_{k+1}) with 0<=k<m.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. For 0<=j<m define S_j=sum_{i=z_j+1}^{z_{j+1}-1} x_i. -/
theorem spec_9 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r →
      (values r).length = zs.length - 1 ∧
      (∀ j, j < zs.length - 1 → (values r).getD j 0 = S xs zs j) ∧
      (∀ i, i < xs.length → xs.getD i 0 ≠ 0 →
        ∃! k, k < zs.length - 1 ∧ zs.getD k 0 < i ∧ i < zs.getD (k + 1) 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r →
      (values r).length = zs.length - 1 ∧
      (∀ j, j < zs.length - 1 → (values r).getD j 0 = S xs zs j) ∧
      (∀ i, i < xs.length → xs.getD i 0 ≠ 0 →
        ∃! k, k < zs.length - 1 ∧ zs.getD k 0 < i ∧ i < zs.getD (k + 1) 0)) := by
  sorry

/-- For every input satisfying the preconditions, merge_nodes head returns a result r; it does not fail by panic, out-of-bounds access, or arithmetic overflow. In particular every segment sum S_j satisfies S_j <= 1000*200000 = 200000000, which is far below the maximum i64 value, so forming all sums is safe.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. For 0<=j<m define S_j=sum_{i=z_j+1}^{z_{j+1}-1} x_i. -/
theorem spec_10 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    (∃ r, Aegis.MergeNodes.merge_nodes head = .ok r) ∧
      ∀ j, j < zs.length - 1 → S xs zs j ≤ 1000 * 200000 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), (∃ r, Aegis.MergeNodes.merge_nodes head = Result.ok r) ∧
      ∀ j, j < zs.length - 1 → S xs zs j ≤ 1000 * 200000) := by
  sorry

/-- Whenever merge_nodes head returns a result r, the first value of r (index 0) equals sum_{i=1}^{z_1-1} x_i, the sum of the initial nonzero run immediately after the first zero and before the next zero.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. -/
theorem spec_11 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r →
      (values r).head? = some (blockSum xs 0 (zs.getD 1 0)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r →
      (values r).head? = some (blockSum xs 0 (zs.getD 1 0))) := by
  sorry

/-- Whenever merge_nodes head returns a result r, the last value of r (index len(r)-1) equals sum_{i=z_{m-1}+1}^{n-2} x_i, the sum of the final nonzero run after the penultimate zero and before the final zero.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. -/
theorem spec_12 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r →
      (values r).getLast? =
        some (blockSum xs (zs.getD (zs.length - 2) 0) (xs.length - 1)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r →
      (values r).getLast? =
        some (blockSum xs (zs.getD (zs.length - 2) 0) (xs.length - 1))) := by
  sorry

/-- Whenever merge_nodes head returns a result r, len(r)=m, and for all j,k with 0<=j<k<m, every input index i with z_j < i < z_{j+1} is less than every input index i' with z_k < i' < z_{k+1}.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. Let z_0<...<z_m be the zero indices; then z_0=0, z_m=n-1, m>=1, and z_{j+1}>=z_j+2. -/
theorem spec_13 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r →
      (values r).length = zs.length - 1 ∧
      ∀ j k i i', j < k → k < zs.length - 1 → zs.getD j 0 < i → i < zs.getD (j + 1) 0 →
        zs.getD k 0 < i' → i' < zs.getD (k + 1) 0 → i < i' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r →
      (values r).length = zs.length - 1 ∧
      ∀ j k i i', j < k → k < zs.length - 1 → zs.getD j 0 < i → i < zs.getD (j + 1) 0 →
        zs.getD k 0 < i' → i' < zs.getD (k + 1) 0 → i < i') := by
  sorry

/-- Whenever merge_nodes head returns a result r, len(r) equals the number of maximal contiguous runs of indices i with x_i != 0 in the input value sequence xs.
  Preconditions: Let xs=[x_0,...,x_{n-1}] be the values of head. Assume 3<=n<=200000, 0<=x_i<=1000 for all i, x_0=x_{n-1}=0, and no two adjacent x_i are both 0. -/
theorem spec_14 (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs) :
    ∀ r, Aegis.MergeNodes.merge_nodes head = .ok r →
      (values r).length = nonzeroRunCount xs := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (head : Aegis.MergeNodes.List) (xs : List Int) (zs : List Nat)
    (h : Pre head xs zs), ∀ r, Aegis.MergeNodes.merge_nodes head = Result.ok r →
      (values r).length = nonzeroRunCount xs) := by
  sorry

end AegisSpec.MergeNodes
