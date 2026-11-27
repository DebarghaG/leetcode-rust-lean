import Aegis.BuildMatrix.Code.Funs

/-!
# Specifications of `Aegis.BuildMatrix.build_matrix`

LeetCode problem `build-a-matrix-with-conditions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.BuildMatrix

abbrev Mat : Type := alloc.vec.Vec (alloc.vec.Vec Std.I64)

abbrev Conds : Type := Slice (alloc.vec.Vec Std.I64)

def cell? (M : Mat) (i j : Nat) : Option Int :=
  (M.val[i]?).bind fun row => (row.val[j]?).map fun x => x.val

def condPairs (conds : Conds) : List (Int × Int) :=
  conds.val.filterMap fun c =>
    match c.val.map (fun x => x.val) with
    | [a, b] => some (a, b)
    | _ => none

abbrev HasCond (conds : Conds) (a b : Int) : Prop := (a, b) ∈ condPairs conds

def CondsWF (conds : Conds) (k : Int) : Prop :=
  ∀ c ∈ conds.val, c.val.length = 2 ∧
    ∀ a b : Std.I64, c.val = [a, b] →
      1 ≤ a.val ∧ a.val ≤ k ∧ 1 ≤ b.val ∧ b.val ≤ k ∧ a.val ≠ b.val

def Shape (M : Mat) (k : Int) : Prop :=
  (M.val.length : Int) = k ∧ ∀ row ∈ M.val, (row.val.length : Int) = k

def Bounds (M : Mat) (k : Int) : Prop :=
  ∀ i j x : Nat, cell? M i j = some x → x = 0 ∨ (1 ≤ x ∧ x ≤ k)

def ExactlyOnce (M : Mat) (k : Int) : Prop :=
  ∀ x : Int, 1 ≤ x → x ≤ k → ∃! p : Nat × Nat, cell? M p.1 p.2 = some x

def RowOrderOK (M : Mat) (conds : Conds) : Prop :=
  ∀ a b : Int, HasCond conds a b →
    ∀ ia ja ib jb : Nat, cell? M ia ja = some a → cell? M ib jb = some b → ia < ib

def ColOrderOK (M : Mat) (conds : Conds) : Prop :=
  ∀ a b : Int, HasCond conds a b →
    ∀ ia ja ib jb : Nat, cell? M ia ja = some a → cell? M ib jb = some b → ja < jb

def ValidMatrix (k : Int) (rc cc : Conds) (M : Mat) : Prop :=
  Shape M k ∧ Bounds M k ∧ ExactlyOnce M k ∧ RowOrderOK M rc ∧ ColOrderOK M cc

def nonzeroCount (M : Mat) : Nat :=
  (M.val.map fun row => (row.val.filter fun x => decide (x.val ≠ 0)).length).sum

inductive Path (conds : Conds) : Int → Int → Prop where

  | single {a b : Int} : HasCond conds a b → Path conds a b

  | step {a b c : Int} : Path conds a b → HasCond conds b c → Path conds a c

def HasCycle (k : Int) (conds : Conds) : Prop :=
  ∃ x : Int, 1 ≤ x ∧ x ≤ k ∧ Path conds x x

def SameEntriesUpToDuplication (C C' : Conds) : Prop :=
  (∀ c, c ∈ C'.val → c ∈ C.val) ∧ ∀ c, c ∈ C.val → c ∈ C'.val

/-- Whenever build_matrix returns a result r, define a matrix M to be valid for (k,row_conditions,col_conditions) iff: (1) len(M)=k and for every i with 0 <= i < k, len(M[i])=k; (2) for every i,j with 0 <= i < k and 0 <= j < k, M[i][j]=0 or 1 <= M[i][j] <= k; (3) for every x with 1 <= x <= k there is exactly one pair (i,j) with 0 <= i < k, 0 <= j < k, and M[i][j]=x; (4) for every t with 0 <= t < len(row_conditions), writing row_conditions[t]=[a,b], for every cells (i_a,j_a) and (i_b,j_b) with 0 <= i_a < k, 0 <= j_a < k, 0 <= i_b < k, 0 <= j_b < k, M[i_a][j_a]=a, and M[i_b][j_b]=b, we have i_a < i_b; (5) for every t with 0 <= t < len(col_conditions), writing col_conditions[t]=[a,b], for every cells (i_a,j_a) and (i_b,j_b) with 0 <= i_a < k, 0 <= j_a < k, 0 <= i_b < k, 0 <= j_b < k, M[i_a][j_a]=a, and M[i_b][j_b]=b, we have j_a < j_b. Then either (A) there exists a valid M and r itself is valid, or (B) no valid M exists and len(r)=0. These alternatives are exclusive.
  Preconditions: k is an integer with 2 <= k <= 400; row_conditions and col_conditions are slices of vectors of 64-bit integers; 1 <= len(row_conditions) <= 10000; 1 <= len(col_conditions) <= 10000; for every t with 0 <= t < len(row_conditions), len(row_conditions[t]) = 2, and if row_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b; for every t with 0 <= t < len(col_conditions), len(col_conditions[t]) = 2, and if col_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b. -/
theorem spec_1 (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r) :
    ((∃ M : Mat, ValidMatrix k.val rc cc M) ∧ ValidMatrix k.val rc cc r) ∨
      ((¬ ∃ M : Mat, ValidMatrix k.val rc cc M) ∧ r.val.length = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r), ((∃ M : Mat, ValidMatrix k.val rc cc M) ∧ ValidMatrix k.val rc cc r) ∨
      ((¬ ∃ M : Mat, ValidMatrix k.val rc cc M) ∧ r.val.length = 0)) := by
  sorry

/-- For every input satisfying the preconditions, the call build_matrix(k,row_conditions,col_conditions) does not fail: there exists a vector r of vectors of 64-bit integers such that the function returns r (an Ok result, not Err or panic).
  Preconditions: k is an integer with 2 <= k <= 400; row_conditions and col_conditions are slices of vectors of 64-bit integers; 1 <= len(row_conditions) <= 10000; 1 <= len(col_conditions) <= 10000; for every t with 0 <= t < len(row_conditions), len(row_conditions[t]) = 2, and if row_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b; for every t with 0 <= t < len(col_conditions), len(col_conditions[t]) = 2, and if col_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b. -/
theorem spec_2 (k : Std.I64) (rc cc : Conds)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val) :
    ∃ r : Mat, Aegis.BuildMatrix.build_matrix k rc cc = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (k : Std.I64) (rc cc : Conds)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val), ∃ r : Mat, Aegis.BuildMatrix.build_matrix k rc cc = ok r) := by
  sorry

/-- Whenever build_matrix returns a result r, either len(r)=0, or len(r)=k and for every i with 0 <= i < k, len(r[i])=k. In particular, a nonempty result is a k-by-k matrix and an empty result has no rows.
  Preconditions: k is an integer with 2 <= k <= 400; row_conditions and col_conditions are slices of vectors of 64-bit integers; 1 <= len(row_conditions) <= 10000; 1 <= len(col_conditions) <= 10000; for every t with 0 <= t < len(row_conditions), len(row_conditions[t]) = 2, and if row_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b; for every t with 0 <= t < len(col_conditions), len(col_conditions[t]) = 2, and if col_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b. -/
theorem spec_3 (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r) :
    r.val.length = 0 ∨ Shape r k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r), r.val.length = 0 ∨ Shape r k.val) := by
  sorry

/-- Whenever build_matrix returns a result r with len(r)>0, for every i,j with 0 <= i < len(r) and 0 <= j < len(r[i]), either r[i][j]=0 or 1 <= r[i][j] <= k.
  Preconditions: k is an integer with 2 <= k <= 400; row_conditions and col_conditions are slices of vectors of 64-bit integers; 1 <= len(row_conditions) <= 10000; 1 <= len(col_conditions) <= 10000; for every t with 0 <= t < len(row_conditions), len(row_conditions[t]) = 2, and if row_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b; for every t with 0 <= t < len(col_conditions), len(col_conditions[t]) = 2, and if col_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b. -/
theorem spec_4 (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length) :
    Bounds r k.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length), Bounds r k.val) := by
  sorry

/-- Whenever build_matrix returns a result r with len(r)>0, for every x with 1 <= x <= k there is exactly one pair (i,j) with 0 <= i < len(r), 0 <= j < len(r[i]), and r[i][j]=x.
  Preconditions: k is an integer with 2 <= k <= 400; row_conditions and col_conditions are slices of vectors of 64-bit integers; 1 <= len(row_conditions) <= 10000; 1 <= len(col_conditions) <= 10000; for every t with 0 <= t < len(row_conditions), len(row_conditions[t]) = 2, and if row_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b; for every t with 0 <= t < len(col_conditions), len(col_conditions[t]) = 2, and if col_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b. -/
theorem spec_5 (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length) :
    ExactlyOnce r k.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length), ExactlyOnce r k.val) := by
  sorry

/-- Whenever build_matrix returns a result r with len(r)>0, the number of pairs (i,j) with 0 <= i < len(r), 0 <= j < len(r[i]), and r[i][j] != 0 is exactly k.
  Preconditions: k is an integer with 2 <= k <= 400; row_conditions and col_conditions are slices of vectors of 64-bit integers; 1 <= len(row_conditions) <= 10000; 1 <= len(col_conditions) <= 10000; for every t with 0 <= t < len(row_conditions), len(row_conditions[t]) = 2, and if row_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b; for every t with 0 <= t < len(col_conditions), len(col_conditions[t]) = 2, and if col_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b. -/
theorem spec_6 (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length) :
    (nonzeroCount r : Int) = k.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length), (nonzeroCount r : Int) = k.val) := by
  sorry

/-- Whenever build_matrix returns a result r with len(r)>0, for every t with 0 <= t < len(row_conditions), writing row_conditions[t]=[a,b], for every cells (i_a,j_a) and (i_b,j_b) with 0 <= i_a < len(r), 0 <= j_a < len(r[i_a]), 0 <= i_b < len(r), 0 <= j_b < len(r[i_b]), r[i_a][j_a]=a, and r[i_b][j_b]=b, we have i_a < i_b.
  Preconditions: k is an integer with 2 <= k <= 400; row_conditions and col_conditions are slices of vectors of 64-bit integers; 1 <= len(row_conditions) <= 10000; 1 <= len(col_conditions) <= 10000; for every t with 0 <= t < len(row_conditions), len(row_conditions[t]) = 2, and if row_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b; for every t with 0 <= t < len(col_conditions), len(col_conditions[t]) = 2, and if col_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b. -/
theorem spec_7 (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length) :
    RowOrderOK r rc := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length), RowOrderOK r rc) := by
  sorry

/-- Whenever build_matrix returns a result r with len(r)>0, for every t with 0 <= t < len(col_conditions), writing col_conditions[t]=[a,b], for every cells (i_a,j_a) and (i_b,j_b) with 0 <= i_a < len(r), 0 <= j_a < len(r[i_a]), 0 <= i_b < len(r), 0 <= j_b < len(r[i_b]), r[i_a][j_a]=a, and r[i_b][j_b]=b, we have j_a < j_b.
  Preconditions: k is an integer with 2 <= k <= 400; row_conditions and col_conditions are slices of vectors of 64-bit integers; 1 <= len(row_conditions) <= 10000; 1 <= len(col_conditions) <= 10000; for every t with 0 <= t < len(row_conditions), len(row_conditions[t]) = 2, and if row_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b; for every t with 0 <= t < len(col_conditions), len(col_conditions[t]) = 2, and if col_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b. -/
theorem spec_8 (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length) :
    ColOrderOK r cc := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length), ColOrderOK r cc) := by
  sorry

/-- Whenever build_matrix returns a result r, if either the row condition graph or the column condition graph contains a directed cycle, then len(r)=0. The row condition graph has vertex set {1,...,k} and a directed edge a -> b for each entry [a,b] of row_conditions; a directed cycle means there are t >= 1 and numbers x_0,...,x_t in {1,...,k} with x_t = x_0 and, for every q with 0 <= q < t, the pair [x_q,x_{q+1}] occurs as an entry of row_conditions. The column condition graph is defined analogously from col_conditions.
  Preconditions: k is an integer with 2 <= k <= 400; row_conditions and col_conditions are slices of vectors of 64-bit integers; 1 <= len(row_conditions) <= 10000; 1 <= len(col_conditions) <= 10000; for every t with 0 <= t < len(row_conditions), len(row_conditions[t]) = 2, and if row_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b; for every t with 0 <= t < len(col_conditions), len(col_conditions[t]) = 2, and if col_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b. -/
theorem spec_9 (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hcyc : HasCycle k.val rc ∨ HasCycle k.val cc) :
    r.val.length = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hcyc : HasCycle k.val rc ∨ HasCycle k.val cc), r.val.length = 0) := by
  sorry

/-- Whenever build_matrix returns a result r, if neither the row condition graph nor the column condition graph contains a directed cycle, then len(r)>0. Here a directed cycle in row_conditions means there are t >= 1 and numbers x_0,...,x_t in {1,...,k} with x_t = x_0 and each pair [x_q,x_{q+1}] for 0 <= q < t occurs as an entry of row_conditions; the same definition applies to col_conditions.
  Preconditions: k is an integer with 2 <= k <= 400; row_conditions and col_conditions are slices of vectors of 64-bit integers; 1 <= len(row_conditions) <= 10000; 1 <= len(col_conditions) <= 10000; for every t with 0 <= t < len(row_conditions), len(row_conditions[t]) = 2, and if row_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b; for every t with 0 <= t < len(col_conditions), len(col_conditions[t]) = 2, and if col_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b. -/
theorem spec_10 (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hnrc : ¬ HasCycle k.val rc) (hncc : ¬ HasCycle k.val cc) :
    0 < r.val.length := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hnrc : ¬ HasCycle k.val rc) (hncc : ¬ HasCycle k.val cc), 0 < r.val.length) := by
  sorry

/-- Whenever build_matrix returns a result r with len(r)>0, let row_conditions' be any list obtained from row_conditions by reordering its entries and then duplicating some entries, and let col_conditions' be any list obtained from col_conditions by reordering its entries and then duplicating some entries. Then r is also a valid matrix for (k,row_conditions',col_conditions'): len(r)=k, every row of r has length k, every cell of r is 0 or an integer in [1,k], every x with 1 <= x <= k appears exactly once in r, every entry [a,b] of row_conditions' satisfies that every occurrence of a in r has row index strictly less than every occurrence of b in r, and every entry [a,b] of col_conditions' satisfies that every occurrence of a in r has column index strictly less than every occurrence of b in r. In particular, duplicate conditions impose no new constraint and the order of the condition lists is irrelevant.
  Preconditions: k is an integer with 2 <= k <= 400; row_conditions and col_conditions are slices of vectors of 64-bit integers; 1 <= len(row_conditions) <= 10000; 1 <= len(col_conditions) <= 10000; for every t with 0 <= t < len(row_conditions), len(row_conditions[t]) = 2, and if row_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b; for every t with 0 <= t < len(col_conditions), len(col_conditions[t]) = 2, and if col_conditions[t] = [a,b] then 1 <= a <= k, 1 <= b <= k, and a != b. -/
theorem spec_11 (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length)
    (rc' cc' : Conds) (hrc' : SameEntriesUpToDuplication rc rc')
    (hcc' : SameEntriesUpToDuplication cc cc') :
    ValidMatrix k.val rc' cc' r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (k : Std.I64) (rc cc : Conds) (r : Mat)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 400)
    (hrc_min : 1 ≤ rc.val.length) (hrc_max : rc.val.length ≤ 10000)
    (hcc_min : 1 ≤ cc.val.length) (hcc_max : cc.val.length ≤ 10000)
    (hrc_wf : CondsWF rc k.val) (hcc_wf : CondsWF cc k.val)
    (hres : Aegis.BuildMatrix.build_matrix k rc cc = ok r)
    (hne : 0 < r.val.length)
    (rc' cc' : Conds) (hrc' : SameEntriesUpToDuplication rc rc')
    (hcc' : SameEntriesUpToDuplication cc cc'), ValidMatrix k.val rc' cc' r) := by
  sorry

end AegisSpec.BuildMatrix
