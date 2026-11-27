import Aegis.ValidArrangement.Code.Funs

/-!
# Specifications of `Aegis.ValidArrangement.valid_arrangement`

LeetCode problem `valid-arrangement-of-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ValidArrangement

  def rowFst (v : alloc.vec.Vec I64) : ℤ := (v.val.getD 0 0#i64).val

  def rowSnd (v : alloc.vec.Vec I64) : ℤ := (v.val.getD 1 0#i64).val

  def rowVal (v : alloc.vec.Vec I64) : ℤ × ℤ := (rowFst v, rowSnd v)

  def rowsContent (rows : List (alloc.vec.Vec I64)) : List (ℤ × ℤ) := rows.map rowVal

  def pairsContent (pairs : Slice (alloc.vec.Vec I64)) : List (ℤ × ℤ) :=
    rowsContent pairs.val

  def IsPairChain : List (ℤ × ℤ) → Prop
    | [] => True
    | [_] => True
    | p :: q :: rest => p.2 = q.1 ∧ IsPairChain (q :: rest)

  def HasChainedPermutation (l : List (ℤ × ℤ)) : Prop :=
    ∃ l' : List (ℤ × ℤ), List.Perm l l' ∧ IsPairChain l'

  def outDeg (pairs : Slice (alloc.vec.Vec I64)) (v : ℤ) : ℕ :=
    ((pairsContent pairs).filter (fun p => p.1 = v)).length

  def inDeg (pairs : Slice (alloc.vec.Vec I64)) (v : ℤ) : ℕ :=
    ((pairsContent pairs).filter (fun p => p.2 = v)).length

  def degImbalance (pairs : Slice (alloc.vec.Vec I64)) (v : ℤ) : ℤ :=
    (outDeg pairs v : ℤ) - (inDeg pairs v : ℤ)

  def imbalance (a b v : ℤ) : ℤ :=
    if a = b then 0 else if v = a then 1 else if v = b then -1 else 0

  def firstOut (r : alloc.vec.Vec (alloc.vec.Vec I64)) : Option ℤ :=
    (rowsContent r.val).head?.map (fun p => p.1)

  def lastIn (r : alloc.vec.Vec (alloc.vec.Vec I64)) : Option ℤ :=
    (rowsContent r.val).getLast?.map (fun p => p.2)

  def ValidInput (pairs : Slice (alloc.vec.Vec I64)) : Prop :=
    1 ≤ pairs.val.length ∧
    pairs.val.length ≤ 100000 ∧
    (∀ v ∈ pairs.val, v.val.length = 2) ∧
    (∀ v ∈ pairs.val, 0 ≤ rowFst v ∧ rowFst v ≤ 10 ^ 9) ∧
    (∀ v ∈ pairs.val, 0 ≤ rowSnd v ∧ rowSnd v ≤ 10 ^ 9) ∧
    (∀ v ∈ pairs.val, rowFst v ≠ rowSnd v) ∧
    pairs.val.Nodup ∧
    HasChainedPermutation (pairsContent pairs)

  /-- Whenever the function returns a result r, r is a valid arrangement of pairs: len(r) = n, and there exists a bijection σ : {0,...,n-1} -> {0,...,n-1} such that for every i with 0 <= i < n, r[i] = pairs[σ(i)], and for every i with 1 <= i < n, r[i-1][1] = r[i][0].
    Preconditions: Let n = len(pairs). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, len(pairs[i]) = 2, 0 <= pairs[i][0] <= 10^9, 0 <= pairs[i][1] <= 10^9, and pairs[i][0] != pairs[i][1]; for every i,j with 0 <= i < j < n, pairs[i] != pairs[j]; and there exists a bijection σ : {0,...,n-1} -> {0,...,n-1} such that for every i with 1 <= i < n, pairs[σ(i-1)][1] = pairs[σ(i)][0]. -/
  theorem spec_1 (pairs : Slice (alloc.vec.Vec I64)) (h : ValidInput pairs) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.ValidArrangement.valid_arrangement pairs = ok r →
        r.val.length = pairs.val.length ∧
        List.Perm r.val pairs.val ∧
        IsPairChain (rowsContent r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (pairs : Slice (alloc.vec.Vec I64)) (h : ValidInput pairs), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.ValidArrangement.valid_arrangement pairs = ok r →
          r.val.length = pairs.val.length ∧
          List.Perm r.val pairs.val ∧
          IsPairChain (rowsContent r.val)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or get stuck) for every input satisfying the preconditions.
    Preconditions: Let n = len(pairs). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, len(pairs[i]) = 2, 0 <= pairs[i][0] <= 10^9, 0 <= pairs[i][1] <= 10^9, and pairs[i][0] != pairs[i][1]; for every i,j with 0 <= i < j < n, pairs[i] != pairs[j]; and there exists a bijection σ : {0,...,n-1} -> {0,...,n-1} such that for every i with 1 <= i < n, pairs[σ(i-1)][1] = pairs[σ(i)][0]. -/
  theorem spec_2 (pairs : Slice (alloc.vec.Vec I64)) (h : ValidInput pairs) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.ValidArrangement.valid_arrangement pairs = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (pairs : Slice (alloc.vec.Vec I64)) (h : ValidInput pairs), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.ValidArrangement.valid_arrangement pairs = ok r) := by
    sorry

  /-- Whenever the function returns r, let a = r[0][0] and b = r[len(r)-1][1]. For every integer value v, define out(v) = |{j | 0 <= j < n and pairs[j][0] = v}| and in(v) = |{j | 0 <= j < n and pairs[j][1] = v}|. Then out(v) - in(v) equals 1 if v = a and a != b; equals -1 if v = b and a != b; and equals 0 otherwise.
    Preconditions: Let n = len(pairs). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, len(pairs[i]) = 2, 0 <= pairs[i][0] <= 10^9, 0 <= pairs[i][1] <= 10^9, and pairs[i][0] != pairs[i][1]; for every i,j with 0 <= i < j < n, pairs[i] != pairs[j]; and there exists a bijection σ : {0,...,n-1} -> {0,...,n-1} such that for every i with 1 <= i < n, pairs[σ(i-1)][1] = pairs[σ(i)][0]. -/
  theorem spec_3 (pairs : Slice (alloc.vec.Vec I64)) (h : ValidInput pairs) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.ValidArrangement.valid_arrangement pairs = ok r →
        ∀ a b : ℤ, firstOut r = some a → lastIn r = some b →
          ∀ v : ℤ, degImbalance pairs v = imbalance a b v := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (pairs : Slice (alloc.vec.Vec I64)) (h : ValidInput pairs), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.ValidArrangement.valid_arrangement pairs = ok r →
          ∀ a b : ℤ, firstOut r = some a → lastIn r = some b →
            ∀ v : ℤ, degImbalance pairs v = imbalance a b v) := by
    sorry

  /-- Whenever the function returns r, let a = r[0][0] and b = r[len(r)-1][1]. Define out(v) and in(v) as the numbers of input pairs whose first coordinate is v and whose second coordinate is v, respectively. Then a = b if and only if out(v) = in(v) for every integer value v.
    Preconditions: Let n = len(pairs). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, len(pairs[i]) = 2, 0 <= pairs[i][0] <= 10^9, 0 <= pairs[i][1] <= 10^9, and pairs[i][0] != pairs[i][1]; for every i,j with 0 <= i < j < n, pairs[i] != pairs[j]; and there exists a bijection σ : {0,...,n-1} -> {0,...,n-1} such that for every i with 1 <= i < n, pairs[σ(i-1)][1] = pairs[σ(i)][0]. -/
  theorem spec_4 (pairs : Slice (alloc.vec.Vec I64)) (h : ValidInput pairs) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.ValidArrangement.valid_arrangement pairs = ok r →
        ∀ a b : ℤ, firstOut r = some a → lastIn r = some b →
          (a = b ↔ ∀ v : ℤ, degImbalance pairs v = 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (pairs : Slice (alloc.vec.Vec I64)) (h : ValidInput pairs), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.ValidArrangement.valid_arrangement pairs = ok r →
          ∀ a b : ℤ, firstOut r = some a → lastIn r = some b →
            (a = b ↔ ∀ v : ℤ, degImbalance pairs v = 0)) := by
    sorry

  /-- Whenever the function returns r, define out(v) and in(v) as the numbers of input pairs whose first coordinate is v and whose second coordinate is v, respectively. If there exists an integer v with out(v) != in(v), then r[0][0] is the unique value v with out(v) = in(v) + 1, and r[len(r)-1][1] is the unique value v with in(v) = out(v) + 1.
    Preconditions: Let n = len(pairs). The input satisfies the problem constraints: 1 <= n <= 100000; for every i with 0 <= i < n, len(pairs[i]) = 2, 0 <= pairs[i][0] <= 10^9, 0 <= pairs[i][1] <= 10^9, and pairs[i][0] != pairs[i][1]; for every i,j with 0 <= i < j < n, pairs[i] != pairs[j]; and there exists a bijection σ : {0,...,n-1} -> {0,...,n-1} such that for every i with 1 <= i < n, pairs[σ(i-1)][1] = pairs[σ(i)][0]. -/
  theorem spec_5 (pairs : Slice (alloc.vec.Vec I64)) (h : ValidInput pairs) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.ValidArrangement.valid_arrangement pairs = ok r →
        (∃ v : ℤ, degImbalance pairs v ≠ 0) →
          (∃! v : ℤ, degImbalance pairs v = 1) ∧
          (∀ v : ℤ, degImbalance pairs v = 1 → firstOut r = some v) ∧
          (∃! v : ℤ, degImbalance pairs v = -1) ∧
          (∀ v : ℤ, degImbalance pairs v = -1 → lastIn r = some v) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (pairs : Slice (alloc.vec.Vec I64)) (h : ValidInput pairs), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.ValidArrangement.valid_arrangement pairs = ok r →
          (∃ v : ℤ, degImbalance pairs v ≠ 0) →
            (∃! v : ℤ, degImbalance pairs v = 1) ∧
            (∀ v : ℤ, degImbalance pairs v = 1 → firstOut r = some v) ∧
            (∃! v : ℤ, degImbalance pairs v = -1) ∧
            (∀ v : ℤ, degImbalance pairs v = -1 → lastIn r = some v)) := by
    sorry

  end AegisSpec.ValidArrangement
