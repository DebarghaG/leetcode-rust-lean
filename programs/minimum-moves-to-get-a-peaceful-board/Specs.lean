import Aegis.MinMoves.Code.Funs

/-!
# Specifications of `Aegis.MinMoves.min_moves`

LeetCode problem `minimum-moves-to-get-a-peaceful-board`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinMoves

  namespace AegisSpec.MinMoves

  def xAt (rooks : Slice (alloc.vec.Vec I64)) (i : Fin rooks.val.length) : ℤ :=
    match (rooks.val.get i).slice.val[0]? with
    | some v => v.val
    | none => 0

  def yAt (rooks : Slice (alloc.vec.Vec I64)) (i : Fin rooks.val.length) : ℤ :=
    match (rooks.val.get i).slice.val[1]? with
    | some v => v.val
    | none => 0

  def xList (rooks : Slice (alloc.vec.Vec I64)) : List ℤ := List.ofFn (xAt rooks)

  def yList (rooks : Slice (alloc.vec.Vec I64)) : List ℤ := List.ofFn (yAt rooks)

  abbrev IsPerm {n : ℕ} (σ : Fin n → Fin n) : Prop := Function.Bijective σ

  def perms (n : ℕ) : Finset (Fin n → Fin n) := Finset.univ.filter (fun σ => IsPerm σ)

  def totalCost {n : ℕ} (x y : Fin n → ℤ) (σ τ : Fin n → Fin n) : ℤ :=
    ∑ i : Fin n, (|x i - ((σ i : ℕ) : ℤ)| + |y i - ((τ i : ℕ) : ℤ)|)

  def rowCost {n : ℕ} (x : Fin n → ℤ) (σ : Fin n → Fin n) : ℤ :=
    ∑ i : Fin n, |x i - ((σ i : ℕ) : ℤ)|

  def colCost {n : ℕ} (y : Fin n → ℤ) (τ : Fin n → Fin n) : ℤ :=
    ∑ i : Fin n, |y i - ((τ i : ℕ) : ℤ)|

  noncomputable def minTotalCost {n : ℕ} (x y : Fin n → ℤ) : ℤ :=
    let s := ((perms n).product (perms n)).image
      (fun p : (Fin n → Fin n) × (Fin n → Fin n) => totalCost x y p.1 p.2)
    if h : s.Nonempty then s.min' h else 0

  noncomputable def minRowCost {n : ℕ} (x : Fin n → ℤ) : ℤ :=
    let s := (perms n).image (fun σ => rowCost x σ)
    if h : s.Nonempty then s.min' h else 0

  noncomputable def minColCost {n : ℕ} (y : Fin n → ℤ) : ℤ :=
    let s := (perms n).image (fun τ => colCost y τ)
    if h : s.Nonempty then s.min' h else 0

  def insertSorted (a : ℤ) : List ℤ → List ℤ
    | [] => [a]
    | b :: t => if a ≤ b then a :: b :: t else b :: insertSorted a t

  def sortList : List ℤ → List ℤ
    | [] => []
    | a :: t => insertSorted a (sortList t)

  def sortedAt {n : ℕ} (l : List ℤ) (i : Fin n) : ℤ := (sortList l).getD i.val 0

  def permuteList {α : Type} (l : List α) (p : Fin l.length → Fin l.length) : List α :=
    List.ofFn (fun i : Fin l.length => l.get (p i))

  /-- Whenever min_moves(rooks) returns a result r, r is equal to the minimum, over all pairs of permutations sigma and tau of {0,...,n-1}, of the sum over i = 0,...,n-1 of (|rooks[i][0] - sigma(i)| + |rooks[i][1] - tau(i)|). Here a permutation of {0,...,n-1} is a bijection from that set to itself, and |.| denotes absolute value. Equivalently, r is the least total number of unit horizontal/vertical moves needed to move the rooks to a configuration with exactly one rook in every row and every column.
    Preconditions: Let n = len(rooks). The input satisfies: 1 <= n <= 500; for every i with 0 <= i < n, len(rooks[i]) = 2, 0 <= rooks[i][0] <= n-1, and 0 <= rooks[i][1] <= n-1; and for every i, j with 0 <= i < j < n, (rooks[i][0], rooks[i][1]) != (rooks[j][0], rooks[j][1]). -/
  theorem spec_1 (rooks : Slice (alloc.vec.Vec I64))
      (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
      (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
      (hbounds : ∀ i : Fin rooks.val.length,
        0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
        0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
      (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
        (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)) :
      ∀ r : I64, min_moves rooks = ok r → r.val = minTotalCost (xAt rooks) (yAt rooks) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (rooks : Slice (alloc.vec.Vec I64))
        (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
        (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
        (hbounds : ∀ i : Fin rooks.val.length,
          0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
          0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
        (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
          (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)), ∀ r : I64, min_moves rooks = ok r → r.val = minTotalCost (xAt rooks) (yAt rooks)) := by
    sorry

  /-- The function min_moves(rooks) returns a result (it does not fail: no panic, out-of-bounds access, or integer overflow occurs).
    Preconditions: Let n = len(rooks). The input satisfies: 1 <= n <= 500; for every i with 0 <= i < n, len(rooks[i]) = 2, 0 <= rooks[i][0] <= n-1, and 0 <= rooks[i][1] <= n-1; and for every i, j with 0 <= i < j < n, (rooks[i][0], rooks[i][1]) != (rooks[j][0], rooks[j][1]). -/
  theorem spec_2 (rooks : Slice (alloc.vec.Vec I64))
      (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
      (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
      (hbounds : ∀ i : Fin rooks.val.length,
        0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
        0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
      (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
        (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)) :
      ∃ r : I64, min_moves rooks = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (rooks : Slice (alloc.vec.Vec I64))
        (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
        (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
        (hbounds : ∀ i : Fin rooks.val.length,
          0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
          0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
        (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
          (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)), ∃ r : I64, min_moves rooks = ok r) := by
    sorry

  /-- Whenever min_moves(rooks) returns r, r = 0 if and only if the n numbers rooks[0][0],...,rooks[n-1][0] are pairwise distinct and the n numbers rooks[0][1],...,rooks[n-1][1] are pairwise distinct (equivalently, the initial board already has exactly one rook in each row and each column).
    Preconditions: Let n = len(rooks). The input satisfies: 1 <= n <= 500; for every i with 0 <= i < n, len(rooks[i]) = 2, 0 <= rooks[i][0] <= n-1, and 0 <= rooks[i][1] <= n-1; and for every i, j with 0 <= i < j < n, (rooks[i][0], rooks[i][1]) != (rooks[j][0], rooks[j][1]). -/
  theorem spec_3 (rooks : Slice (alloc.vec.Vec I64))
      (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
      (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
      (hbounds : ∀ i : Fin rooks.val.length,
        0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
        0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
      (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
        (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)) :
      ∀ r : I64, min_moves rooks = ok r →
        (r.val = 0 ↔ Function.Injective (xAt rooks) ∧ Function.Injective (yAt rooks)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (rooks : Slice (alloc.vec.Vec I64))
        (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
        (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
        (hbounds : ∀ i : Fin rooks.val.length,
          0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
          0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
        (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
          (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)), ∀ r : I64, min_moves rooks = ok r →
          (r.val = 0 ↔ Function.Injective (xAt rooks) ∧ Function.Injective (yAt rooks))) := by
    sorry

  /-- Whenever min_moves(rooks) returns r, r <= sum over i = 0,...,n-1 of (|rooks[i][0] - i| + |rooks[i][1] - i|).
    Preconditions: Let n = len(rooks). The input satisfies: 1 <= n <= 500; for every i with 0 <= i < n, len(rooks[i]) = 2, 0 <= rooks[i][0] <= n-1, and 0 <= rooks[i][1] <= n-1; and for every i, j with 0 <= i < j < n, (rooks[i][0], rooks[i][1]) != (rooks[j][0], rooks[j][1]). -/
  theorem spec_4 (rooks : Slice (alloc.vec.Vec I64))
      (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
      (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
      (hbounds : ∀ i : Fin rooks.val.length,
        0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
        0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
      (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
        (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)) :
      ∀ r : I64, min_moves rooks = ok r →
        r.val ≤ ∑ i : Fin rooks.val.length,
          (|xAt rooks i - ((i : ℕ) : ℤ)| + |yAt rooks i - ((i : ℕ) : ℤ)|) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (rooks : Slice (alloc.vec.Vec I64))
        (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
        (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
        (hbounds : ∀ i : Fin rooks.val.length,
          0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
          0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
        (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
          (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)), ∀ r : I64, min_moves rooks = ok r →
          r.val ≤ ∑ i : Fin rooks.val.length,
            (|xAt rooks i - ((i : ℕ) : ℤ)| + |yAt rooks i - ((i : ℕ) : ℤ)|)) := by
    sorry

  /-- Whenever min_moves(rooks) returns r, let R be the minimum over permutations sigma of {0,...,n-1} of sum over i = 0,...,n-1 of |rooks[i][0] - sigma(i)|, and let C be the minimum over permutations tau of {0,...,n-1} of sum over i = 0,...,n-1 of |rooks[i][1] - tau(i)|. Then r = R + C.
    Preconditions: Let n = len(rooks). The input satisfies: 1 <= n <= 500; for every i with 0 <= i < n, len(rooks[i]) = 2, 0 <= rooks[i][0] <= n-1, and 0 <= rooks[i][1] <= n-1; and for every i, j with 0 <= i < j < n, (rooks[i][0], rooks[i][1]) != (rooks[j][0], rooks[j][1]). -/
  theorem spec_5 (rooks : Slice (alloc.vec.Vec I64))
      (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
      (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
      (hbounds : ∀ i : Fin rooks.val.length,
        0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
        0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
      (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
        (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)) :
      ∀ r : I64, min_moves rooks = ok r →
        r.val = minRowCost (xAt rooks) + minColCost (yAt rooks) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (rooks : Slice (alloc.vec.Vec I64))
        (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
        (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
        (hbounds : ∀ i : Fin rooks.val.length,
          0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
          0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
        (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
          (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)), ∀ r : I64, min_moves rooks = ok r →
          r.val = minRowCost (xAt rooks) + minColCost (yAt rooks)) := by
    sorry

  /-- Whenever min_moves(rooks) returns r, there exist permutations sigma and tau of {0,...,n-1} such that sum over i = 0,...,n-1 of (|rooks[i][0] - sigma(i)| + |rooks[i][1] - tau(i)|) = r.
    Preconditions: Let n = len(rooks). The input satisfies: 1 <= n <= 500; for every i with 0 <= i < n, len(rooks[i]) = 2, 0 <= rooks[i][0] <= n-1, and 0 <= rooks[i][1] <= n-1; and for every i, j with 0 <= i < j < n, (rooks[i][0], rooks[i][1]) != (rooks[j][0], rooks[j][1]). -/
  theorem spec_6 (rooks : Slice (alloc.vec.Vec I64))
      (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
      (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
      (hbounds : ∀ i : Fin rooks.val.length,
        0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
        0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
      (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
        (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)) :
      ∀ r : I64, min_moves rooks = ok r →
        ∃ σ τ : Fin rooks.val.length → Fin rooks.val.length,
          IsPerm σ ∧ IsPerm τ ∧ totalCost (xAt rooks) (yAt rooks) σ τ = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (rooks : Slice (alloc.vec.Vec I64))
        (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
        (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
        (hbounds : ∀ i : Fin rooks.val.length,
          0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
          0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
        (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
          (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)), ∀ r : I64, min_moves rooks = ok r →
          ∃ σ τ : Fin rooks.val.length → Fin rooks.val.length,
            IsPerm σ ∧ IsPerm τ ∧ totalCost (xAt rooks) (yAt rooks) σ τ = r.val) := by
    sorry

  /-- Whenever min_moves(rooks) returns r, for every pair of permutations sigma and tau of {0,...,n-1}, sum over i = 0,...,n-1 of (|rooks[i][0] - sigma(i)| + |rooks[i][1] - tau(i)|) >= r.
    Preconditions: Let n = len(rooks). The input satisfies: 1 <= n <= 500; for every i with 0 <= i < n, len(rooks[i]) = 2, 0 <= rooks[i][0] <= n-1, and 0 <= rooks[i][1] <= n-1; and for every i, j with 0 <= i < j < n, (rooks[i][0], rooks[i][1]) != (rooks[j][0], rooks[j][1]). -/
  theorem spec_7 (rooks : Slice (alloc.vec.Vec I64))
      (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
      (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
      (hbounds : ∀ i : Fin rooks.val.length,
        0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
        0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
      (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
        (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)) :
      ∀ r : I64, min_moves rooks = ok r →
        ∀ σ τ : Fin rooks.val.length → Fin rooks.val.length,
          IsPerm σ → IsPerm τ → totalCost (xAt rooks) (yAt rooks) σ τ ≥ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (rooks : Slice (alloc.vec.Vec I64))
        (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
        (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
        (hbounds : ∀ i : Fin rooks.val.length,
          0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
          0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
        (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
          (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)), ∀ r : I64, min_moves rooks = ok r →
          ∀ σ τ : Fin rooks.val.length → Fin rooks.val.length,
            IsPerm σ → IsPerm τ → totalCost (xAt rooks) (yAt rooks) σ τ ≥ r.val) := by
    sorry

  /-- Whenever min_moves(rooks) returns r and min_moves(rooks2) returns r2, r = r2.
    Preconditions: Let n = len(rooks). The input satisfies: 1 <= n <= 500; for every i with 0 <= i < n, len(rooks[i]) = 2, 0 <= rooks[i][0] <= n-1, and 0 <= rooks[i][1] <= n-1; and for every i, j with 0 <= i < j < n, (rooks[i][0], rooks[i][1]) != (rooks[j][0], rooks[j][1]). Let p be a permutation of {0,...,n-1} and let rooks2 be the list of length n with rooks2[i] = rooks[p(i)] for every i. -/
  theorem spec_8 (rooks rooks2 : Slice (alloc.vec.Vec I64))
      (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
      (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
      (hbounds : ∀ i : Fin rooks.val.length,
        0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
        0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
      (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
        (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j))
      (p : Fin rooks.val.length → Fin rooks.val.length) (hp : IsPerm p)
      (hrooks2 : rooks2.val = permuteList rooks.val p) :
      ∀ r r2 : I64, min_moves rooks = ok r → min_moves rooks2 = ok r2 → r.val = r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (rooks rooks2 : Slice (alloc.vec.Vec I64))
        (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
        (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
        (hbounds : ∀ i : Fin rooks.val.length,
          0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
          0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
        (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
          (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j))
        (p : Fin rooks.val.length → Fin rooks.val.length) (hp : IsPerm p)
        (hrooks2 : rooks2.val = permuteList rooks.val p), ∀ r r2 : I64, min_moves rooks = ok r → min_moves rooks2 = ok r2 → r.val = r2.val) := by
    sorry

  /-- Whenever min_moves(rooks) returns r, let xs be the nondecreasing sort of the list [rooks[i][0] | 0 <= i < n] and ys be the nondecreasing sort of the list [rooks[i][1] | 0 <= i < n]. Then r = sum over i = 0,...,n-1 of (|xs[i] - i| + |ys[i] - i|).
    Preconditions: Let n = len(rooks). The input satisfies: 1 <= n <= 500; for every i with 0 <= i < n, len(rooks[i]) = 2, 0 <= rooks[i][0] <= n-1, and 0 <= rooks[i][1] <= n-1; and for every i, j with 0 <= i < j < n, (rooks[i][0], rooks[i][1]) != (rooks[j][0], rooks[j][1]). -/
  theorem spec_9 (rooks : Slice (alloc.vec.Vec I64))
      (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
      (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
      (hbounds : ∀ i : Fin rooks.val.length,
        0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
        0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
      (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
        (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)) :
      ∀ r : I64, min_moves rooks = ok r →
        r.val = ∑ i : Fin rooks.val.length,
          (|sortedAt (xList rooks) i - ((i : ℕ) : ℤ)| +
            |sortedAt (yList rooks) i - ((i : ℕ) : ℤ)|) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (rooks : Slice (alloc.vec.Vec I64))
        (hne : 1 ≤ rooks.val.length) (hle : rooks.val.length ≤ 500)
        (hlen : ∀ i : Fin rooks.val.length, (rooks.val.get i).slice.val.length = 2)
        (hbounds : ∀ i : Fin rooks.val.length,
          0 ≤ xAt rooks i ∧ xAt rooks i ≤ (rooks.val.length : ℤ) - 1 ∧
          0 ≤ yAt rooks i ∧ yAt rooks i ≤ (rooks.val.length : ℤ) - 1)
        (hdistinct : ∀ i j : Fin rooks.val.length, i < j →
          (xAt rooks i, yAt rooks i) ≠ (xAt rooks j, yAt rooks j)), ∀ r : I64, min_moves rooks = ok r →
          r.val = ∑ i : Fin rooks.val.length,
            (|sortedAt (xList rooks) i - ((i : ℕ) : ℤ)| +
              |sortedAt (yList rooks) i - ((i : ℕ) : ℤ)|)) := by
    sorry

  end AegisSpec.MinMoves
