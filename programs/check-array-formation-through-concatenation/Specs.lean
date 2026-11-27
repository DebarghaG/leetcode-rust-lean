import Aegis.CanFormArray.Code.Funs

/-!
# Specifications of `Aegis.CanFormArray.can_form_array`

LeetCode problem `check-array-formation-through-concatenation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanFormArray

  def arrVals (arr : Slice Std.I64) : List Int := arr.val.map (fun x => x.val)

  def piecesVals (pieces : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    pieces.val.map (fun v => v.val.map (fun x => x.val))

  def numPieces (pieces : Slice (alloc.vec.Vec Std.I64)) : Nat := (piecesVals pieces).length

  def arrLen (arr : Slice Std.I64) : Nat := (arrVals arr).length

  def piece (pieces : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
    (piecesVals pieces).getD i []

  def pieceLen (pieces : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
    (piece pieces i).length

  def pieceLens (pieces : Slice (alloc.vec.Vec Std.I64)) : List Nat :=
    (piecesVals pieces).map List.length

  def flattenedPieces (pieces : Slice (alloc.vec.Vec Std.I64)) : List Int :=
    (piecesVals pieces).flatten

  def countOf (l : List Int) (x : Int) : Nat :=
    (l.filter (fun y => decide (y = x))).length

  def countInPieces (pieces : Slice (alloc.vec.Vec Std.I64)) (x : Int) : Nat :=
    ((piecesVals pieces).map (fun l => countOf l x)).sum

  def BlockMatches (arrv : List Int) (w : List Int) (s : Nat) : Prop :=
    ∀ (j : Nat) (hj : j < w.length), arrv[s + j]? = some (w.get ⟨j, hj⟩)

  def DisjointIntervals (s₁ l₁ s₂ l₂ : Nat) : Prop :=
    s₁ + l₁ ≤ s₂ ∨ s₂ + l₂ ≤ s₁

  def pre (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ numPieces pieces ∧
    numPieces pieces ≤ arrLen arr ∧
    arrLen arr ≤ 100 ∧
    (∀ i, i < numPieces pieces → 1 ≤ pieceLen pieces i ∧ pieceLen pieces i ≤ arrLen arr) ∧
    (pieceLens pieces).sum = arrLen arr ∧
    (∀ (k : Nat) (hk : k < arrLen arr),
      1 ≤ (arrVals arr).get ⟨k, hk⟩ ∧ (arrVals arr).get ⟨k, hk⟩ ≤ 100) ∧
    (∀ (i : Nat), i < numPieces pieces → ∀ (j : Nat) (hj : j < pieceLen pieces i),
      1 ≤ (piece pieces i).get ⟨j, hj⟩ ∧ (piece pieces i).get ⟨j, hj⟩ ≤ 100) ∧
    (arrVals arr).Nodup ∧
    (flattenedPieces pieces).Nodup

  def IsPermutation (m : Nat) (p : List Nat) : Prop := p.Perm (List.range m)

  def prefixSum (pieces : Slice (alloc.vec.Vec Std.I64)) (p : List Nat) (t : Nat) : Nat :=
    ((p.take t).map (pieceLen pieces)).sum

  def ConcatenatesTo (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
      (p : List Nat) : Prop :=
    ∀ (t : Nat) (ht : t < p.length),
      BlockMatches (arrVals arr) (piece pieces (p.get ⟨t, ht⟩)) (prefixSum pieces p t)

  def WitnessOrder (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
      (p : List Nat) : Prop :=
    IsPermutation (numPieces pieces) p ∧ ConcatenatesTo arr pieces p

  /-- Under the preconditions, can_form_array arr pieces returns a result r (it does not fail). A permutation of pieces is a sequence p_0,...,p_{m-1} of indices with {p_0,...,p_{m-1}} = {0,...,m-1}. For such a sequence define s_0 = 0 and s_{t+1} = s_t + len(pieces[p_t]) for 0 <= t < m. Then r = true if and only if there exists a permutation p_0,...,p_{m-1} of pieces such that for every t with 0 <= t < m and every j with 0 <= j < len(pieces[p_t]), arr[s_t + j] = pieces[p_t][j]. Equivalently, r = true iff some ordering of all the pieces concatenates to exactly arr.
    Preconditions: Let m = len(pieces) and n = len(arr). Assume 1 <= m <= n <= 100; for every i with 0 <= i < m, 1 <= len(pieces[i]) <= n; sum_{i=0}^{m-1} len(pieces[i]) = n; for every k with 0 <= k < n, 1 <= arr[k] <= 100; for every i with 0 <= i < m and every j with 0 <= j < len(pieces[i]), 1 <= pieces[i][j] <= 100; the n values arr[0],...,arr[n-1] are pairwise distinct; and the flattened list of all pieces[i][j] has pairwise distinct values. -/
  theorem spec_1 (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
      (hpre : pre arr pieces) :
      ∃ r : Bool,
        Aegis.CanFormArray.can_form_array arr pieces = ok r ∧
          (r = true ↔ ∃ p : List Nat, WitnessOrder arr pieces p) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
        (hpre : pre arr pieces), ∃ r : Bool,
          Aegis.CanFormArray.can_form_array arr pieces = ok r ∧
            (r = true ↔ ∃ p : List Nat, WitnessOrder arr pieces p)) := by
    sorry

  /-- Under the preconditions, can_form_array arr pieces returns a result r; it does not fail (no panic, overflow, or out-of-bounds).
    Preconditions: Let m = len(pieces) and n = len(arr). Assume 1 <= m <= n <= 100; for every i with 0 <= i < m, 1 <= len(pieces[i]) <= n; sum_{i=0}^{m-1} len(pieces[i]) = n; for every k with 0 <= k < n, 1 <= arr[k] <= 100; for every i with 0 <= i < m and every j with 0 <= j < len(pieces[i]), 1 <= pieces[i][j] <= 100; the n values arr[0],...,arr[n-1] are pairwise distinct; and the flattened list of all pieces[i][j] has pairwise distinct values. -/
  theorem spec_2 (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
      (hpre : pre arr pieces) :
      ∃ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
        (hpre : pre arr pieces), ∃ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r) := by
    sorry

  /-- Whenever can_form_array arr pieces returns a result r with r = true, for every integer x the number of indices k with 0 <= k < n and arr[k] = x is equal to the sum over i = 0,...,m-1 of the number of indices j with 0 <= j < len(pieces[i]) and pieces[i][j] = x.
    Preconditions: Let m = len(pieces) and n = len(arr). Assume 1 <= m <= n <= 100; for every i with 0 <= i < m, 1 <= len(pieces[i]) <= n; sum_{i=0}^{m-1} len(pieces[i]) = n; for every k with 0 <= k < n, 1 <= arr[k] <= 100; for every i with 0 <= i < m and every j with 0 <= j < len(pieces[i]), 1 <= pieces[i][j] <= 100; the n values arr[0],...,arr[n-1] are pairwise distinct; and the flattened list of all pieces[i][j] has pairwise distinct values. -/
  theorem spec_3 (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
      (hpre : pre arr pieces) :
      ∀ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r → r = true →
        ∀ x : Int, countOf (arrVals arr) x = countInPieces pieces x := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
        (hpre : pre arr pieces), ∀ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r → r = true →
          ∀ x : Int, countOf (arrVals arr) x = countInPieces pieces x) := by
    sorry

  /-- Whenever can_form_array arr pieces returns a result r with r = true, for every i with 0 <= i < m there exists an integer s_i such that 0 <= s_i, s_i + len(pieces[i]) <= n, and for every j with 0 <= j < len(pieces[i]), arr[s_i + j] = pieces[i][j]. Thus each piece occurs as a contiguous block of arr, in the same internal order.
    Preconditions: Let m = len(pieces) and n = len(arr). Assume 1 <= m <= n <= 100; for every i with 0 <= i < m, 1 <= len(pieces[i]) <= n; sum_{i=0}^{m-1} len(pieces[i]) = n; for every k with 0 <= k < n, 1 <= arr[k] <= 100; for every i with 0 <= i < m and every j with 0 <= j < len(pieces[i]), 1 <= pieces[i][j] <= 100; the n values arr[0],...,arr[n-1] are pairwise distinct; and the flattened list of all pieces[i][j] has pairwise distinct values. -/
  theorem spec_4 (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
      (hpre : pre arr pieces) :
      ∀ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r → r = true →
        ∀ i, i < numPieces pieces →
          ∃ s : Nat, s + pieceLen pieces i ≤ arrLen arr ∧
            BlockMatches (arrVals arr) (piece pieces i) s := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
        (hpre : pre arr pieces), ∀ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r → r = true →
          ∀ i, i < numPieces pieces →
            ∃ s : Nat, s + pieceLen pieces i ≤ arrLen arr ∧
              BlockMatches (arrVals arr) (piece pieces i) s) := by
    sorry

  /-- Whenever can_form_array arr pieces returns a result r with r = true, there exist integers s_i, one for each i with 0 <= i < m, such that for every i and every j with 0 <= j < len(pieces[i]), arr[s_i + j] = pieces[i][j]; the intervals [s_i, s_i + len(pieces[i]) - 1] are pairwise disjoint; and their union is exactly {0,1,...,n-1}. The s_i are the start positions of the pieces in a witnessing concatenation.
    Preconditions: Let m = len(pieces) and n = len(arr). Assume 1 <= m <= n <= 100; for every i with 0 <= i < m, 1 <= len(pieces[i]) <= n; sum_{i=0}^{m-1} len(pieces[i]) = n; for every k with 0 <= k < n, 1 <= arr[k] <= 100; for every i with 0 <= i < m and every j with 0 <= j < len(pieces[i]), 1 <= pieces[i][j] <= 100; the n values arr[0],...,arr[n-1] are pairwise distinct; and the flattened list of all pieces[i][j] has pairwise distinct values. -/
  theorem spec_5 (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
      (hpre : pre arr pieces) :
      ∀ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r → r = true →
        ∃ s : Nat → Nat,
          (∀ i, i < numPieces pieces →
            BlockMatches (arrVals arr) (piece pieces i) (s i)) ∧
          (∀ i, i < numPieces pieces → ∀ j, j < numPieces pieces → i ≠ j →
            DisjointIntervals (s i) (pieceLen pieces i) (s j) (pieceLen pieces j)) ∧
          (∀ k, k < arrLen arr →
            ∃ i, i < numPieces pieces ∧ s i ≤ k ∧ k < s i + pieceLen pieces i) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
        (hpre : pre arr pieces), ∀ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r → r = true →
          ∃ s : Nat → Nat,
            (∀ i, i < numPieces pieces →
              BlockMatches (arrVals arr) (piece pieces i) (s i)) ∧
            (∀ i, i < numPieces pieces → ∀ j, j < numPieces pieces → i ≠ j →
              DisjointIntervals (s i) (pieceLen pieces i) (s j) (pieceLen pieces j)) ∧
            (∀ k, k < arrLen arr →
              ∃ i, i < numPieces pieces ∧ s i ≤ k ∧ k < s i + pieceLen pieces i)) := by
    sorry

  /-- Whenever can_form_array arr pieces returns a result r with r = true, there is exactly one index i with 0 <= i < m such that pieces[i][0] = arr[0], and there is exactly one index k with 0 <= k < m such that pieces[k][len(pieces[k])-1] = arr[n-1].
    Preconditions: Let m = len(pieces) and n = len(arr). Assume 1 <= m <= n <= 100; for every i with 0 <= i < m, 1 <= len(pieces[i]) <= n; sum_{i=0}^{m-1} len(pieces[i]) = n; for every k with 0 <= k < n, 1 <= arr[k] <= 100; for every i with 0 <= i < m and every j with 0 <= j < len(pieces[i]), 1 <= pieces[i][j] <= 100; the n values arr[0],...,arr[n-1] are pairwise distinct; and the flattened list of all pieces[i][j] has pairwise distinct values. -/
  theorem spec_6 (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
      (hpre : pre arr pieces) :
      ∀ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r → r = true →
        (∃! i : Nat, i < numPieces pieces ∧
            (piece pieces i)[0]? = (arrVals arr)[0]?) ∧
          (∃! k : Nat, k < numPieces pieces ∧
            (piece pieces k)[pieceLen pieces k - 1]? = (arrVals arr)[arrLen arr - 1]?) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
        (hpre : pre arr pieces), ∀ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r → r = true →
          (∃! i : Nat, i < numPieces pieces ∧
              (piece pieces i)[0]? = (arrVals arr)[0]?) ∧
            (∃! k : Nat, k < numPieces pieces ∧
              (piece pieces k)[pieceLen pieces k - 1]? = (arrVals arr)[arrLen arr - 1]?)) := by
    sorry

  /-- Whenever can_form_array arr pieces returns a result r with r = true, there is exactly one permutation p_0,...,p_{m-1} of {0,...,m-1} such that concatenating pieces[p_0],...,pieces[p_{m-1}] gives arr (using the concatenation condition from spec_1).
    Preconditions: Let m = len(pieces) and n = len(arr). Assume 1 <= m <= n <= 100; for every i with 0 <= i < m, 1 <= len(pieces[i]) <= n; sum_{i=0}^{m-1} len(pieces[i]) = n; for every k with 0 <= k < n, 1 <= arr[k] <= 100; for every i with 0 <= i < m and every j with 0 <= j < len(pieces[i]), 1 <= pieces[i][j] <= 100; the n values arr[0],...,arr[n-1] are pairwise distinct; and the flattened list of all pieces[i][j] has pairwise distinct values. -/
  theorem spec_7 (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
      (hpre : pre arr pieces) :
      ∀ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r → r = true →
        ∃! p : List Nat, WitnessOrder arr pieces p := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
        (hpre : pre arr pieces), ∀ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r → r = true →
          ∃! p : List Nat, WitnessOrder arr pieces p) := by
    sorry

  /-- Whenever can_form_array arr pieces returns a result r and can_form_array arr pieces' returns a result r', we have r = r'. In other words, the truth value depends on the multiset of pieces, not on the top-level order in which they are listed.
    Preconditions: Let m = len(pieces) and n = len(arr). Assume the preconditions on arr and pieces from spec_1. Let pieces' be any slice of vectors of length m for which there exists a bijection σ from {0,...,m-1} to itself such that pieces'[i] = pieces[σ(i)] for every i with 0 <= i < m (so pieces' is a top-level reordering of pieces and also satisfies the same constraints). -/
  theorem spec_8 (arr : Slice Std.I64) (pieces pieces' : Slice (alloc.vec.Vec Std.I64))
      (hpre : pre arr pieces)
      (hlen : numPieces pieces' = numPieces pieces)
      (hσ : ∃ σ : Nat → Nat,
        (∀ i, i < numPieces pieces → σ i < numPieces pieces) ∧
        (∀ i₁, i₁ < numPieces pieces → ∀ i₂, i₂ < numPieces pieces →
          σ i₁ = σ i₂ → i₁ = i₂) ∧
        (∀ j, j < numPieces pieces → ∃ i, i < numPieces pieces ∧ σ i = j) ∧
        (∀ i, i < numPieces pieces → piece pieces' i = piece pieces (σ i))) :
      ∀ r r' : Bool,
        Aegis.CanFormArray.can_form_array arr pieces = ok r →
        Aegis.CanFormArray.can_form_array arr pieces' = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64) (pieces pieces' : Slice (alloc.vec.Vec Std.I64))
        (hpre : pre arr pieces)
        (hlen : numPieces pieces' = numPieces pieces)
        (hσ : ∃ σ : Nat → Nat,
          (∀ i, i < numPieces pieces → σ i < numPieces pieces) ∧
          (∀ i₁, i₁ < numPieces pieces → ∀ i₂, i₂ < numPieces pieces →
            σ i₁ = σ i₂ → i₁ = i₂) ∧
          (∀ j, j < numPieces pieces → ∃ i, i < numPieces pieces ∧ σ i = j) ∧
          (∀ i, i < numPieces pieces → piece pieces' i = piece pieces (σ i))), ∀ r r' : Bool,
          Aegis.CanFormArray.can_form_array arr pieces = ok r →
          Aegis.CanFormArray.can_form_array arr pieces' = ok r' → r = r') := by
    sorry

  /-- Then can_form_array arr pieces returns a result r and r = true if and only if for every integer x, the number of indices k with 0 <= k < n and arr[k] = x equals the number of indices i with 0 <= i < m and pieces[i][0] = x.
    Preconditions: Let m = len(pieces) and n = len(arr). Assume 1 <= m <= n <= 100; for every i with 0 <= i < m, 1 <= len(pieces[i]) <= n; sum_{i=0}^{m-1} len(pieces[i]) = n; for every k with 0 <= k < n, 1 <= arr[k] <= 100; for every i with 0 <= i < m and every j with 0 <= j < len(pieces[i]), 1 <= pieces[i][j] <= 100; the n values arr[0],...,arr[n-1] are pairwise distinct; and the flattened list of all pieces[i][j] has pairwise distinct values. Assume in addition that len(pieces[i]) = 1 for every i with 0 <= i < m. -/
  theorem spec_9 (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
      (hpre : pre arr pieces)
      (hunit : ∀ i, i < numPieces pieces → pieceLen pieces i = 1) :
      ∃ r : Bool,
        Aegis.CanFormArray.can_form_array arr pieces = ok r ∧
          (r = true ↔ ∀ x : Int, countOf (arrVals arr) x = countInPieces pieces x) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
        (hpre : pre arr pieces)
        (hunit : ∀ i, i < numPieces pieces → pieceLen pieces i = 1), ∃ r : Bool,
          Aegis.CanFormArray.can_form_array arr pieces = ok r ∧
            (r = true ↔ ∀ x : Int, countOf (arrVals arr) x = countInPieces pieces x)) := by
    sorry

  /-- Then can_form_array arr pieces returns a result r with r = true.
    Preconditions: Let m = len(pieces) and n = len(arr). Assume 1 <= m <= n <= 100; for every i with 0 <= i < m, 1 <= len(pieces[i]) <= n; sum_{i=0}^{m-1} len(pieces[i]) = n; for every k with 0 <= k < n, 1 <= arr[k] <= 100; for every i with 0 <= i < m and every j with 0 <= j < len(pieces[i]), 1 <= pieces[i][j] <= 100; the n values arr[0],...,arr[n-1] are pairwise distinct; and the flattened list of all pieces[i][j] has pairwise distinct values. Suppose that the pieces in their given order already concatenate to arr: define t_0 = 0 and t_{i+1} = t_i + len(pieces[i]) for 0 <= i < m, and assume that for every i with 0 <= i < m and every j with 0 <= j < len(pieces[i]), arr[t_i + j] = pieces[i][j]. -/
  theorem spec_10 (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
      (hpre : pre arr pieces)
      (hconcat : ConcatenatesTo arr pieces (List.range (numPieces pieces))) :
      ∃ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r ∧ r = true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64) (pieces : Slice (alloc.vec.Vec Std.I64))
        (hpre : pre arr pieces)
        (hconcat : ConcatenatesTo arr pieces (List.range (numPieces pieces))), ∃ r : Bool, Aegis.CanFormArray.can_form_array arr pieces = ok r ∧ r = true) := by
    sorry

  end AegisSpec.CanFormArray
