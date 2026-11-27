import Aegis.MaximumWhiteTiles.Code.Funs

/-!
# Specifications of `Aegis.MaximumWhiteTiles.maximum_white_tiles`

LeetCode problem `maximum-white-tiles-covered-by-a-carpet`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumWhiteTiles

  namespace AegisSpec.MaximumWhiteTiles

  def tileList (tiles : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    tiles.val.map (fun v => v.val.map (fun x => x.val))

  def tileAt (tiles : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
    (tileList tiles).getD i []

  def tileLo (tiles : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (tileAt tiles i).headD 0

  def tileHi (tiles : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (tileAt tiles i).getD 1 0

  def whiteSet (tiles : Slice (alloc.vec.Vec Std.I64)) : Set ℤ :=
    {x : ℤ | ∃ i, i < tiles.val.length ∧ tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i}

  noncomputable def countCovered (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : ℤ) (s : ℤ) : ℕ :=
    Set.ncard {x : ℤ | x ∈ whiteSet tiles ∧ s ≤ x ∧ x ≤ s + carpetLen - 1}

  def IsBestCoverage (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen r : ℤ) : Prop :=
    (∀ s : ℤ, (countCovered tiles carpetLen s : ℤ) ≤ r) ∧
      ∃ s : ℤ, (countCovered tiles carpetLen s : ℤ) = r

  def totalWhite (tiles : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ∑ i ∈ Finset.range tiles.val.length, (tileHi tiles i - tileLo tiles i + 1)

  def maxTileLen (tiles : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((List.range tiles.val.length).map
      (fun i => tileHi tiles i - tileLo tiles i + 1)).max?.getD 0

  def minLo (tiles : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((List.range tiles.val.length).map (fun i => tileLo tiles i)).min?.getD 0

  def maxHi (tiles : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((List.range tiles.val.length).map (fun i => tileHi tiles i)).max?.getD 0

  def maxClampedLen (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : ℤ) : ℤ :=
    ((List.range tiles.val.length).map
      (fun i => min carpetLen (tileHi tiles i - tileLo tiles i + 1))).max?.getD 0

  /-- Whenever the function returns a result r (Result.ok r), r is the maximum, over all integers s, of C(s), where C(s) is the number of integers x such that both (i) there exists an index i with 0 <= i < len(tiles) and tiles[i][0] <= x <= tiles[i][1], and (ii) s <= x <= s + carpetLen - 1. In words, r is the largest possible number of white tiles covered by placing a carpet of length carpetLen on the consecutive integer positions s, s+1, ..., s+carpetLen-1, for any integer start s.
    Preconditions: 1 <= len(tiles) <= 50000; 1 <= carpetLen <= 1000000000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; and the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]. -/
  theorem spec_1 (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
      (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r) :
      IsBestCoverage tiles carpetLen.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
        (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r), IsBestCoverage tiles carpetLen.val r.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (Result.ok r); it does not fail, panic, return Result.err, or overflow 64-bit arithmetic.
    Preconditions: 1 <= len(tiles) <= 50000; 1 <= carpetLen <= 1000000000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; and the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]. -/
  theorem spec_2 (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j)) :
      ∃ r : Std.I64, maximum_white_tiles tiles carpetLen = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j)), ∃ r : Std.I64, maximum_white_tiles tiles carpetLen = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= min(carpetLen, T), where T is the total number of white tiles: T = |{x in Z : there exists i with 0 <= i < len(tiles) and tiles[i][0] <= x <= tiles[i][1]}| = sum_{i=0}^{len(tiles)-1} (tiles[i][1] - tiles[i][0] + 1) (the sum formula uses pairwise non-overlap).
    Preconditions: 1 <= len(tiles) <= 50000; 1 <= carpetLen <= 1000000000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; and the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]. -/
  theorem spec_3 (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
      (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r) :
      r.val ≤ min carpetLen.val (totalWhite tiles) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
        (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r), r.val ≤ min carpetLen.val (totalWhite tiles)) := by
    sorry

  /-- Whenever the function returns a result r, r >= min(carpetLen, M), where M = max_{0 <= i < len(tiles)} (tiles[i][1] - tiles[i][0] + 1) is the length of the longest white interval.
    Preconditions: 1 <= len(tiles) <= 50000; 1 <= carpetLen <= 1000000000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; and the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]. -/
  theorem spec_4 (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
      (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r) :
      min carpetLen.val (maxTileLen tiles) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
        (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r), min carpetLen.val (maxTileLen tiles) ≤ r.val) := by
    sorry

  /-- Let minL = min_{0 <= i < len(tiles)} tiles[i][0], maxR = max_{0 <= i < len(tiles)} tiles[i][1], and T = sum_{i=0}^{len(tiles)-1} (tiles[i][1] - tiles[i][0] + 1). Whenever the function returns a result r, r = T if and only if carpetLen >= maxR - minL + 1.
    Preconditions: 1 <= len(tiles) <= 50000; 1 <= carpetLen <= 1000000000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; and the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]. -/
  theorem spec_5 (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
      (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r) :
      r.val = totalWhite tiles ↔ maxHi tiles - minLo tiles + 1 ≤ carpetLen.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
        (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r), r.val = totalWhite tiles ↔ maxHi tiles - minLo tiles + 1 ≤ carpetLen.val) := by
    sorry

  /-- Let C(s) be defined as in spec_1: the number of white integers x with s <= x <= s + carpetLen - 1. Whenever the function returns a result r, there exists an index i with 0 <= i < len(tiles) such that C(tiles[i][0]) = r.
    Preconditions: 1 <= len(tiles) <= 50000; 1 <= carpetLen <= 1000000000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; and the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]. -/
  theorem spec_6 (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
      (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r) :
      ∃ i, i < tiles.val.length ∧ (countCovered tiles carpetLen.val (tileLo tiles i) : ℤ) = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
        (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r), ∃ i, i < tiles.val.length ∧ (countCovered tiles carpetLen.val (tileLo tiles i) : ℤ) = r.val) := by
    sorry

  /-- Let pi be any permutation of {0,1,...,len(tiles)-1}, and let tiles' be the slice of length len(tiles) with tiles'[i] = tiles[pi(i)] for every 0 <= i < len(tiles). Whenever both calls maximum_white_tiles(tiles, carpetLen) and maximum_white_tiles(tiles', carpetLen) return results r and r' respectively, r = r'.
    Preconditions: 1 <= len(tiles) <= 50000; 1 <= carpetLen <= 1000000000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; and the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]. -/
  theorem spec_7 (tiles tiles' : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
      (hperm : (tileList tiles').Perm (tileList tiles))
      (r r' : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r)
      (hr' : maximum_white_tiles tiles' carpetLen = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (tiles tiles' : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
        (hperm : (tileList tiles').Perm (tileList tiles))
        (r r' : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r)
        (hr' : maximum_white_tiles tiles' carpetLen = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever both calls maximum_white_tiles(tiles, carpetLen) and maximum_white_tiles(tiles', carpetLen) return results r and r' respectively, r = r'.
    Preconditions: 1 <= len(tiles) <= 50000; 1 <= carpetLen <= 1000000000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]; let d be an integer such that 1 <= tiles[i][0] + d and tiles[i][1] + d <= 1000000000 for every 0 <= i < len(tiles), and define tiles'[i] = [tiles[i][0] + d, tiles[i][1] + d]. -/
  theorem spec_8 (tiles tiles' : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
      (d : ℤ)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
      (hdlo : ∀ i, i < tiles.val.length → 1 ≤ tileLo tiles i + d)
      (hdhi : ∀ i, i < tiles.val.length → tileHi tiles i + d ≤ 1000000000)
      (htrans : tileList tiles' =
        (tileList tiles).map (fun t => t.map (fun x => x + d)))
      (r r' : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r)
      (hr' : maximum_white_tiles tiles' carpetLen = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (tiles tiles' : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
        (d : ℤ)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
        (hdlo : ∀ i, i < tiles.val.length → 1 ≤ tileLo tiles i + d)
        (hdhi : ∀ i, i < tiles.val.length → tileHi tiles i + d ≤ 1000000000)
        (htrans : tileList tiles' =
          (tileList tiles).map (fun t => t.map (fun x => x + d)))
        (r r' : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r)
        (hr' : maximum_white_tiles tiles' carpetLen = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever maximum_white_tiles(tiles, L1) returns r1 and maximum_white_tiles(tiles, L2) returns r2, we have r1 <= r2.
    Preconditions: 1 <= len(tiles) <= 50000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]; let L1 and L2 be integers with 1 <= L1 <= L2 <= 1000000000. -/
  theorem spec_9 (tiles : Slice (alloc.vec.Vec Std.I64)) (L1 L2 : Std.I64)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
      (hL1 : 1 ≤ L1.val) (hL12 : L1.val ≤ L2.val) (hL2 : L2.val ≤ 1000000000)
      (r1 r2 : Std.I64) (hr1 : maximum_white_tiles tiles L1 = ok r1)
      (hr2 : maximum_white_tiles tiles L2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (tiles : Slice (alloc.vec.Vec Std.I64)) (L1 L2 : Std.I64)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
        (hL1 : 1 ≤ L1.val) (hL12 : L1.val ≤ L2.val) (hL2 : L2.val ≤ 1000000000)
        (r1 r2 : Std.I64) (hr1 : maximum_white_tiles tiles L1 = ok r1)
        (hr2 : maximum_white_tiles tiles L2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Whenever maximum_white_tiles(tiles, carpetLen) returns r and maximum_white_tiles(tiles', carpetLen) returns r', we have r <= r'.
    Preconditions: 1 <= len(tiles) <= 50000; 1 <= carpetLen <= 1000000000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]; len(tiles) <= 49999; let [l,r] be an integer interval with 1 <= l <= r <= 1000000000 such that for every i with 0 <= i < len(tiles), [l,r] and [tiles[i][0], tiles[i][1]] have no integer in common; let tiles' be any slice obtained by appending [l,r] to tiles (so len(tiles') = len(tiles)+1 and the first len(tiles) entries are those of tiles). -/
  theorem spec_10 (tiles tiles' : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
      (l rint : ℤ)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
      (hlen : tiles.val.length ≤ 49999)
      (hl1 : 1 ≤ l) (hlr : l ≤ rint) (hr2 : rint ≤ 1000000000)
      (hdisj : ∀ i, i < tiles.val.length → ¬ (tileLo tiles i ≤ rint ∧ l ≤ tileHi tiles i))
      (happ : tileList tiles' = tileList tiles ++ [[l, rint]])
      (r r' : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r)
      (hr' : maximum_white_tiles tiles' carpetLen = ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (tiles tiles' : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
        (l rint : ℤ)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
        (hlen : tiles.val.length ≤ 49999)
        (hl1 : 1 ≤ l) (hlr : l ≤ rint) (hr2 : rint ≤ 1000000000)
        (hdisj : ∀ i, i < tiles.val.length → ¬ (tileLo tiles i ≤ rint ∧ l ≤ tileHi tiles i))
        (happ : tileList tiles' = tileList tiles ++ [[l, rint]])
        (r r' : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r)
        (hr' : maximum_white_tiles tiles' carpetLen = ok r'), r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function returns a result r, r = max_{0 <= i < len(tiles)} min(carpetLen, tiles[i][1] - tiles[i][0] + 1).
    Preconditions: 1 <= len(tiles) <= 50000; 1 <= carpetLen <= 1000000000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]; additionally, for every i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, and tiles[i][0] < tiles[j][0], we have tiles[j][0] - tiles[i][1] >= carpetLen. -/
  theorem spec_11 (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
      (hgap : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        tileLo tiles i < tileLo tiles j →
          carpetLen.val ≤ tileLo tiles j - tileHi tiles i)
      (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r) :
      r.val = maxClampedLen tiles carpetLen.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
        (hgap : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          tileLo tiles i < tileLo tiles j →
            carpetLen.val ≤ tileLo tiles j - tileHi tiles i)
        (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r), r.val = maxClampedLen tiles carpetLen.val) := by
    sorry

  /-- Whenever the function returns a result r, r = min(carpetLen, B - A + 1), where A = min_{0 <= i < len(tiles)} tiles[i][0] and B = max_{0 <= i < len(tiles)} tiles[i][1].
    Preconditions: 1 <= len(tiles) <= 50000; 1 <= carpetLen <= 1000000000; for every i with 0 <= i < len(tiles), len(tiles[i]) = 2 and 1 <= tiles[i][0] <= tiles[i][1] <= 1000000000; the intervals are pairwise non-overlapping: for all i,j with 0 <= i < len(tiles), 0 <= j < len(tiles), i != j, there is no integer x with tiles[i][0] <= x <= tiles[i][1] and tiles[j][0] <= x <= tiles[j][1]; and the union W = {x in Z : there exists i with 0 <= i < len(tiles) and tiles[i][0] <= x <= tiles[i][1]} is contiguous, i.e. there exist integers A <= B with W = {x in Z : A <= x <= B}. -/
  theorem spec_12 (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
      (A B : ℤ)
      (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
      (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
      (hshape : ∀ i, i < tiles.val.length →
        (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
          tileHi tiles i ≤ 1000000000)
      (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
        ∀ x : ℤ,
          ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
      (hA : A = minLo tiles) (hB : B = maxHi tiles) (hAB : A ≤ B)
      (hcontig : ∀ x : ℤ, x ∈ whiteSet tiles ↔ A ≤ x ∧ x ≤ B)
      (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r) :
      r.val = min carpetLen.val (B - A + 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (tiles : Slice (alloc.vec.Vec Std.I64)) (carpetLen : Std.I64)
        (A B : ℤ)
        (hne : 1 ≤ tiles.val.length) (hle : tiles.val.length ≤ 50000)
        (hc1 : 1 ≤ carpetLen.val) (hc2 : carpetLen.val ≤ 1000000000)
        (hshape : ∀ i, i < tiles.val.length →
          (tileAt tiles i).length = 2 ∧ 1 ≤ tileLo tiles i ∧ tileLo tiles i ≤ tileHi tiles i ∧
            tileHi tiles i ≤ 1000000000)
        (hsep : ∀ i j, i < tiles.val.length → j < tiles.val.length → i ≠ j →
          ∀ x : ℤ,
            ¬ (tileLo tiles i ≤ x ∧ x ≤ tileHi tiles i ∧ tileLo tiles j ≤ x ∧ x ≤ tileHi tiles j))
        (hA : A = minLo tiles) (hB : B = maxHi tiles) (hAB : A ≤ B)
        (hcontig : ∀ x : ℤ, x ∈ whiteSet tiles ↔ A ≤ x ∧ x ≤ B)
        (r : Std.I64) (hr : maximum_white_tiles tiles carpetLen = ok r), r.val = min carpetLen.val (B - A + 1)) := by
    sorry

  end AegisSpec.MaximumWhiteTiles
