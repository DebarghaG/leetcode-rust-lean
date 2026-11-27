import Aegis.MinDistance.Code.Funs

/-!
# Specifications of `Aegis.MinDistance.min_distance`

LeetCode problem `squirrel-simulation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped BigOperators

namespace AegisSpec.MinDistance

def coords (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

def nutCoords (nuts : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
  nuts.val.map (fun v => v.val.map (fun x => x.val))

def rowOf (p : List ℤ) : ℤ := p.getD 0 0

def colOf (p : List ℤ) : ℤ := p.getD 1 0

def mdist (p q : List ℤ) : ℤ := |rowOf p - rowOf q| + |colOf p - colOf q|

def nutAt (nuts : Slice (alloc.vec.Vec I64)) (i : ℕ) : List ℤ := (nutCoords nuts).getD i []

def D (tree : Slice I64) (nuts : Slice (alloc.vec.Vec I64)) (i : ℕ) : ℤ :=
  mdist (coords tree) (nutAt nuts i)

def S (squirrel : Slice I64) (nuts : Slice (alloc.vec.Vec I64)) (i : ℕ) : ℤ :=
  mdist (coords squirrel) (nutAt nuts i)

def idx (nuts : Slice (alloc.vec.Vec I64)) : Finset ℕ := Finset.range nuts.val.length

theorem idx_nonempty_of_pos {n : ℕ} (h : 0 < n) : (Finset.range n).Nonempty :=
  Finset.nonempty_range_iff.mpr (Nat.pos_iff_ne_zero.mp h)

noncomputable def totalD (tree : Slice I64) (nuts : Slice (alloc.vec.Vec I64)) : ℤ :=
  Finset.sum (idx nuts) (fun i => D tree nuts i)

noncomputable def minSD (tree squirrel : Slice I64) (nuts : Slice (alloc.vec.Vec I64)) : ℤ :=
  if h : 0 < nuts.val.length then
    (idx nuts).inf' (idx_nonempty_of_pos h) (fun i => S squirrel nuts i - D tree nuts i)
  else 0

noncomputable def maxD (tree : Slice I64) (nuts : Slice (alloc.vec.Vec I64)) : ℤ :=
  if h : 0 < nuts.val.length then (idx nuts).sup' (idx_nonempty_of_pos h) (fun i => D tree nuts i)
  else 0

def PtInGarden (height width : ℤ) (p : List ℤ) : Prop :=
  p.length = 2 ∧ 0 ≤ rowOf p ∧ rowOf p ≤ height ∧ 0 ≤ colOf p ∧ colOf p ≤ width

def GardenIn (height width : ℤ) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) : Prop :=
  PtInGarden height width (coords tree) ∧ PtInGarden height width (coords squirrel) ∧
  ∀ p ∈ nutCoords nuts, PtInGarden height width p

def Pre (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) : Prop :=
  1 ≤ height.val ∧ height.val ≤ 100 ∧ 1 ≤ width.val ∧ width.val ≤ 100 ∧
  tree.val.length = 2 ∧ squirrel.val.length = 2 ∧
  1 ≤ nuts.val.length ∧ nuts.val.length ≤ 5000 ∧
  GardenIn height.val width.val tree squirrel nuts

def shiftPt (dr dc : ℤ) (p : List ℤ) : List ℤ := [rowOf p + dr, colOf p + dc]

def shiftCoord (dr dc : ℤ) (s : Slice I64) : List ℤ := shiftPt dr dc (coords s)

def shiftNutCoords (dr dc : ℤ) (nuts : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
  (nutCoords nuts).map (shiftPt dr dc)

def transposePt (p : List ℤ) : List ℤ := [colOf p, rowOf p]

def transposeCoord (s : Slice I64) : List ℤ := transposePt (coords s)

def transposeNutCoords (nuts : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
  (nutCoords nuts).map transposePt

/-- Let n = len(nuts). For 0 <= i < n define D_i = |tree[0] - nuts[i][0]| + |tree[1] - nuts[i][1]| and S_i = |squirrel[0] - nuts[i][0]| + |squirrel[1] - nuts[i][1]|. Whenever min_distance returns a result r, r = 2 * (Σ_{i=0}^{n-1} D_i) + min_{0 <= i < n} (S_i - D_i).
  Preconditions: height and width are integers with 1 <= height <= 100 and 1 <= width <= 100; len(tree)=2 and len(squirrel)=2; n=len(nuts) with 1 <= n <= 5000; len(nuts[i])=2 for every 0 <= i < n; every row coordinate in tree, squirrel, or nuts satisfies 0 <= row <= height; every column coordinate satisfies 0 <= col <= width. -/
theorem spec_1 (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts) :
    ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      r.val = 2 * totalD tree nuts + minSD tree squirrel nuts := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts), ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      r.val = 2 * totalD tree nuts + minSD tree squirrel nuts) := by
  sorry

/-- For every input satisfying the preconditions, min_distance returns a result r (Result.ok r); it does not fail by overflow, out-of-bounds indexing, empty minimum, or panic.
  Preconditions: Same as spec_1: 1 <= height,width <= 100; len(tree)=2; len(squirrel)=2; n=len(nuts) with 1 <= n <= 5000; each nuts[i] has length 2; all positions lie in the garden. -/
theorem spec_2 (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts) :
    ∃ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts), ∃ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r) := by
  sorry

/-- Whenever min_distance returns a result r, r >= 0.
  Preconditions: Same as spec_1. -/
theorem spec_3 (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts) :
    ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts), ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      0 ≤ r.val) := by
  sorry

/-- Let D_i = |tree[0] - nuts[i][0]| + |tree[1] - nuts[i][1]| for 0 <= i < n. Whenever min_distance returns a result r, r <= 2 * (Σ_{i=0}^{n-1} D_i) + (|squirrel[0] - tree[0]| + |squirrel[1] - tree[1]|).
  Preconditions: Same as spec_1. -/
theorem spec_4 (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts) :
    ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      r.val ≤ 2 * totalD tree nuts + mdist (coords squirrel) (coords tree) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts), ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      r.val ≤ 2 * totalD tree nuts + mdist (coords squirrel) (coords tree)) := by
  sorry

/-- Let D_i = |tree[0] - nuts[i][0]| + |tree[1] - nuts[i][1]| for 0 <= i < n. Whenever min_distance returns a result r, r >= 2 * (Σ_{i=0}^{n-1} D_i) - max_{0 <= i < n} D_i.
  Preconditions: Same as spec_1. -/
theorem spec_5 (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts) :
    ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      2 * totalD tree nuts - maxD tree nuts ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts), ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      2 * totalD tree nuts - maxD tree nuts ≤ r.val) := by
  sorry

/-- Whenever min_distance returns a result r, r and (squirrel[0] + squirrel[1] - tree[0] - tree[1]) have the same parity.
  Preconditions: Same as spec_1. -/
theorem spec_6 (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts) :
    ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      ∃ k : ℤ, r.val - (rowOf (coords squirrel) + colOf (coords squirrel) -
        (rowOf (coords tree) + colOf (coords tree))) = 2 * k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts), ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      ∃ k : ℤ, r.val - (rowOf (coords squirrel) + colOf (coords squirrel) -
        (rowOf (coords tree) + colOf (coords tree))) = 2 * k) := by
  sorry

/-- Let π be any bijection of {0,...,n-1}, and let nutsπ be the slice with nutsπ[i] = nuts[π(i)]. Whenever a call on (height,width,tree,squirrel,nuts) returns r and a call on (height,width,tree,squirrel,nutsπ) returns r', we have r = r'.
  Preconditions: Same as spec_1. -/
theorem spec_7 (height width : I64) (tree squirrel : Slice I64)
    (nuts nutsPi : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts)
    (π : Equiv.Perm (Fin nuts.val.length))
    (hπ : nutsPi.val = List.ofFn (fun i : Fin nuts.val.length => nuts.val.get (π i))) :
    ∀ r r' : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      Aegis.MinDistance.min_distance height width tree squirrel nutsPi = ok r' → r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (height width : I64) (tree squirrel : Slice I64)
    (nuts nutsPi : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts)
    (π : Equiv.Perm (Fin nuts.val.length))
    (hπ : nutsPi.val = List.ofFn (fun i : Fin nuts.val.length => nuts.val.get (π i))), ∀ r r' : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      Aegis.MinDistance.min_distance height width tree squirrel nutsPi = ok r' → r.val = r'.val) := by
  sorry

/-- For any integers dr and dc such that every shifted row coordinate tree[0]+dr, squirrel[0]+dr, nuts[i][0]+dr is still in [0,height] and every shifted column coordinate tree[1]+dc, squirrel[1]+dc, nuts[i][1]+dc is still in [0,width], let tree', squirrel', and nuts' be the shifted positions. Whenever the original call returns r and the shifted call with the same height and width returns r', we have r = r'.
  Preconditions: Same as corrected S1. -/
theorem spec_8 (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts)
    (dr dc : ℤ) (tree' squirrel' : Slice I64) (nuts' : Slice (alloc.vec.Vec I64))
    (htree : coords tree' = shiftCoord dr dc tree)
    (hsquirrel : coords squirrel' = shiftCoord dr dc squirrel)
    (hnuts : nutCoords nuts' = shiftNutCoords dr dc nuts)
    (hgarden : GardenIn height.val width.val tree' squirrel' nuts') :
    ∀ r r' : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      Aegis.MinDistance.min_distance height width tree' squirrel' nuts' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts)
    (dr dc : ℤ) (tree' squirrel' : Slice I64) (nuts' : Slice (alloc.vec.Vec I64))
    (htree : coords tree' = shiftCoord dr dc tree)
    (hsquirrel : coords squirrel' = shiftCoord dr dc squirrel)
    (hnuts : nutCoords nuts' = shiftNutCoords dr dc nuts)
    (hgarden : GardenIn height.val width.val tree' squirrel' nuts'), ∀ r r' : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      Aegis.MinDistance.min_distance height width tree' squirrel' nuts' = ok r' →
      r.val = r'.val) := by
  sorry

/-- Let P^T = [P[1],P[0]] for a two-element position P. Whenever min_distance(height,width,tree,squirrel,nuts) returns r and min_distance(width,height, tree^T, squirrel^T, nuts^T) returns r', where nuts^T[i] = (nuts[i])^T, we have r = r'.
  Preconditions: Same as spec_1. -/
theorem spec_9 (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts)
    (treeT squirrelT : Slice I64) (nutsT : Slice (alloc.vec.Vec I64))
    (htree : coords treeT = transposeCoord tree)
    (hsquirrel : coords squirrelT = transposeCoord squirrel)
    (hnuts : nutCoords nutsT = transposeNutCoords nuts) :
    ∀ r r' : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      Aegis.MinDistance.min_distance width height treeT squirrelT nutsT = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts)
    (treeT squirrelT : Slice I64) (nutsT : Slice (alloc.vec.Vec I64))
    (htree : coords treeT = transposeCoord tree)
    (hsquirrel : coords squirrelT = transposeCoord squirrel)
    (hnuts : nutCoords nutsT = transposeNutCoords nuts), ∀ r r' : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      Aegis.MinDistance.min_distance width height treeT squirrelT nutsT = ok r' →
      r.val = r'.val) := by
  sorry

/-- Let D_i = |tree[0] - nuts[i][0]| + |tree[1] - nuts[i][1]| and S_i = |squirrel[0] - nuts[i][0]| + |squirrel[1] - nuts[i][1]|. Whenever min_distance returns a result r, there exists an index j with 0 <= j < n such that r = S_j + D_j + Σ_{i=0, i≠j}^{n-1} 2*D_i.
  Preconditions: Same as spec_1. -/
theorem spec_10 (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts) :
    ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      ∃ j : ℕ, j < nuts.val.length ∧
        r.val = S squirrel nuts j + D tree nuts j +
          Finset.sum ((idx nuts).erase j) (fun i => 2 * D tree nuts i) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts), ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      ∃ j : ℕ, j < nuts.val.length ∧
        r.val = S squirrel nuts j + D tree nuts j +
          Finset.sum ((idx nuts).erase j) (fun i => 2 * D tree nuts i)) := by
  sorry

/-- Let D_i = |tree[0] - nuts[i][0]| + |tree[1] - nuts[i][1]| and S_i = |squirrel[0] - nuts[i][0]| + |squirrel[1] - nuts[i][1]|. Whenever min_distance returns a result r, for every index j with 0 <= j < n, r <= S_j + D_j + Σ_{i=0, i≠j}^{n-1} 2*D_i.
  Preconditions: Same as spec_1. -/
theorem spec_11 (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts) :
    ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      ∀ j : ℕ, j < nuts.val.length →
        r.val ≤ S squirrel nuts j + D tree nuts j +
          Finset.sum ((idx nuts).erase j) (fun i => 2 * D tree nuts i) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (height width : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts), ∀ r : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      ∀ j : ℕ, j < nuts.val.length →
        r.val ≤ S squirrel nuts j + D tree nuts j +
          Finset.sum ((idx nuts).erase j) (fun i => 2 * D tree nuts i)) := by
  sorry

/-- Let height' and width' be any integers with 1 <= height' <= 100 and 1 <= width' <= 100 such that all positions in tree, squirrel, and nuts also satisfy 0 <= row <= height' and 0 <= col <= width'. Whenever min_distance(height,width,tree,squirrel,nuts) returns r and min_distance(height',width',tree,squirrel,nuts) returns r', we have r = r'.
  Preconditions: Same as corrected S1. -/
theorem spec_12 (height width height' width' : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts)
    (hheight' : 1 ≤ height'.val ∧ height'.val ≤ 100)
    (hwidth' : 1 ≤ width'.val ∧ width'.val ≤ 100)
    (hgarden : GardenIn height'.val width'.val tree squirrel nuts) :
    ∀ r r' : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      Aegis.MinDistance.min_distance height' width' tree squirrel nuts = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (height width height' width' : I64) (tree squirrel : Slice I64)
    (nuts : Slice (alloc.vec.Vec I64)) (hpre : Pre height width tree squirrel nuts)
    (hheight' : 1 ≤ height'.val ∧ height'.val ≤ 100)
    (hwidth' : 1 ≤ width'.val ∧ width'.val ≤ 100)
    (hgarden : GardenIn height'.val width'.val tree squirrel nuts), ∀ r r' : I64, Aegis.MinDistance.min_distance height width tree squirrel nuts = ok r →
      Aegis.MinDistance.min_distance height' width' tree squirrel nuts = ok r' →
      r.val = r'.val) := by
  sorry

end AegisSpec.MinDistance
