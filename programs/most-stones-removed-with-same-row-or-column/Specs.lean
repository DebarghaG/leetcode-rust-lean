import Aegis.RemoveStones.Code.Funs

/-!
# Specifications of `Aegis.RemoveStones.remove_stones`

LeetCode problem `most-stones-removed-with-same-row-or-column`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RemoveStones

abbrev Stone := alloc.vec.Vec I64

abbrev Stones := Slice Stone

def len (stones : Stones) : Nat := stones.val.length

def coords (v : Stone) : List Int := v.val.map (fun x => x.val)

def fstCoord (v : Stone) : Int := (coords v).getD 0 0

def sndCoord (v : Stone) : Int := (coords v).getD 1 0

def stone (stones : Stones) (i : Nat) : List Int :=
  match stones.val[i]? with
  | some v => coords v
  | none => []

def row (stones : Stones) (i : Nat) : Int := (stone stones i).getD 0 0

def col (stones : Stones) (i : Nat) : Int := (stone stones i).getD 1 0

def ValidInput (stones : Stones) : Prop :=
  1 ≤ len stones ∧
  len stones ≤ 1000 ∧
  (∀ i, i < len stones → (stone stones i).length = 2) ∧
  (∀ i, i < len stones → 0 ≤ row stones i ∧ row stones i ≤ 10000) ∧
  (∀ i, i < len stones → 0 ≤ col stones i ∧ col stones i ≤ 10000) ∧
  (∀ i j, i < j → j < len stones →
    ¬ (row stones i = row stones j ∧ col stones i = col stones j))

abbrev Idx (stones : Stones) : Type := { i : Nat // i < len stones }

def Adj (stones : Stones) (i j : Idx stones) : Prop :=
  i ≠ j ∧ (row stones i.1 = row stones j.1 ∨ col stones i.1 = col stones j.1)

def Connected (stones : Stones) (i j : Idx stones) : Prop :=
  Relation.ReflTransGen (Adj stones) i j

theorem adj_symm {stones : Stones} {i j : Idx stones} (h : Adj stones i j) : Adj stones j i := by
  refine ⟨fun hji => h.1 hji.symm, ?_⟩
  rcases h.2 with hc | hc
  · exact Or.inl hc.symm
  · exact Or.inr hc.symm

theorem connected_refl (stones : Stones) (i : Idx stones) : Connected stones i i :=
  Relation.ReflTransGen.refl

theorem connected_symm {stones : Stones} {a b : Idx stones} (hab : Connected stones a b) :
    Connected stones b a := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (adj_symm hbc)) ih

theorem connected_trans {stones : Stones} {a b c : Idx stones}
    (hab : Connected stones a b) (hbc : Connected stones b c) : Connected stones a c :=
  Relation.ReflTransGen.trans hab hbc

theorem connected_equivalence (stones : Stones) : Equivalence (Connected stones) where
  refl := connected_refl stones
  symm := fun hab => connected_symm (stones := stones) hab
  trans := fun hab hbc => connected_trans (stones := stones) hab hbc

def componentsSetoid (stones : Stones) : Setoid (Idx stones) where
  r := Connected stones
  iseqv := connected_equivalence stones

noncomputable def ncomponents (stones : Stones) : Nat :=
  Nat.card (Quotient (componentsSetoid stones))

noncomputable def numRows (stones : Stones) : Nat :=
  Nat.card { x : Int // ∃ i, i < len stones ∧ row stones i = x }

noncomputable def numCols (stones : Stones) : Nat :=
  Nat.card { y : Int // ∃ i, i < len stones ∧ col stones i = y }

noncomputable def numIsolated (stones : Stones) : Nat :=
  Nat.card { i : Nat // i < len stones ∧
    ∀ j, j < len stones → j ≠ i →
      row stones j ≠ row stones i ∧ col stones j ≠ col stones i }

def Removable (stones : Stones) (removed : List Nat) (i : Nat) : Prop :=
  i < len stones ∧
  ∃ j, j < len stones ∧ j ≠ i ∧ j ∉ removed ∧
    (row stones i = row stones j ∨ col stones i = col stones j)

def LegalOrderFrom (stones : Stones) : List Nat → List Nat → Prop
  | _, [] => True
  | removed, i :: rest => Removable stones removed i ∧ LegalOrderFrom stones (i :: removed) rest

def LegalOrder (stones : Stones) (l : List Nat) : Prop := LegalOrderFrom stones [] l

def Chain (stones : Stones) : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
    (row stones a = row stones b ∨ col stones a = col stones b) ∧ Chain stones (b :: rest)

def Walk (stones : Stones) (i j : Nat) : Prop :=
  ∃ l : List Nat, l.head? = some i ∧ l.getLast? = some j ∧
    (∀ k ∈ l, k < len stones) ∧ Chain stones l

def mkSlice {α : Type} (l : List α) (h : l.length ≤ Usize.max) : Slice α :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

def mkStone (l : List I64) (h : l.length ≤ Usize.max) : Stone := ⟨mkSlice l h⟩

theorem slice_val_length {α : Type} (s : Slice α) : s.val.length = s.leng :=
  Aeneas.Data.ListN.ListN_length s.list

theorem stone_val_length (v : Stone) : v.val.length = v.slice.leng :=
  slice_val_length v.slice

def swapStone (v : Stone) : Stone :=
  mkStone v.val.reverse (by
    rw [List.length_reverse, stone_val_length]
    exact v.slice.bound)

def swapStones (stones : Stones) : Stones :=
  mkSlice (stones.val.map swapStone) (by
    rw [List.length_map, slice_val_length]
    exact stones.bound)

def permuteStones (stones : Stones) (p : Equiv.Perm (Fin (len stones))) : Stones :=
  mkSlice (List.ofFn (fun i : Fin (len stones) => stones.val[(p i).1])) (by
    simp only [len, List.length_ofFn, slice_val_length]
    exact stones.bound)

def permCoord (f : Equiv.Perm (Fin 10001)) (x : Int) : Fin 10001 :=
  f ⟨x.toNat % 10001, Nat.mod_lt _ (by norm_num)⟩

def finToI64 (k : Fin 10001) : I64 :=
  IScalar.ofInt (ty := IScalarTy.I64) (k.1 : Int) (by
    have hk : k.1 < 10001 := k.2
    simp [IScalar.cMin, IScalar.cMax, IScalar.rMin, IScalar.rMax, I64.rMin, I64.rMax]
    omega)

def transformStone (f g : Equiv.Perm (Fin 10001)) (v : Stone) : Stone :=
  mkStone (v.val.mapIdx (fun j x =>
      if j = 0 then finToI64 (permCoord f x.val)
      else if j = 1 then finToI64 (permCoord g x.val) else finToI64 ⟨0, by norm_num⟩)) (by
    rw [List.length_mapIdx, stone_val_length]
    exact v.slice.bound)

def transformStones (stones : Stones) (f g : Equiv.Perm (Fin 10001)) : Stones :=
  mkSlice (stones.val.map (transformStone f g)) (by
    rw [List.length_map, slice_val_length]
    exact stones.bound)

/-- Let n = len(stones). On the index set I = {i | 0 <= i < n}, define i ~ j to mean i != j and (stones[i][0] = stones[j][0] or stones[i][1] = stones[j][1]). Let connected be the reflexive-transitive closure of ~ on I, and let c be the number of equivalence classes of connected (equivalently, the number of connected components of the undirected graph on I whose edges are the pairs with i ~ j). The function returns a result r and r = n - c.
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_1 (stones : Stones) (h : ValidInput stones) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      r.val = (len stones : Int) - (ncomponents stones : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      r.val = (len stones : Int) - (ncomponents stones : Int)) := by
  sorry

/-- The function remove_stones returns a result r on every input satisfying the preconditions; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_2 (stones : Stones) (h : ValidInput stones) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= len(stones) - 1.
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_3 (stones : Stones) (h : ValidInput stones) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (len stones : Int) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (len stones : Int) - 1) := by
  sorry

/-- Let R be the number of distinct values in the set {stones[i][0] | 0 <= i < len(stones)}. The function returns a result r and r >= len(stones) - R.
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_4 (stones : Stones) (h : ValidInput stones) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      (len stones : Int) - (numRows stones : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      (len stones : Int) - (numRows stones : Int) ≤ r.val) := by
  sorry

/-- Let C be the number of distinct values in the set {stones[i][1] | 0 <= i < len(stones)}. The function returns a result r and r >= len(stones) - C.
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_5 (stones : Stones) (h : ValidInput stones) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      (len stones : Int) - (numCols stones : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      (len stones : Int) - (numCols stones : Int) ≤ r.val) := by
  sorry

/-- Let I be the number of indices i with 0 <= i < len(stones) such that for every j with 0 <= j < len(stones) and j != i, stones[j][0] != stones[i][0] and stones[j][1] != stones[i][1]. The function returns a result r and r <= len(stones) - I.
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_6 (stones : Stones) (h : ValidInput stones) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      r.val ≤ (len stones : Int) - (numIsolated stones : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      r.val ≤ (len stones : Int) - (numIsolated stones : Int)) := by
  sorry

/-- The function returns a result r. Let m be the nonnegative integer equal to r. There exists a sequence i_1, ..., i_m of distinct indices from {0, ..., len(stones)-1} (empty when m=0) such that for every t with 1 <= t <= m, putting S_t = {i_1, ..., i_{t-1}}, there is an index j with 0 <= j < len(stones), j != i_t, and j not in S_t, satisfying stones[i_t][0] = stones[j][0] or stones[i_t][1] = stones[j][1]. Thus r stones can legally be removed in that order.
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_7 (stones : Stones) (h : ValidInput stones) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      ∃ l : List Nat, l.Nodup ∧ LegalOrder stones l ∧ (l.length : Int) = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      ∃ l : List Nat, l.Nodup ∧ LegalOrder stones l ∧ (l.length : Int) = r.val) := by
  sorry

/-- The function returns a result r. For every m >= 0 and every sequence i_1, ..., i_m of distinct indices from {0, ..., len(stones)-1} that is legal in the following sense: for each t with 1 <= t <= m, before removing i_t there is an index j with 0 <= j < len(stones), j != i_t, and j not in {i_1, ..., i_{t-1}} such that stones[i_t][0] = stones[j][0] or stones[i_t][1] = stones[j][1]; we have m <= r.
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_8 (stones : Stones) (h : ValidInput stones) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      ∀ l : List Nat, l.Nodup → LegalOrder stones l → (l.length : Int) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      ∀ l : List Nat, l.Nodup → LegalOrder stones l → (l.length : Int) ≤ r.val) := by
  sorry

/-- Let swapped be the list of length len(stones) with swapped[i] = [stones[i][1], stones[i][0]] for every i with 0 <= i < len(stones). The function returns a result r, and the same function remove_stones applied to swapped also returns the same result r.
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_9 (stones : Stones) (h : ValidInput stones) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      Aegis.RemoveStones.remove_stones (swapStones stones) = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      Aegis.RemoveStones.remove_stones (swapStones stones) = ok r) := by
  sorry

/-- For every permutation p of the index set {0, ..., len(stones)-1}, let permuted be the list of length len(stones) with permuted[i] = stones[p(i)] for 0 <= i < len(stones). The function returns a result r, and the same function remove_stones applied to permuted also returns the same result r.
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_10 (stones : Stones) (h : ValidInput stones)
    (p : Equiv.Perm (Fin (len stones))) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      Aegis.RemoveStones.remove_stones (permuteStones stones p) = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones)
    (p : Equiv.Perm (Fin (len stones))), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      Aegis.RemoveStones.remove_stones (permuteStones stones p) = ok r) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if for every i,j with 0 <= i < j < len(stones), stones[i][0] != stones[j][0] and stones[i][1] != stones[j][1] (equivalently, no two stones share a row or a column).
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_11 (stones : Stones) (h : ValidInput stones) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      (r.val = 0 ↔ ∀ i j, i < j → j < len stones →
        row stones i ≠ row stones j ∧ col stones i ≠ col stones j) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      (r.val = 0 ↔ ∀ i j, i < j → j < len stones →
        row stones i ≠ row stones j ∧ col stones i ≠ col stones j)) := by
  sorry

/-- The function returns a result r, and r = len(stones) - 1 if and only if all stones lie in a single connected component: for every i with 0 <= i < len(stones), there exist m >= 0 and indices k_0, ..., k_m in {0, ..., len(stones)-1} such that k_0 = i, k_m = 0, and for every t with 0 <= t < m, stones[k_t][0] = stones[k_{t+1}][0] or stones[k_t][1] = stones[k_{t+1}][1].
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; and for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]. -/
theorem spec_12 (stones : Stones) (h : ValidInput stones) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      (r.val = (len stones : Int) - 1 ↔ ∀ i, i < len stones → Walk stones i 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      (r.val = (len stones : Int) - 1 ↔ ∀ i, i < len stones → Walk stones i 0)) := by
  sorry

/-- Let transformed be the list of length len(stones) with transformed[i] = [f(stones[i][0]), g(stones[i][1])] for every i with 0 <= i < len(stones). The function returns a result r, and the same function remove_stones applied to transformed also returns the same result r.
  Preconditions: len(stones) >= 1 and len(stones) <= 1000; for every i with 0 <= i < len(stones), len(stones[i]) = 2, 0 <= stones[i][0] <= 10000, and 0 <= stones[i][1] <= 10000; for every i,j with 0 <= i < j < len(stones), it is not the case that stones[i][0] = stones[j][0] and stones[i][1] = stones[j][1]; and f and g are permutations of {0, 1, ..., 10000}. -/
theorem spec_13 (stones : Stones) (h : ValidInput stones)
    (f g : Equiv.Perm (Fin 10001)) :
    ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      Aegis.RemoveStones.remove_stones (transformStones stones f g) = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (stones : Stones) (h : ValidInput stones)
    (f g : Equiv.Perm (Fin 10001)), ∃ r, Aegis.RemoveStones.remove_stones stones = ok r ∧
      Aegis.RemoveStones.remove_stones (transformStones stones f g) = ok r) := by
  sorry

end AegisSpec.RemoveStones
