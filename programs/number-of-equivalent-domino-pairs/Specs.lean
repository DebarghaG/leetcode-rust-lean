import Aegis.NumEquivDominoPairs.Code.Funs

/-!
# Specifications of `Aegis.NumEquivDominoPairs.num_equiv_domino_pairs`

LeetCode problem `number-of-equivalent-domino-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumEquivDominoPairs

open Aegis.NumEquivDominoPairs (num_equiv_domino_pairs)

def contents (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

def dominoAt (dominoes : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  match dominoes.val[i]? with
  | some v => contents v
  | none => []

def dominoEquivB (x y : List Int) : Bool :=
  match x, y with
  | [a, b], [c, d] => (a == c && b == d) || (a == d && b == c)
  | _, _ => false

def DominoEquiv (x y : List Int) : Prop := dominoEquivB x y = true

def numEquivPairs (dominoes : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  ((List.range dominoes.val.length).product (List.range dominoes.val.length)).countP
    (fun p => p.1 < p.2 && dominoEquivB (dominoAt dominoes p.1) (dominoAt dominoes p.2))

def countEquivTo (dominoes : Slice (alloc.vec.Vec Std.I64)) (x : List Int) : Nat :=
  (List.range dominoes.val.length).countP (fun i => dominoEquivB (dominoAt dominoes i) x)

def IsValidDomino (v : alloc.vec.Vec Std.I64) : Prop :=
  v.val.length = 2 ∧ ∀ z ∈ v.val, 1 ≤ z.val ∧ z.val ≤ 9

def ValidInput (dominoes : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ dominoes.val.length ∧ dominoes.val.length ≤ 40000 ∧
    ∀ v ∈ dominoes.val, IsValidDomino v

def IsPermOn (n : Nat) (pi : Nat → Nat) : Prop :=
  (∀ i, i < n → pi i < n) ∧
    (∀ i, i < n → ∀ k, k < n → pi i = pi k → i = k) ∧
      (∀ j, j < n → ∃ i, i < n ∧ pi i = j)

def IsPermOn1To9 (f : Int → Int) : Prop :=
  (∀ z, 1 ≤ z ∧ z ≤ 9 → 1 ≤ f z ∧ f z ≤ 9) ∧
    (∀ z, 1 ≤ z ∧ z ≤ 9 → ∀ w, 1 ≤ w ∧ w ≤ 9 → f z = f w → z = w) ∧
      (∀ y, 1 ≤ y ∧ y ≤ 9 → ∃ z, 1 ≤ z ∧ z ≤ 9 ∧ f z = y)

/-- Whenever the function returns a result r, r equals the number of pairs (i,j) such that 0 <= i < j < len(dominoes) and dominoes[i] and dominoes[j] are equivalent, where two two-element vectors x and y are equivalent when (x[0]=y[0] and x[1]=y[1]) or (x[0]=y[1] and x[1]=y[0]).
  Preconditions: 1 <= len(dominoes) <= 40000; for every i with 0 <= i < len(dominoes), len(dominoes[i]) = 2; for every i with 0 <= i < len(dominoes) and j in {0,1}, 1 <= dominoes[i][j] <= 9. -/
theorem spec_1 (dominoes : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput dominoes)
    (r : I64) (hr : num_equiv_domino_pairs dominoes = ok r) :
    r.val = (numEquivPairs dominoes : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (dominoes : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput dominoes)
    (r : I64) (hr : num_equiv_domino_pairs dominoes = ok r), r.val = (numEquivPairs dominoes : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; in particular it does not fail, panic, access an out-of-bounds index, or overflow 64-bit arithmetic in producing the reported count.
  Preconditions: 1 <= len(dominoes) <= 40000; for every i with 0 <= i < len(dominoes), len(dominoes[i]) = 2; for every i with 0 <= i < len(dominoes) and j in {0,1}, 1 <= dominoes[i][j] <= 9. -/
theorem spec_2 (dominoes : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput dominoes) :
    ∃ r : I64, num_equiv_domino_pairs dominoes = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (dominoes : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput dominoes), ∃ r : I64, num_equiv_domino_pairs dominoes = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(dominoes)*(len(dominoes)-1)/2; under the length constraint this also gives 0 <= r <= 799980000.
  Preconditions: 1 <= len(dominoes) <= 40000; for every i with 0 <= i < len(dominoes), len(dominoes[i]) = 2; for every i with 0 <= i < len(dominoes) and j in {0,1}, 1 <= dominoes[i][j] <= 9. -/
theorem spec_3 (dominoes : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput dominoes)
    (r : I64) (hr : num_equiv_domino_pairs dominoes = ok r) :
    0 ≤ r.val ∧
      r.val ≤ ((dominoes.val.length * (dominoes.val.length - 1) / 2 : Nat) : Int) ∧
        r.val ≤ 799980000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (dominoes : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput dominoes)
    (r : I64) (hr : num_equiv_domino_pairs dominoes = ok r), 0 ≤ r.val ∧
      r.val ≤ ((dominoes.val.length * (dominoes.val.length - 1) / 2 : Nat) : Int) ∧
        r.val ≤ 799980000) := by
  sorry

/-- Let dominoes' be any input with len(dominoes')=len(dominoes) such that for every i with 0 <= i < len(dominoes), dominoes'[i][0]=dominoes[i][1] and dominoes'[i][1]=dominoes[i][0]. Whenever num_equiv_domino_pairs(dominoes) returns r and num_equiv_domino_pairs(dominoes') returns r', we have r = r'.
  Preconditions: 1 <= len(dominoes) <= 40000; for every i with 0 <= i < len(dominoes), len(dominoes[i]) = 2; for every i with 0 <= i < len(dominoes) and j in {0,1}, 1 <= dominoes[i][j] <= 9. -/
theorem spec_4 (dominoes dominoes' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput dominoes) (h' : ValidInput dominoes')
    (hlen : dominoes'.val.length = dominoes.val.length)
    (hswap : ∀ i, i < dominoes.val.length →
      dominoAt dominoes' i = (dominoAt dominoes i).reverse)
    (r r' : I64) (hr : num_equiv_domino_pairs dominoes = ok r)
    (hr' : num_equiv_domino_pairs dominoes' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (dominoes dominoes' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput dominoes) (h' : ValidInput dominoes')
    (hlen : dominoes'.val.length = dominoes.val.length)
    (hswap : ∀ i, i < dominoes.val.length →
      dominoAt dominoes' i = (dominoAt dominoes i).reverse)
    (r r' : I64) (hr : num_equiv_domino_pairs dominoes = ok r)
    (hr' : num_equiv_domino_pairs dominoes' = ok r'), r.val = r'.val) := by
  sorry

/-- For any dominoes' that is a permutation of dominoes, meaning len(dominoes')=len(dominoes) and there is a bijection pi from {0,...,len(dominoes)-1} to itself such that dominoes'[i]=dominoes[pi(i)] for every i, if num_equiv_domino_pairs(dominoes) returns r and num_equiv_domino_pairs(dominoes') returns r', then r = r'.
  Preconditions: 1 <= len(dominoes) <= 40000; for every i with 0 <= i < len(dominoes), len(dominoes[i]) = 2; for every i with 0 <= i < len(dominoes) and j in {0,1}, 1 <= dominoes[i][j] <= 9. -/
theorem spec_5 (dominoes dominoes' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput dominoes) (h' : ValidInput dominoes')
    (hlen : dominoes'.val.length = dominoes.val.length)
    (hperm : ∃ pi : Nat → Nat, IsPermOn dominoes.val.length pi ∧
      ∀ i, i < dominoes.val.length → dominoAt dominoes' i = dominoAt dominoes (pi i))
    (r r' : I64) (hr : num_equiv_domino_pairs dominoes = ok r)
    (hr' : num_equiv_domino_pairs dominoes' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (dominoes dominoes' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput dominoes) (h' : ValidInput dominoes')
    (hlen : dominoes'.val.length = dominoes.val.length)
    (hperm : ∃ pi : Nat → Nat, IsPermOn dominoes.val.length pi ∧
      ∀ i, i < dominoes.val.length → dominoAt dominoes' i = dominoAt dominoes (pi i))
    (r r' : I64) (hr : num_equiv_domino_pairs dominoes = ok r)
    (hr' : num_equiv_domino_pairs dominoes' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exist indices i,j with 0 <= i < j < len(dominoes) such that dominoes[i] and dominoes[j] are equivalent, where two two-element vectors x and y are equivalent when (x[0]=y[0] and x[1]=y[1]) or (x[0]=y[1] and x[1]=y[0]).
  Preconditions: 1 <= len(dominoes) <= 40000; for every i with 0 <= i < len(dominoes), len(dominoes[i]) = 2; for every i with 0 <= i < len(dominoes) and j in {0,1}, 1 <= dominoes[i][j] <= 9. -/
theorem spec_6 (dominoes : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput dominoes)
    (r : I64) (hr : num_equiv_domino_pairs dominoes = ok r) :
    0 < r.val ↔ ∃ i j : Nat, i < j ∧ j < dominoes.val.length ∧
      DominoEquiv (dominoAt dominoes i) (dominoAt dominoes j) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (dominoes : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput dominoes)
    (r : I64) (hr : num_equiv_domino_pairs dominoes = ok r), 0 < r.val ↔ ∃ i j : Nat, i < j ∧ j < dominoes.val.length ∧
      DominoEquiv (dominoAt dominoes i) (dominoAt dominoes j)) := by
  sorry

/-- Let dominoes' be the list obtained by appending x to dominoes, so len(dominoes')=len(dominoes)+1 and dominoes'[len(dominoes)]=x. Whenever num_equiv_domino_pairs(dominoes) returns r and num_equiv_domino_pairs(dominoes') returns r', we have r' = r + k, where k is the number of indices i with 0 <= i < len(dominoes) such that dominoes[i] and x are equivalent, with equivalence defined by (u[0]=v[0] and u[1]=v[1]) or (u[0]=v[1] and u[1]=v[0]).
  Preconditions: 1 <= len(dominoes) < 40000; for every i with 0 <= i < len(dominoes), len(dominoes[i]) = 2; for every i with 0 <= i < len(dominoes) and j in {0,1}, 1 <= dominoes[i][j] <= 9; and x is a two-element vector with 1 <= x[0] <= 9 and 1 <= x[1] <= 9. -/
theorem spec_7 (dominoes dominoes' : Slice (alloc.vec.Vec Std.I64))
    (x : alloc.vec.Vec Std.I64)
    (h : ValidInput dominoes) (hx : IsValidDomino x)
    (h' : ValidInput dominoes') (hcat : dominoes'.val = dominoes.val ++ [x])
    (r r' : I64) (hr : num_equiv_domino_pairs dominoes = ok r)
    (hr' : num_equiv_domino_pairs dominoes' = ok r') :
    r'.val = r.val + (countEquivTo dominoes (contents x) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (dominoes dominoes' : Slice (alloc.vec.Vec Std.I64))
    (x : alloc.vec.Vec Std.I64)
    (h : ValidInput dominoes) (hx : IsValidDomino x)
    (h' : ValidInput dominoes') (hcat : dominoes'.val = dominoes.val ++ [x])
    (r r' : I64) (hr : num_equiv_domino_pairs dominoes = ok r)
    (hr' : num_equiv_domino_pairs dominoes' = ok r'), r'.val = r.val + (countEquivTo dominoes (contents x) : Int)) := by
  sorry

/-- For every permutation f of {1,...,9}, let dominoes' have the same shape as dominoes and satisfy dominoes'[i][j]=f(dominoes[i][j]) for every i with 0 <= i < len(dominoes) and j in {0,1}. Whenever num_equiv_domino_pairs(dominoes) returns r and num_equiv_domino_pairs(dominoes') returns r', we have r = r'.
  Preconditions: 1 <= len(dominoes) <= 40000; for every i with 0 <= i < len(dominoes), len(dominoes[i]) = 2; for every i with 0 <= i < len(dominoes) and j in {0,1}, 1 <= dominoes[i][j] <= 9. -/
theorem spec_8 (dominoes dominoes' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput dominoes) (h' : ValidInput dominoes')
    (hlen : dominoes'.val.length = dominoes.val.length)
    (f : Int → Int) (hf : IsPermOn1To9 f)
    (hmap : ∀ i, i < dominoes.val.length → dominoAt dominoes' i = (dominoAt dominoes i).map f)
    (r r' : I64) (hr : num_equiv_domino_pairs dominoes = ok r)
    (hr' : num_equiv_domino_pairs dominoes' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (dominoes dominoes' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput dominoes) (h' : ValidInput dominoes')
    (hlen : dominoes'.val.length = dominoes.val.length)
    (f : Int → Int) (hf : IsPermOn1To9 f)
    (hmap : ∀ i, i < dominoes.val.length → dominoAt dominoes' i = (dominoAt dominoes i).map f)
    (r r' : I64) (hr : num_equiv_domino_pairs dominoes = ok r)
    (hr' : num_equiv_domino_pairs dominoes' = ok r'), r.val = r'.val) := by
  sorry

end AegisSpec.NumEquivDominoPairs
