import Aegis.MaxWeight.Code.Funs

/-!
# Specifications of `Aegis.MaxWeight.max_weight`

LeetCode problem `eat-pizzas`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxWeight

  def weights (pizzas : Slice Std.I64) : List Int := pizzas.val.map (fun x => x.val)

  def insertSorted (x : Int) : List Int → List Int
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

  def sortInts : List Int → List Int
    | [] => []
    | x :: xs => insertSorted x (sortInts xs)

  def altSum : List Int → Int
    | [] => 0
    | [x] => x
    | x :: _ :: xs => x + altSum xs

  def topSum (b : List Int) (o : Nat) : Int := (b.reverse.take o).sum

  def skipSum (b : List Int) (o e : Nat) : Int :=
    altSum ((b.reverse.drop (o + 1)).take (2 * e))

  def formulaValue (b : List Int) : Int :=
    let d := b.length / 4
    let o := (d + 1) / 2
    let e := d / 2
    topSum b o + skipSum b o e

  def sortedWeights (pizzas : Slice Std.I64) : List Int := sortInts (weights pizzas)

  def maxWeightOf (pizzas : Slice Std.I64) : Int := (weights pizzas).foldr max 0

  def ValidInput (pizzas : Slice Std.I64) : Prop :=
    4 ≤ (weights pizzas).length ∧
      (weights pizzas).length ≤ 200000 ∧
      (weights pizzas).length % 4 = 0 ∧
      ∀ i : Fin (weights pizzas).length,
        1 ≤ (weights pizzas).get i ∧ (weights pizzas).get i ≤ 100000

  def PointwiseOn (L₁ L₂ : List Int) (R : Int → Int → Prop) : Prop :=
    ∀ (i : Nat) (h₁ : i < L₁.length) (h₂ : i < L₂.length), R L₁[i] L₂[i]

  def IsQuadPartition {m d : Nat} (g : Fin m → Fin d) : Prop :=
    ∀ j : Fin d, ((List.finRange m).filter (fun i => g i = j)).length = 4

  def groupWeights (L : List Int) {d : Nat} (g : (i : Fin L.length) → Fin d)
      (j : Fin d) : List Int :=
    sortInts (((List.finRange L.length).filter (fun i => g i = j)).map (fun i => L.get i))

  /-- Whenever max_weight returns a result r, the following holds. Let b be the nondecreasing list obtained by sorting pizzas, so len(b) = n and b is a permutation of pizzas. Put d = n/4, o = ceil(d/2) = (d+1) div 2, and e = floor(d/2) = d div 2. Then, as an ordinary integer, the value of r is Sum_{i=0}^{o-1} b[n-1-i] + Sum_{j=1}^{e} b[n-o-2j]. The second sum is empty if e = 0.
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. -/
  theorem spec_1 (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
      (hr : Aegis.MaxWeight.max_weight pizzas = ok r) :
      r.val = formulaValue (sortedWeights pizzas) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
        (hr : Aegis.MaxWeight.max_weight pizzas = ok r), r.val = formulaValue (sortedWeights pizzas)) := by
    sorry

  /-- For every pizzas satisfying the preconditions, max_weight returns a result r; it does not fail, panic, perform an out-of-bounds access, or overflow.
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. -/
  theorem spec_2 (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) :
      ∃ r : Std.I64, Aegis.MaxWeight.max_weight pizzas = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (pizzas : Slice Std.I64) (hpre : ValidInput pizzas), ∃ r : Std.I64, Aegis.MaxWeight.max_weight pizzas = ok r) := by
    sorry

  /-- Whenever max_weight returns a result r, as an integer r >= max_{0 <= i < n} pizzas[i].
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. -/
  theorem spec_3 (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
      (hr : Aegis.MaxWeight.max_weight pizzas = ok r) :
      maxWeightOf pizzas ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
        (hr : Aegis.MaxWeight.max_weight pizzas = ok r), maxWeightOf pizzas ≤ r.val) := by
    sorry

  /-- Whenever max_weight returns a result r, r <= (n/4) * max_{0 <= i < n} pizzas[i].
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. -/
  theorem spec_4 (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
      (hr : Aegis.MaxWeight.max_weight pizzas = ok r) :
      r.val ≤ ((weights pizzas).length / 4 : Nat) * maxWeightOf pizzas := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
        (hr : Aegis.MaxWeight.max_weight pizzas = ok r), r.val ≤ ((weights pizzas).length / 4 : Nat) * maxWeightOf pizzas) := by
    sorry

  /-- Whenever max_weight returns a result r, r <= Sum_{i=0}^{n-1} pizzas[i].
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. -/
  theorem spec_5 (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
      (hr : Aegis.MaxWeight.max_weight pizzas = ok r) :
      r.val ≤ (weights pizzas).sum := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
        (hr : Aegis.MaxWeight.max_weight pizzas = ok r), r.val ≤ (weights pizzas).sum) := by
    sorry

  /-- Whenever max_weight returns a result r, r = (n/4) * w.
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. Also assume there is an integer w such that pizzas[i] = w for every i with 0 <= i < n. -/
  theorem spec_6 (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (w : Int)
      (hconst : ∀ i : Fin (weights pizzas).length, (weights pizzas).get i = w)
      (r : Std.I64) (hr : Aegis.MaxWeight.max_weight pizzas = ok r) :
      r.val = ((weights pizzas).length / 4 : Nat) * w := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (w : Int)
        (hconst : ∀ i : Fin (weights pizzas).length, (weights pizzas).get i = w)
        (r : Std.I64) (hr : Aegis.MaxWeight.max_weight pizzas = ok r), r.val = ((weights pizzas).length / 4 : Nat) * w) := by
    sorry

  /-- Whenever max_weight returns a result r, r = max_{0 <= i < 4} pizzas[i].
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. Also assume n = 4. -/
  theorem spec_7 (pizzas : Slice Std.I64) (hpre : ValidInput pizzas)
      (hlen : (weights pizzas).length = 4) (r : Std.I64)
      (hr : Aegis.MaxWeight.max_weight pizzas = ok r) :
      r.val = maxWeightOf pizzas := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (pizzas : Slice Std.I64) (hpre : ValidInput pizzas)
        (hlen : (weights pizzas).length = 4) (r : Std.I64)
        (hr : Aegis.MaxWeight.max_weight pizzas = ok r), r.val = maxWeightOf pizzas) := by
    sorry

  /-- Whenever max_weight returns r for pizzas and returns r' for q, r = r'.
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. Let q be another slice of length n satisfying the same bounds, and assume q is a permutation of pizzas, meaning that for every integer v, the number of positions i with pizzas[i] = v equals the number of positions i with q[i] = v. -/
  theorem spec_8 (pizzas q : Slice Std.I64) (hpre : ValidInput pizzas)
      (hq : ValidInput q) (hlen : (weights q).length = (weights pizzas).length)
      (hperm : ∀ v : Int, (weights q).count v = (weights pizzas).count v)
      (r r' : Std.I64) (hr : Aegis.MaxWeight.max_weight pizzas = ok r)
      (hr' : Aegis.MaxWeight.max_weight q = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (pizzas q : Slice Std.I64) (hpre : ValidInput pizzas)
        (hq : ValidInput q) (hlen : (weights q).length = (weights pizzas).length)
        (hperm : ∀ v : Int, (weights q).count v = (weights pizzas).count v)
        (r r' : Std.I64) (hr : Aegis.MaxWeight.max_weight pizzas = ok r)
        (hr' : Aegis.MaxWeight.max_weight q = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever max_weight returns r for pizzas and returns r' for q, r' = r + (n/4) * c.
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. Let q be another slice of length n satisfying the same bounds, and assume there is an integer c such that q[i] = pizzas[i] + c for every i with 0 <= i < n. -/
  theorem spec_9 (pizzas q : Slice Std.I64) (hpre : ValidInput pizzas)
      (hq : ValidInput q) (hlen : (weights q).length = (weights pizzas).length) (c : Int)
      (hshift : PointwiseOn (weights pizzas) (weights q) (fun a b => b = a + c))
      (r r' : Std.I64) (hr : Aegis.MaxWeight.max_weight pizzas = ok r)
      (hr' : Aegis.MaxWeight.max_weight q = ok r') :
      r'.val = r.val + ((weights pizzas).length / 4 : Nat) * c := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (pizzas q : Slice Std.I64) (hpre : ValidInput pizzas)
        (hq : ValidInput q) (hlen : (weights q).length = (weights pizzas).length) (c : Int)
        (hshift : PointwiseOn (weights pizzas) (weights q) (fun a b => b = a + c))
        (r r' : Std.I64) (hr : Aegis.MaxWeight.max_weight pizzas = ok r)
        (hr' : Aegis.MaxWeight.max_weight q = ok r'), r'.val = r.val + ((weights pizzas).length / 4 : Nat) * c) := by
    sorry

  /-- Whenever max_weight returns r for pizzas and returns r' for q, r <= r'.
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. Let q be another slice of length n satisfying the same bounds, and assume pizzas[i] <= q[i] for every i with 0 <= i < n. -/
  theorem spec_10 (pizzas q : Slice Std.I64) (hpre : ValidInput pizzas)
      (hq : ValidInput q) (hlen : (weights q).length = (weights pizzas).length)
      (hmono : PointwiseOn (weights pizzas) (weights q) (fun a b => a ≤ b))
      (r r' : Std.I64) (hr : Aegis.MaxWeight.max_weight pizzas = ok r)
      (hr' : Aegis.MaxWeight.max_weight q = ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (pizzas q : Slice Std.I64) (hpre : ValidInput pizzas)
        (hq : ValidInput q) (hlen : (weights q).length = (weights pizzas).length)
        (hmono : PointwiseOn (weights pizzas) (weights q) (fun a b => a ≤ b))
        (r r' : Std.I64) (hr : Aegis.MaxWeight.max_weight pizzas = ok r)
        (hr' : Aegis.MaxWeight.max_weight q = ok r'), r.val ≤ r'.val) := by
    sorry

  /-- Whenever max_weight returns r for pizzas and returns r' for q, r' = c * r.
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. Let q be another slice of length n satisfying the same bounds, and assume there is an integer c >= 1 such that q[i] = c * pizzas[i] for every i with 0 <= i < n. -/
  theorem spec_11 (pizzas q : Slice Std.I64) (hpre : ValidInput pizzas)
      (hq : ValidInput q) (hlen : (weights q).length = (weights pizzas).length) (c : Int)
      (hc : 1 ≤ c) (hscale : PointwiseOn (weights pizzas) (weights q) (fun a b => b = c * a))
      (r r' : Std.I64) (hr : Aegis.MaxWeight.max_weight pizzas = ok r)
      (hr' : Aegis.MaxWeight.max_weight q = ok r') :
      r'.val = c * r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (pizzas q : Slice Std.I64) (hpre : ValidInput pizzas)
        (hq : ValidInput q) (hlen : (weights q).length = (weights pizzas).length) (c : Int)
        (hc : 1 ≤ c) (hscale : PointwiseOn (weights pizzas) (weights q) (fun a b => b = c * a))
        (r r' : Std.I64) (hr : Aegis.MaxWeight.max_weight pizzas = ok r)
        (hr' : Aegis.MaxWeight.max_weight q = ok r'), r'.val = c * r.val) := by
    sorry

  /-- Whenever max_weight returns a result r, there exist d = n/4 pairwise disjoint 4-element subsets G_1, ..., G_d of {0, ..., n-1} whose union is {0, ..., n-1}, and a set O of exactly o = ceil(d/2) of these groups, such that, writing the four weights in each group G in nondecreasing order as W_G <= X_G <= Y_G <= Z_G, one has r = Sum_{G in O} Z_G + Sum_{G not in O} Y_G.
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. -/
  theorem spec_12 (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
      (hr : Aegis.MaxWeight.max_weight pizzas = ok r) :
      ∃ d : Nat,
        d = (weights pizzas).length / 4 ∧
          ∃ (g : (i : Fin (weights pizzas).length) → Fin d) (O : Finset (Fin d))
            (W X Y Z : Fin d → Int),
            IsQuadPartition g ∧
              O.card = (d + 1) / 2 ∧
              (∀ j : Fin d, W j ≤ X j ∧ X j ≤ Y j ∧ Y j ≤ Z j) ∧
              (∀ j : Fin d, groupWeights (weights pizzas) g j = [W j, X j, Y j, Z j]) ∧
              r.val = (∑ j ∈ O, Z j) + ∑ j ∈ (Finset.univ \ O), Y j := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
        (hr : Aegis.MaxWeight.max_weight pizzas = ok r), ∃ d : Nat,
          d = (weights pizzas).length / 4 ∧
            ∃ (g : (i : Fin (weights pizzas).length) → Fin d) (O : Finset (Fin d))
              (W X Y Z : Fin d → Int),
              IsQuadPartition g ∧
                O.card = (d + 1) / 2 ∧
                (∀ j : Fin d, W j ≤ X j ∧ X j ≤ Y j ∧ Y j ≤ Z j) ∧
                (∀ j : Fin d, groupWeights (weights pizzas) g j = [W j, X j, Y j, Z j]) ∧
                r.val = (∑ j ∈ O, Z j) + ∑ j ∈ (Finset.univ \ O), Y j) := by
    sorry

  /-- Whenever max_weight returns a result r, for every choice of d = n/4 pairwise disjoint 4-element subsets G_1, ..., G_d of {0, ..., n-1} whose union is {0, ..., n-1}, and every set O of exactly o = ceil(d/2) of these groups, if W_G <= X_G <= Y_G <= Z_G are the sorted weights of group G, then Sum_{G in O} Z_G + Sum_{G not in O} Y_G <= r.
    Preconditions: Let n = len(pizzas). Assume 4 <= n <= 200000, n is a multiple of 4, and for every i with 0 <= i < n, 1 <= pizzas[i] <= 100000. -/
  theorem spec_13 (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
      (hr : Aegis.MaxWeight.max_weight pizzas = ok r) :
      ∀ (d : Nat) (hd : d = (weights pizzas).length / 4)
        (g : (i : Fin (weights pizzas).length) → Fin d) (O : Finset (Fin d))
        (W X Y Z : Fin d → Int),
        IsQuadPartition g →
          O.card = (d + 1) / 2 →
            (∀ j : Fin d, W j ≤ X j ∧ X j ≤ Y j ∧ Y j ≤ Z j) →
              (∀ j : Fin d, groupWeights (weights pizzas) g j = [W j, X j, Y j, Z j]) →
                (∑ j ∈ O, Z j) + ∑ j ∈ (Finset.univ \ O), Y j ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (pizzas : Slice Std.I64) (hpre : ValidInput pizzas) (r : Std.I64)
        (hr : Aegis.MaxWeight.max_weight pizzas = ok r), ∀ (d : Nat) (hd : d = (weights pizzas).length / 4)
          (g : (i : Fin (weights pizzas).length) → Fin d) (O : Finset (Fin d))
          (W X Y Z : Fin d → Int),
          IsQuadPartition g →
            O.card = (d + 1) / 2 →
              (∀ j : Fin d, W j ≤ X j ∧ X j ≤ Y j ∧ Y j ≤ Z j) →
                (∀ j : Fin d, groupWeights (weights pizzas) g j = [W j, X j, Y j, Z j]) →
                  (∑ j ∈ O, Z j) + ∑ j ∈ (Finset.univ \ O), Y j ≤ r.val) := by
    sorry

  end AegisSpec.MaxWeight
