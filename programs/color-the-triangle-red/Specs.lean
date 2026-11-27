import Aegis.ColorRed.Code.Funs

/-!
# Specifications of `Aegis.ColorRed.color_red`

LeetCode problem `color-the-triangle-red`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ColorRed

namespace AegisSpec.ColorRed

def nNat (n : Std.I64) : Nat := n.val.toNat

def IsPair (v : alloc.vec.Vec Std.I64) (p : Nat × Nat) : Prop :=
  ∃ i j : Std.I64, v.val = [i, j] ∧ i.val = (p.1 : Int) ∧ j.val = (p.2 : Int)

def toPair (v : alloc.vec.Vec Std.I64) : Option (Nat × Nat) :=
  match v.val with
  | [i, j] => if 0 ≤ i.val ∧ 0 ≤ j.val then some (i.val.toNat, j.val.toNat) else none
  | _ => none

def occList (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (Nat × Nat) :=
  r.val.filterMap toPair

def Occ (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : Finset (Nat × Nat) :=
  (occList r).toFinset

def InB (n : Nat) (p : Nat × Nat) : Prop :=
  1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ 2 * p.1 - 1

def B (n : Nat) : Finset (Nat × Nat) :=
  (((Finset.range n).product (Finset.range (2 * n))).filter
      (fun p : Nat × Nat => p.2 + 1 ≤ 2 * (p.1 + 1) - 1)).image
    (fun p : Nat × Nat => (p.1 + 1, p.2 + 1))

theorem mem_B_iff (n : Nat) (p : Nat × Nat) : p ∈ B n ↔ InB n p := by
  simp [B, InB, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, b, hb, hle, rfl⟩
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨p.1 - 1, by omega, p.2 - 1, by omega, by omega, ?_⟩
    refine Prod.ext ?_ ?_ <;> simp <;> omega

def Neighbor (p q : Nat × Nat) : Prop :=
  (p.1 = q.1 ∧ Int.natAbs ((p.2 : Int) - (q.2 : Int)) = 1) ∨
    (p.2 % 2 = 1 ∧ q = (p.1 + 1, p.2 + 1)) ∨
    (p.2 % 2 = 0 ∧ p = (q.1 + 1, q.2 + 1))

instance instDecidablePredNeighbor (p : Nat × Nat) : DecidablePred (Neighbor p) :=
  fun q => by unfold Neighbor; infer_instance

inductive Add (n : Nat) : Finset (Nat × Nat) → Finset (Nat × Nat) → Prop
  | intro (S : Finset (Nat × Nat)) (p : Nat × Nat)
      (hB : p ∈ B n) (hnot : p ∉ S)
      (h2 : 2 ≤ (S.filter (fun q => Neighbor p q)).card) : Add n S (insert p S)

def Reach (n : Nat) (S T : Finset (Nat × Nat)) : Prop :=
  Relation.ReflTransGen (Add n) S T

def Stable (n : Nat) (S : Finset (Nat × Nat)) : Prop :=
  ∀ p, p ∈ B n → p ∉ S → (S.filter (fun q => Neighbor p q)).card < 2

def ColorOrder (n : Nat) : Finset (Nat × Nat) → List (Nat × Nat) → Prop
  | _, [] => True
  | S, p :: ps =>
      p ∈ B n ∧ p ∉ S ∧ 2 ≤ (S.filter (fun q => Neighbor p q)).card ∧
        ColorOrder n (insert p S) ps

noncomputable def K (n : Nat) : Nat :=
  sInf {k : Nat | ∃ T : Finset (Nat × Nat), T ⊆ B n ∧ Reach n T (B n) ∧ T.card = k}

/-- Assume 1 <= n <= 1000. Let B_n = { (i,j) : 1 <= i <= n and 1 <= j <= 2i - 1 }. Two triangles of B_n are neighbors iff they share a side in the triangular tiling (equivalently: same row and |j-j'| = 1, or j is odd and (i',j') = (i+1,j+1), or j is even and (i',j') = (i-1,j-1)). For S subset of B_n, let Cl(S) be the set obtained from S by repeatedly adding every triangle of B_n not yet in the set that has at least two neighbors already in the set, until no such triangle remains. The function returns a result r such that: (a) every element of r is a two-entry vector [i,j]; (b) the pairs occurring in r are pairwise distinct; (c) every occurring pair belongs to B_n; (d) if S is the set of occurring pairs, then Cl(S) = B_n; and (e) |S| = min { |T| : T subset of B_n and Cl(T) = B_n }. The order of the coordinate pairs in r is not restricted.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_1 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      color_red n = ok r ∧
        (∀ v ∈ r.val, v.val.length = 2) ∧
        (occList r).Nodup ∧
        (∀ p, p ∈ Occ r → p ∈ B (nNat n)) ∧
        Reach (nNat n) (Occ r) (B (nNat n)) ∧
        (Occ r).card = K (nNat n) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      color_red n = ok r ∧
        (∀ v ∈ r.val, v.val.length = 2) ∧
        (occList r).Nodup ∧
        (∀ p, p ∈ Occ r → p ∈ B (nNat n)) ∧
        Reach (nNat n) (Occ r) (B (nNat n)) ∧
        (Occ r).card = K (nNat n)) := by
  sorry

/-- Whenever the function returns a result r, r is a list of coordinate pairs: each element of r has exactly two components, the first a row index and the second a position index, both i64 integers. In particular, no element of r is a length-0, length-1, or length-greater-than-2 vector.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_2 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      (∀ v ∈ r.val, v.val.length = 2) ∧
        (∀ v ∈ r.val, ∃ i j : Std.I64, v.val = [i, j]) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      (∀ v ∈ r.val, v.val.length = 2) ∧
        (∀ v ∈ r.val, ∃ i j : Std.I64, v.val = [i, j])) := by
  sorry

/-- Whenever the function returns a result r, for every element [i,j] of r, 1 <= i <= n and 1 <= j <= 2i - 1. Thus every returned coordinate lies in B_n: row i has exactly 2i - 1 valid positions, and no coordinate outside the triangle is used.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_3 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      ∀ v ∈ r.val, ∀ i j : Std.I64, v.val = [i, j] →
        (1 : Int) ≤ i.val ∧ i.val ≤ n.val ∧ (1 : Int) ≤ j.val ∧ j.val ≤ 2 * i.val - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      ∀ v ∈ r.val, ∀ i j : Std.I64, v.val = [i, j] →
        (1 : Int) ≤ i.val ∧ i.val ≤ n.val ∧ (1 : Int) ≤ j.val ∧ j.val ≤ 2 * i.val - 1) := by
  sorry

/-- Whenever the function returns a result r, for all indices a,b with 0 <= a < b < len(r), r[a] != r[b]. Hence k = len(r) is exactly the number of distinct triangles that are colored red initially.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_4 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      r.val.Nodup ∧ (Occ r).card = r.val.length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      r.val.Nodup ∧ (Occ r).card = r.val.length) := by
  sorry

/-- Whenever the function returns a result r, let S be the set of coordinate pairs appearing in r. If initially exactly the triangles in S are red and all other triangles of B_n are white, then repeatedly adding every white triangle that has at least two red neighbors eventually makes all triangles of B_n red; equivalently, the closure process cannot stop while some triangle of B_n is still white.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_5 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      Reach (nNat n) (Occ r) (B (nNat n)) ∧
        (Stable (nNat n) (Occ r) → Occ r = B (nNat n)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      Reach (nNat n) (Occ r) (B (nNat n)) ∧
        (Stable (nNat n) (Occ r) → Occ r = B (nNat n))) := by
  sorry

/-- Whenever the function returns a result r, let S be the set of coordinate pairs appearing in r. Then |S| = K(n), where K(n) is the minimum cardinality of a subset T of B_n whose repeated 2-red-neighbor closure is B_n. This is the problem's requirement that the answer has the smallest possible size.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_6 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      (Occ r).card = K (nNat n) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      (Occ r).card = K (nNat n)) := by
  sorry

/-- Whenever the function returns a result r, let S be the set of coordinate pairs appearing in r. For every x in S, the set S \ {x} does not have closure B_n; that is, removing any one initially red triangle makes it impossible to color all triangles by the algorithm. No initially red triangle is redundant.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_7 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      ∀ x, x ∈ Occ r → ¬ Reach (nNat n) (Occ r \ {x}) (B (nNat n)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      ∀ x, x ∈ Occ r → ¬ Reach (nNat n) (Occ r \ {x}) (B (nNat n))) := by
  sorry

/-- Whenever the function returns a result r, the three corner triangles (1,1), (n,1), and (n,2n-1) each occur in r. These are exactly the degree-one triangles of B_n in the side-neighbor graph, so they cannot become red later and must be chosen initially.
  Preconditions: 2 <= n <= 1000. -/
theorem spec_8 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      (1, 1) ∈ Occ r ∧ (nNat n, 1) ∈ Occ r ∧ (nNat n, 2 * nNat n - 1) ∈ Occ r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      (1, 1) ∈ Occ r ∧ (nNat n, 1) ∈ Occ r ∧ (nNat n, 2 * nNat n - 1) ∈ Occ r) := by
  sorry

/-- Assume n = 1. The function returns a result r whose only element is [1,1]; equivalently len(r) = 1 and r[0] = [1,1]. There is only one unit triangle in B_1.
  Preconditions: n = 1. -/
theorem spec_9 (n : Std.I64) (hn : n.val = 1) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      color_red n = ok r ∧ r.val.length = 1 ∧ occList r = [(1, 1)] := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 1), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      color_red n = ok r ∧ r.val.length = 1 ∧ occList r = [(1, 1)]) := by
  sorry

/-- Assume n = 2. Whenever the function returns a result r, the set of pairs appearing in r is exactly { (1,1), (2,1), (2,3) }; thus len(r) = 3, the pair (2,2) does not occur, and the three pairs may appear in any order.
  Preconditions: n = 2. -/
theorem spec_10 (n : Std.I64) (hn : n.val = 2) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      Occ r = ({(1, 1), (2, 1), (2, 3)} : Finset (Nat × Nat)) ∧
        r.val.length = 3 ∧ (2, 2) ∉ Occ r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 2), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      Occ r = ({(1, 1), (2, 1), (2, 3)} : Finset (Nat × Nat)) ∧
        r.val.length = 3 ∧ (2, 2) ∉ Occ r) := by
  sorry

/-- Whenever the function returns a result r, let S be the set of coordinate pairs appearing in r. There exists a sequence x_1, ..., x_{n^2 - |S|} listing exactly the triangles of B_n \ S such that for every q from 1 to n^2 - |S|, the triangle x_q has at least two neighbors in S union {x_1, ..., x_{q-1}}. This sequence is a valid order in which the algorithm can color all initially white triangles.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_11 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      ∃ xs : List (Nat × Nat),
        (∀ p, p ∈ xs ↔ p ∈ B (nNat n) ∧ p ∉ Occ r) ∧
          xs.Nodup ∧ ColorOrder (nNat n) (Occ r) xs := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      ∃ xs : List (Nat × Nat),
        (∀ p, p ∈ xs ↔ p ∈ B (nNat n) ∧ p ∉ Occ r) ∧
          xs.Nodup ∧ ColorOrder (nNat n) (Occ r) xs) := by
  sorry

/-- Whenever the function returns a result r, let S be the set of coordinate pairs appearing in r. Starting from exactly S red, every maximal run of the stated algorithm - at each step choosing any white triangle with at least two red neighbors - ends only after all n^2 triangles of B_n are red. Thus nondeterministic choices cannot cause a premature stop.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_12 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      ∀ T : Finset (Nat × Nat), Reach (nNat n) (Occ r) T → Stable (nNat n) T →
        T = B (nNat n) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r →
      ∀ T : Finset (Nat × Nat), Reach (nNat n) (Occ r) T → Stable (nNat n) T →
        T = B (nNat n)) := by
  sorry

/-- Assume 1 <= n <= 1000. The function returns a result r; it does not fail, overflow, panic, or get stuck. In particular, color_red(n) is defined for every allowed n.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_13 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), color_red n = ok r) := by
  sorry

end AegisSpec.ColorRed
