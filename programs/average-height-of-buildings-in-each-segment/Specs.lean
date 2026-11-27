import Aegis.AverageHeightOfBuildings.Code.Funs

/-!
# Specifications of `Aegis.AverageHeightOfBuildings.average_height_of_buildings`

LeetCode problem `average-height-of-buildings-in-each-segment`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.AverageHeightOfBuildings

  abbrev Triple : Type := ℤ × ℤ × ℤ

  def rowTriple (v : alloc.vec.Vec Std.I64) : Triple :=
    match v.val with
    | s :: e :: h :: _ => (s.val, e.val, h.val)
    | _ => (0, 0, 0)

  def startAt (buildings : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (rowTriple buildings.val[i]!).1

  def endAt (buildings : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (rowTriple buildings.val[i]!).2.1

  def heightAt (buildings : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (rowTriple buildings.val[i]!).2.2

  def triples (buildings : Slice (alloc.vec.Vec Std.I64)) : List Triple :=
    buildings.val.map rowTriple

  def covering (buildings : Slice (alloc.vec.Vec Std.I64)) (x : ℤ) : List Triple :=
    (triples buildings).filter (fun t => decide (t.1 ≤ x ∧ x < t.2.1))

  def C (buildings : Slice (alloc.vec.Vec Std.I64)) (x : ℤ) : ℕ :=
    (covering buildings x).length

  def S (buildings : Slice (alloc.vec.Vec Std.I64)) (x : ℤ) : ℤ :=
    ((covering buildings x).map (fun t => t.2.2)).sum

  def A (buildings : Slice (alloc.vec.Vec Std.I64)) (x : ℤ) : ℤ :=
    Int.tdiv (S buildings x) (C buildings x : ℤ)

  def outRow (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (k : ℕ) : Triple :=
    match r.val[k]? with
    | some v => rowTriple v
    | none => (0, 0, 0)

  def outCount (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (x : ℤ) : ℕ :=
    (r.val.filter (fun v => decide ((rowTriple v).1 ≤ x ∧ x < (rowTriple v).2.1))).length

  def maxHeight (buildings : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((triples buildings).map (fun t => t.2.2)).max?.getD 0

  def minStart (buildings : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((triples buildings).map (fun t => t.1)).min?.getD 0

  def maxEnd (buildings : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((triples buildings).map (fun t => t.2.1)).max?.getD 0

  def ValidInput (buildings : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ buildings.val.length ∧
      buildings.val.length ≤ 100000 ∧
      (∀ v ∈ buildings.val, v.val.length = 3) ∧
      ∀ i, i < buildings.val.length →
        0 ≤ startAt buildings i ∧
          startAt buildings i < endAt buildings i ∧
          endAt buildings i ≤ 100000000 ∧
          1 ≤ heightAt buildings i ∧ heightAt buildings i ≤ 100000

  def IsMaxSegment (buildings : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ) : Prop :=
    a < b ∧
      (∀ x, a ≤ x → x < b → 0 < C buildings x) ∧
      ∃ c,
        (∀ x, a ≤ x → x < b → A buildings x = c) ∧
          (C buildings (a - 1) = 0 ∨ A buildings (a - 1) ≠ c) ∧
            (C buildings b = 0 ∨ A buildings b ≠ c)

  noncomputable def numSegments (buildings : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    Nat.card {p : ℤ × ℤ // IsMaxSegment buildings p.1 p.2}

  /-- Whenever the function returns a result r, the following hold. Every row of r has length 3; write its rows as r[k] = [l_k, r_k, a_k] for 0 <= k < len(r), and require l_k < r_k. For an integer x, let C(x) be the number of indices i with start_i <= x < end_i, and let S(x) be the sum of height_i over those i; when C(x) > 0 set A(x) = floor(S(x)/C(x)) using integer division truncating toward zero. Then (1) for every integer x, the number of k with l_k <= x < r_k is 1 if C(x) > 0 and is 0 if C(x) = 0; (2) for every k and every integer x with l_k <= x < r_k, C(x) > 0 and a_k = A(x); (3) for any two distinct rows p and q, if r_p = l_q or r_q = l_p then a_p != a_q. Equivalently, r is exactly the collection of maximal contiguous constant-average segments of the covered part of the street, with empty gaps excluded, and is therefore a minimum-size representation.
    Preconditions: Let n = len(buildings). For every i with 0 <= i < n, buildings[i] has length 3; write start_i = buildings[i][0], end_i = buildings[i][1], height_i = buildings[i][2]. Assume 1 <= n <= 100000, 0 <= start_i < end_i <= 100000000, and 1 <= height_i <= 100000. -/
  theorem spec_1
    (buildings : Slice (alloc.vec.Vec Std.I64))
    (hinput : ValidInput buildings)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r) :
    (∀ v ∈ r.val, v.val.length = 3) ∧
      (∀ k, k < r.val.length → (outRow r k).1 < (outRow r k).2.1) ∧
      (∀ x : ℤ, C buildings x = 0 → outCount r x = 0) ∧
      (∀ x : ℤ, 0 < C buildings x → outCount r x = 1) ∧
      (∀ k, k < r.val.length → ∀ x : ℤ,
        (outRow r k).1 ≤ x → x < (outRow r k).2.1 →
          0 < C buildings x ∧ (outRow r k).2.2 = A buildings x) ∧
      (∀ p q, p < r.val.length → q < r.val.length → p ≠ q →
        ((outRow r p).2.1 = (outRow r q).1 ∨ (outRow r q).2.1 = (outRow r p).1) →
          (outRow r p).2.2 ≠ (outRow r q).2.2) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64))
      (hinput : ValidInput buildings)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r), (∀ v ∈ r.val, v.val.length = 3) ∧
        (∀ k, k < r.val.length → (outRow r k).1 < (outRow r k).2.1) ∧
        (∀ x : ℤ, C buildings x = 0 → outCount r x = 0) ∧
        (∀ x : ℤ, 0 < C buildings x → outCount r x = 1) ∧
        (∀ k, k < r.val.length → ∀ x : ℤ,
          (outRow r k).1 ≤ x → x < (outRow r k).2.1 →
            0 < C buildings x ∧ (outRow r k).2.2 = A buildings x) ∧
        (∀ p q, p < r.val.length → q < r.val.length → p ≠ q →
          ((outRow r p).2.1 = (outRow r q).1 ∨ (outRow r q).2.1 = (outRow r p).1) →
            (outRow r p).2.2 ≠ (outRow r q).2.2)) := by
    sorry

  /-- The function returns a result r (it does not fail: there is no arithmetic overflow, out-of-bounds access, division by zero, or panic).
    Preconditions: Let n = len(buildings). For every i with 0 <= i < n, buildings[i] has length 3; write start_i = buildings[i][0], end_i = buildings[i][1], height_i = buildings[i][2]. Assume 1 <= n <= 100000, 0 <= start_i < end_i <= 100000000, and 1 <= height_i <= 100000. -/
  theorem spec_2
    (buildings : Slice (alloc.vec.Vec Std.I64))
    (hinput : ValidInput buildings) :
    ∃ r, Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64))
      (hinput : ValidInput buildings), ∃ r, Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r) := by
    sorry

  /-- Whenever the function returns a result r, every row [l, r, a] of r is maximal on both sides. Define C(x) as the number of buildings i with start_i <= x < end_i, and for covered x define A(x) = floor(S(x)/C(x)), where S(x) is the sum of height_i over buildings covering x. Then if C(l-1) > 0 we have A(l-1) != a, and if C(r) > 0 we have A(r) != a.
    Preconditions: Let n = len(buildings). For every i with 0 <= i < n, buildings[i] has length 3; write start_i = buildings[i][0], end_i = buildings[i][1], height_i = buildings[i][2]. Assume 1 <= n <= 100000, 0 <= start_i < end_i <= 100000000, and 1 <= height_i <= 100000. -/
  theorem spec_3
    (buildings : Slice (alloc.vec.Vec Std.I64))
    (hinput : ValidInput buildings)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r) :
    ∀ k, k < r.val.length →
      (0 < C buildings ((outRow r k).1 - 1) → A buildings ((outRow r k).1 - 1) ≠ (outRow r k).2.2) ∧
        (0 < C buildings (outRow r k).2.1 → A buildings (outRow r k).2.1 ≠ (outRow r k).2.2) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64))
      (hinput : ValidInput buildings)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r), ∀ k, k < r.val.length →
        (0 < C buildings ((outRow r k).1 - 1) → A buildings ((outRow r k).1 - 1) ≠ (outRow r k).2.2) ∧
          (0 < C buildings (outRow r k).2.1 → A buildings (outRow r k).2.1 ≠ (outRow r k).2.2)) := by
    sorry

  /-- Whenever the function returns a result r, for every row [l, r, a] of r, the left endpoint l is equal to start_i or end_i for some building i, and the right endpoint r is equal to start_i or end_i for some building i. Thus every endpoint belongs to the set {start_i, end_i | 0 <= i < n}.
    Preconditions: Let n = len(buildings). For every i with 0 <= i < n, buildings[i] has length 3; write start_i = buildings[i][0], end_i = buildings[i][1], height_i = buildings[i][2]. Assume 1 <= n <= 100000, 0 <= start_i < end_i <= 100000000, and 1 <= height_i <= 100000. -/
  theorem spec_4
    (buildings : Slice (alloc.vec.Vec Std.I64))
    (hinput : ValidInput buildings)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r) :
    ∀ k, k < r.val.length →
      (∃ i, i < buildings.val.length ∧
          ((outRow r k).1 = startAt buildings i ∨ (outRow r k).1 = endAt buildings i)) ∧
        ∃ i, i < buildings.val.length ∧
          ((outRow r k).2.1 = startAt buildings i ∨ (outRow r k).2.1 = endAt buildings i) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64))
      (hinput : ValidInput buildings)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r), ∀ k, k < r.val.length →
        (∃ i, i < buildings.val.length ∧
            ((outRow r k).1 = startAt buildings i ∨ (outRow r k).1 = endAt buildings i)) ∧
          ∃ i, i < buildings.val.length ∧
            ((outRow r k).2.1 = startAt buildings i ∨ (outRow r k).2.1 = endAt buildings i)) := by
    sorry

  /-- Whenever the function returns a result r, for every row [l, r, a] of r, 1 <= a <= max_{0 <= i < n} height_i. In particular, a is positive and does not exceed the tallest building height.
    Preconditions: Let n = len(buildings). For every i with 0 <= i < n, buildings[i] has length 3; write start_i = buildings[i][0], end_i = buildings[i][1], height_i = buildings[i][2]. Assume 1 <= n <= 100000, 0 <= start_i < end_i <= 100000000, and 1 <= height_i <= 100000. -/
  theorem spec_5
    (buildings : Slice (alloc.vec.Vec Std.I64))
    (hinput : ValidInput buildings)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r) :
    ∀ k, k < r.val.length →
      1 ≤ (outRow r k).2.2 ∧ (outRow r k).2.2 ≤ maxHeight buildings := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64))
      (hinput : ValidInput buildings)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r), ∀ k, k < r.val.length →
        1 ≤ (outRow r k).2.2 ∧ (outRow r k).2.2 ≤ maxHeight buildings) := by
    sorry

  /-- Whenever the function returns a result r, for every row [l, r, a] of r, min_{0 <= i < n} start_i <= l < r <= max_{0 <= i < n} end_i.
    Preconditions: Let n = len(buildings). For every i with 0 <= i < n, buildings[i] has length 3; write start_i = buildings[i][0], end_i = buildings[i][1], height_i = buildings[i][2]. Assume 1 <= n <= 100000, 0 <= start_i < end_i <= 100000000, and 1 <= height_i <= 100000. -/
  theorem spec_6
    (buildings : Slice (alloc.vec.Vec Std.I64))
    (hinput : ValidInput buildings)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r) :
    ∀ k, k < r.val.length →
      minStart buildings ≤ (outRow r k).1 ∧
        (outRow r k).1 < (outRow r k).2.1 ∧
          (outRow r k).2.1 ≤ maxEnd buildings := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64))
      (hinput : ValidInput buildings)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r), ∀ k, k < r.val.length →
        minStart buildings ≤ (outRow r k).1 ∧
          (outRow r k).1 < (outRow r k).2.1 ∧
            (outRow r k).2.1 ≤ maxEnd buildings) := by
    sorry

  /-- Whenever the function returns a result r, let C(x) and A(x) be as follows: C(x) is the number of buildings i with start_i <= x < end_i, and for C(x) > 0, A(x) = floor(S(x)/C(x)) with S(x) the sum of height_i over buildings covering x. Let K be the number of intervals [a, b) with integer a < b such that: (i) C(x) > 0 for every integer x with a <= x < b; (ii) A(x) has the same value c for every such x; (iii) either C(a-1) = 0 or A(a-1) != c; (iv) either C(b) = 0 or A(b) != c. Then len(r) = K, so r has the minimum possible number of segments.
    Preconditions: Let n = len(buildings). For every i with 0 <= i < n, buildings[i] has length 3; write start_i = buildings[i][0], end_i = buildings[i][1], height_i = buildings[i][2]. Assume 1 <= n <= 100000, 0 <= start_i < end_i <= 100000000, and 1 <= height_i <= 100000. -/
  theorem spec_7
    (buildings : Slice (alloc.vec.Vec Std.I64))
    (hinput : ValidInput buildings)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r) :
    r.val.length = numSegments buildings := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64))
      (hinput : ValidInput buildings)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r), r.val.length = numSegments buildings) := by
    sorry

  /-- For any permutation pi of the indices {0,...,n-1}, let buildings_pi be the list whose k-th entry is buildings[pi(k)]. Whenever the function returns r on buildings and r' on buildings_pi, the multiset of triples (l, r, a) appearing as rows of r equals the multiset of triples appearing as rows of r'. Thus the answer depends only on the multiset of buildings, not on their order in the input.
    Preconditions: Let n = len(buildings). For every i with 0 <= i < n, buildings[i] has length 3; write start_i = buildings[i][0], end_i = buildings[i][1], height_i = buildings[i][2]. Assume 1 <= n <= 100000, 0 <= start_i < end_i <= 100000000, and 1 <= height_i <= 100000. -/
  theorem spec_8
    (buildings : Slice (alloc.vec.Vec Std.I64))
    (hinput : ValidInput buildings)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r)
    (buildings' : Slice (alloc.vec.Vec Std.I64))
    (hperm : List.Perm buildings'.val buildings.val)
    (hinput' : ValidInput buildings')
    (r' : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hres' : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings' = ok r') :
    List.Perm (r.val.map rowTriple) (r'.val.map rowTriple) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64))
      (hinput : ValidInput buildings)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings = ok r)
      (buildings' : Slice (alloc.vec.Vec Std.I64))
      (hperm : List.Perm buildings'.val buildings.val)
      (hinput' : ValidInput buildings')
      (r' : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres' : Aegis.AverageHeightOfBuildings.average_height_of_buildings buildings' = ok r'), List.Perm (r.val.map rowTriple) (r'.val.map rowTriple)) := by
    sorry

  end AegisSpec.AverageHeightOfBuildings
