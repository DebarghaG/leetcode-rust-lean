import Aegis.ColorTheArray.Code.Funs

/-!
# Specifications of `Aegis.ColorTheArray.color_the_array`

LeetCode problem `number-of-adjacent-elements-with-the-same-color`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
    open Aegis.ColorTheArray

  namespace AegisSpec.ColorTheArray

  def model (queries : Slice (alloc.vec.Vec I64)) : List (List Int) :=
    queries.val.map (fun v => v.val.map (fun x => x.val))

  def qLen (qs : List (List Int)) (j : Nat) : Nat :=
    (qs.getD j []).length

  def qIdx (qs : List (List Int)) (j : Nat) : Int :=
    (qs.getD j []).getD 0 0

  def qColor (qs : List (List Int)) (j : Nat) : Int :=
    (qs.getD j []).getD 1 0

  def colorState (n : Int) (qs : List (List Int)) : Nat → List Int
    | 0 => List.replicate n.toNat 0
    | j + 1 => (colorState n qs j).set (qIdx qs j).toNat (qColor qs j)

  def prevColor (n : Int) (qs : List (List Int)) (j : Nat) : Int :=
    (colorState n qs j).getD (qIdx qs j).toNat 0

  def sameCount (n : Int) (c : List Int) : Int :=
    Int.ofNat ((List.range (n - 1).toNat).countP (fun i =>
      c.getD i 0 != 0 && c.getD i 0 == c.getD (i + 1) 0))

  def visited (qs : List (List Int)) (j : Nat) (q : Int) : Bool :=
    (List.range (j + 1)).any (fun p => qIdx qs p == q)

  def adjacentIndexCount (n : Int) (qs : List (List Int)) (j : Nat) : Int :=
    Int.ofNat ((List.range (n - 1).toNat).countP (fun i =>
      visited qs j (i : Int) && visited qs j ((i : Int) + 1)))

  def neighborCount (n : Int) (c : List Int) (p : Int) (x : Int) : Int :=
    if x = 0 then 0
    else
      Int.ofNat (List.length ((List.filter
        (fun q : Int => decide (0 ≤ q ∧ q < n ∧ c.getD q.toNat 0 = x))
        ([p - 1, p + 1] : List Int))))

  /-- Let c_0 be the length-n array with c_0[i] = 0 for every 0 <= i < n. For every j with 0 <= j < m, let c_{j+1} be the length-n array obtained from c_j by setting c_{j+1}[queries[j][0]] = queries[j][1] and leaving every other entry unchanged. For an array c of length n, let same(c) be the number of indices i with 0 <= i < n-1 such that c[i] != 0 and c[i] = c[i+1]. The function returns a result r such that len(r) = m and for every j with 0 <= j < m, r[j] = same(c_{j+1}).
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. -/
  theorem spec_1 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000) :
      ∃ r, color_the_array n queries = ok r ∧
        r.val.length = queries.val.length ∧
        ∀ (j : Nat), j < queries.val.length → ∀ (x : I64), r.val[j]? = some x →
          x.val = sameCount n.val (colorState n.val (model queries) (j + 1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000), ∃ r, color_the_array n queries = ok r ∧
          r.val.length = queries.val.length ∧
          ∀ (j : Nat), j < queries.val.length → ∀ (x : I64), r.val[j]? = some x →
            x.val = sameCount n.val (colorState n.val (model queries) (j + 1))) := by
    sorry

  /-- Whenever the standard preconditions hold, the function returns a result r; it does not fail, panic, access an index out of bounds, or overflow a 64-bit integer.
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. -/
  theorem spec_2 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000) :
      ∃ r, color_the_array n queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000), ∃ r, color_the_array n queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = m, where m = len(queries).
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. -/
  theorem spec_3 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000) :
      ∀ r, color_the_array n queries = ok r → r.val.length = queries.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000), ∀ r, color_the_array n queries = ok r → r.val.length = queries.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < m, 0 <= r[j] <= n-1.
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. -/
  theorem spec_4 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000) :
      ∀ r, color_the_array n queries = ok r →
        ∀ (j : Nat), j < queries.val.length → ∀ (x : I64), r.val[j]? = some x →
          0 ≤ x.val ∧ x.val ≤ n.val - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000), ∀ r, color_the_array n queries = ok r →
          ∀ (j : Nat), j < queries.val.length → ∀ (x : I64), r.val[j]? = some x →
            0 ≤ x.val ∧ x.val ≤ n.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < m, let D_j be the set of indices q such that there exists p with 0 <= p <= j and queries[p][0] = q. Then r[j] is at most the number of indices i with 0 <= i < n-1 such that i is in D_j and i+1 is in D_j.
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. -/
  theorem spec_5 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000) :
      ∀ r, color_the_array n queries = ok r →
        ∀ (j : Nat), j < queries.val.length → ∀ (x : I64), r.val[j]? = some x →
          x.val ≤ adjacentIndexCount n.val (model queries) j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000), ∀ r, color_the_array n queries = ok r →
          ∀ (j : Nat), j < queries.val.length → ∀ (x : I64), r.val[j]? = some x →
            x.val ≤ adjacentIndexCount n.val (model queries) j) := by
    sorry

  /-- Whenever the function returns a result r, r[0] = 0.
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. -/
  theorem spec_6 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000) :
      ∀ r, color_the_array n queries = ok r →
        ∀ (x : I64), r.val[0]? = some x → x.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000), ∀ r, color_the_array n queries = ok r →
          ∀ (x : I64), r.val[0]? = some x → x.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < m, r[j] = 0.
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. Assume that for every p and q with 0 <= p < q < m, |queries[p][0] - queries[q][0]| != 1. -/
  theorem spec_7 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000)
      (hsep : ∀ (p q : Nat), p < q → q < queries.val.length →
        (qIdx (model queries) p - qIdx (model queries) q).natAbs ≠ 1) :
      ∀ r, color_the_array n queries = ok r →
        ∀ (j : Nat), j < queries.val.length → ∀ (x : I64), r.val[j]? = some x →
          x.val = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000)
        (hsep : ∀ (p q : Nat), p < q → q < queries.val.length →
          (qIdx (model queries) p - qIdx (model queries) q).natAbs ≠ 1), ∀ r, color_the_array n queries = ok r →
          ∀ (j : Nat), j < queries.val.length → ∀ (x : I64), r.val[j]? = some x →
            x.val = 0) := by
    sorry

  /-- Let c_0, c_1, ... be the color states defined as in the main specification. Whenever the function returns a result r, for every j with 1 <= j < m, if queries[j][1] = c_j[queries[j][0]], then r[j] = r[j-1].
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. -/
  theorem spec_8 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000) :
      ∀ r, color_the_array n queries = ok r →
        ∀ (j : Nat), 1 ≤ j → j < queries.val.length →
          qColor (model queries) j = prevColor n.val (model queries) j →
          ∀ (x y : I64), r.val[j]? = some x → r.val[j - 1]? = some y → x.val = y.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000), ∀ r, color_the_array n queries = ok r →
          ∀ (j : Nat), 1 ≤ j → j < queries.val.length →
            qColor (model queries) j = prevColor n.val (model queries) j →
            ∀ (x y : I64), r.val[j]? = some x → r.val[j - 1]? = some y → x.val = y.val) := by
    sorry

  /-- Let c_0, c_1, ... be the color states defined as in the main specification. For an array c of length n, an index p, and a color x, let L(c,p,x) be the number of q in {p-1, p+1} that satisfy 0 <= q < n and c[q] = x and x != 0. Whenever the function returns a result r, for every j with 1 <= j < m, with idx = queries[j][0], old = c_j[idx], and new = queries[j][1], we have r[j] = r[j-1] + L(c_j, idx, new) - L(c_j, idx, old).
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. -/
  theorem spec_9 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000) :
      ∀ r, color_the_array n queries = ok r →
        ∀ (j : Nat), 1 ≤ j → j < queries.val.length →
          ∀ (x y : I64), r.val[j]? = some x → r.val[j - 1]? = some y →
            x.val = y.val +
                neighborCount n.val (colorState n.val (model queries) j)
                  (qIdx (model queries) j) (qColor (model queries) j) -
              neighborCount n.val (colorState n.val (model queries) j)
                (qIdx (model queries) j) (prevColor n.val (model queries) j) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000), ∀ r, color_the_array n queries = ok r →
          ∀ (j : Nat), 1 ≤ j → j < queries.val.length →
            ∀ (x y : I64), r.val[j]? = some x → r.val[j - 1]? = some y →
              x.val = y.val +
                  neighborCount n.val (colorState n.val (model queries) j)
                    (qIdx (model queries) j) (qColor (model queries) j) -
                neighborCount n.val (colorState n.val (model queries) j)
                  (qIdx (model queries) j) (prevColor n.val (model queries) j)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 1 <= j < m, |r[j] - r[j-1]| <= 2.
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. -/
  theorem spec_10 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000) :
      ∀ r, color_the_array n queries = ok r →
        ∀ (j : Nat), 1 ≤ j → j < queries.val.length →
          ∀ (x y : I64), r.val[j]? = some x → r.val[j - 1]? = some y →
            -2 ≤ x.val - y.val ∧ x.val - y.val ≤ 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000), ∀ r, color_the_array n queries = ok r →
          ∀ (j : Nat), 1 ≤ j → j < queries.val.length →
            ∀ (x y : I64), r.val[j]? = some x → r.val[j - 1]? = some y →
              -2 ≤ x.val - y.val ∧ x.val - y.val ≤ 2) := by
    sorry

  /-- Let c_0, c_1, ... be the color states defined as in the main specification. Whenever the function returns a result r, for every j with 0 <= j < m, r[j] = 0 if and only if there is no index i with 0 <= i < n-1 such that c_{j+1}[i] != 0 and c_{j+1}[i] = c_{j+1}[i+1].
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. -/
  theorem spec_11 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000) :
      ∀ r, color_the_array n queries = ok r →
        ∀ (j : Nat), j < queries.val.length → ∀ (x : I64), r.val[j]? = some x →
          (x.val = 0 ↔ sameCount n.val (colorState n.val (model queries) (j + 1)) = 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000), ∀ r, color_the_array n queries = ok r →
          ∀ (j : Nat), j < queries.val.length → ∀ (x : I64), r.val[j]? = some x →
            (x.val = 0 ↔ sameCount n.val (colorState n.val (model queries) (j + 1)) = 0)) := by
    sorry

  /-- Whenever the function returns a result r, r[j] = n - 1.
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. Assume that for some j with 0 <= j < m and some color x != 0, c_{j+1}[i] = x for every 0 <= i < n, where c_{j+1} is the state after the j-th query as in the main specification. -/
  theorem spec_12 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000) :
      ∀ (r : alloc.vec.Vec I64) (j : Nat) (x : Int), color_the_array n queries = ok r →
        j < queries.val.length → x ≠ 0 →
        (∀ (i : Nat), i < n.val.toNat → (colorState n.val (model queries) (j + 1)).getD i 0 = x) →
        ∀ (y : I64), r.val[j]? = some y → y.val = n.val - 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000), ∀ (r : alloc.vec.Vec I64) (j : Nat) (x : Int), color_the_array n queries = ok r →
          j < queries.val.length → x ≠ 0 →
          (∀ (i : Nat), i < n.val.toNat → (colorState n.val (model queries) (j + 1)).getD i 0 = x) →
          ∀ (y : I64), r.val[j]? = some y → y.val = n.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < m, r[j] equals the number of indices i with 0 <= i < n-1 such that there exist p and q with 0 <= p <= j, 0 <= q <= j, queries[p][0] = i, and queries[q][0] = i+1.
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. Assume there exists a color x with 1 <= x <= 100000 such that queries[p][1] = x for every 0 <= p < m. -/
  theorem spec_13 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000)
      (hcolor : ∃ (x : Int), 1 ≤ x ∧ x ≤ 100000 ∧
        ∀ (p : Nat), p < queries.val.length → qColor (model queries) p = x) :
      ∀ r, color_the_array n queries = ok r →
        ∀ (j : Nat), j < queries.val.length → ∀ (y : I64), r.val[j]? = some y →
          y.val = adjacentIndexCount n.val (model queries) j := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000)
        (hcolor : ∃ (x : Int), 1 ≤ x ∧ x ≤ 100000 ∧
          ∀ (p : Nat), p < queries.val.length → qColor (model queries) p = x), ∀ r, color_the_array n queries = ok r →
          ∀ (j : Nat), j < queries.val.length → ∀ (y : I64), r.val[j]? = some y →
            y.val = adjacentIndexCount n.val (model queries) j) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 1 <= j < m, r[j] >= r[j-1].
    Preconditions: n is an integer with 1 <= n <= 100000; let m = len(queries); 1 <= m <= 100000; for every j with 0 <= j < m, len(queries[j]) = 2, 0 <= queries[j][0] < n, and 1 <= queries[j][1] <= 100000. Assume that for every j with 0 <= j < m, c_j[queries[j][0]] = 0, where c_j is the state before the j-th query as in the main specification. -/
  theorem spec_14 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
      (hq : ∀ (j : Nat), j < queries.val.length →
        qLen (model queries) j = 2 ∧
        0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
        1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000)
      (hzero : ∀ (j : Nat), j < queries.val.length → prevColor n.val (model queries) j = 0) :
      ∀ r, color_the_array n queries = ok r →
        ∀ (j : Nat), 1 ≤ j → j < queries.val.length →
          ∀ (x y : I64), r.val[j]? = some x → r.val[j - 1]? = some y → y.val ≤ x.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hm_lb : 1 ≤ queries.val.length) (hm_ub : queries.val.length ≤ 100000)
        (hq : ∀ (j : Nat), j < queries.val.length →
          qLen (model queries) j = 2 ∧
          0 ≤ qIdx (model queries) j ∧ qIdx (model queries) j < n.val ∧
          1 ≤ qColor (model queries) j ∧ qColor (model queries) j ≤ 100000)
        (hzero : ∀ (j : Nat), j < queries.val.length → prevColor n.val (model queries) j = 0), ∀ r, color_the_array n queries = ok r →
          ∀ (j : Nat), 1 ≤ j → j < queries.val.length →
            ∀ (x y : I64), r.val[j]? = some x → r.val[j - 1]? = some y → y.val ≤ x.val) := by
    sorry

  end AegisSpec.ColorTheArray
