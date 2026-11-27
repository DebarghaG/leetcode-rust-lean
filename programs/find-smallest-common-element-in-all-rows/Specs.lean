import Aegis.SmallestCommonElement.Code.Funs

/-!
# Specifications of `Aegis.SmallestCommonElement.smallest_common_element`

LeetCode problem `find-smallest-common-element-in-all-rows`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SmallestCommonElement

  abbrev Matrix := Slice (alloc.vec.Vec I64)

  def entry (mat : Matrix) (i j : Nat) (hi : i < mat.val.length)
      (hj : j < (mat.val[i]'hi).val.length) : Int :=
    ((mat.val[i]'hi).val[j]'hj).val

  def OccursIn (row : alloc.vec.Vec I64) (x : Int) : Prop :=
    ∃ (j : Nat) (hj : j < row.val.length), (row.val[j]'hj).val = x

  def Common (mat : Matrix) (x : Int) : Prop :=
    ∀ (i : Nat) (hi : i < mat.val.length), OccursIn (mat.val[i]'hi) x

  def IsFirst (row : alloc.vec.Vec I64) (first : Int) : Prop :=
    ∃ v : I64, row.val.head? = some v ∧ v.val = first

  def IsLast (row : alloc.vec.Vec I64) (last : Int) : Prop :=
    ∃ v : I64, row.val.getLast? = some v ∧ v.val = last

  def RowStrictlyIncreasing (row : alloc.vec.Vec I64) : Prop :=
    ∀ (j k : Nat) (hjk : j < k) (hk : k < row.val.length),
      (row.val[j]'(Nat.lt_trans hjk hk)).val < (row.val[k]'hk).val

  /-- Let common(x) mean: for every i with 0 <= i < len(mat), there exists j with 0 <= j < len(mat[i]) and mat[i][j] = x. The function returns a result r and: if there exists some integer x satisfying common(x), then common(r) and for every x satisfying common(x), r <= x; if no integer x satisfies common(x), then r = -1.
    Preconditions: 1 <= len(mat) <= 500; there exists n with 1 <= n <= 500 such that len(mat[i]) = n for every i with 0 <= i < len(mat); for every i with 0 <= i < len(mat) and every j with 0 <= j < len(mat[i]), 1 <= mat[i][j] <= 10000; and every row is strictly increasing, i.e. for every i with 0 <= i < len(mat) and every j,k with 0 <= j < k < len(mat[i]), mat[i][j] < mat[i][k]. -/
  theorem spec_1 (mat : Matrix)
      (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
      (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
        ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
      (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
        (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
      (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)) :
      ∃ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r ∧
        ((∃ x : Int, Common mat x) → Common mat r.val ∧ ∀ x : Int, Common mat x → r.val ≤ x) ∧
        ((¬ ∃ x : Int, Common mat x) → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mat : Matrix)
        (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
        (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
          ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
        (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
          (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
        (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)), ∃ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r ∧
          ((∃ x : Int, Common mat x) → Common mat r.val ∧ ∀ x : Int, Common mat x → r.val ≤ x) ∧
          ((¬ ∃ x : Int, Common mat x) → r.val = -1)) := by
    sorry

  /-- For every mat satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: 1 <= len(mat) <= 500; there exists n with 1 <= n <= 500 such that len(mat[i]) = n for every i with 0 <= i < len(mat); for every i with 0 <= i < len(mat) and every j with 0 <= j < len(mat[i]), 1 <= mat[i][j] <= 10000; and every row is strictly increasing, i.e. for every i with 0 <= i < len(mat) and every j,k with 0 <= j < k < len(mat[i]), mat[i][j] < mat[i][k]. -/
  theorem spec_2 (mat : Matrix)
      (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
      (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
        ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
      (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
        (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
      (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)) :
      ∃ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mat : Matrix)
        (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
        (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
          ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
        (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
          (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
        (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)), ∃ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every i with 0 <= i < len(mat) there exists j with 0 <= j < len(mat[i]) and mat[i][j] = r.
    Preconditions: 1 <= len(mat) <= 500; there exists n with 1 <= n <= 500 such that len(mat[i]) = n for every i with 0 <= i < len(mat); for every i with 0 <= i < len(mat) and every j with 0 <= j < len(mat[i]), 1 <= mat[i][j] <= 10000; and every row is strictly increasing, i.e. for every i with 0 <= i < len(mat) and every j,k with 0 <= j < k < len(mat[i]), mat[i][j] < mat[i][k]. -/
  theorem spec_3 (mat : Matrix)
      (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
      (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
        ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
      (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
        (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
      (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)) :
      ∀ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
        r.val ≠ -1 → Common mat r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mat : Matrix)
        (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
        (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
          ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
        (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
          (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
        (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)), ∀ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
          r.val ≠ -1 → Common mat r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = -1 if and only if there is no integer x such that for every i with 0 <= i < len(mat) there exists j with 0 <= j < len(mat[i]) and mat[i][j] = x.
    Preconditions: 1 <= len(mat) <= 500; there exists n with 1 <= n <= 500 such that len(mat[i]) = n for every i with 0 <= i < len(mat); for every i with 0 <= i < len(mat) and every j with 0 <= j < len(mat[i]), 1 <= mat[i][j] <= 10000; and every row is strictly increasing, i.e. for every i with 0 <= i < len(mat) and every j,k with 0 <= j < k < len(mat[i]), mat[i][j] < mat[i][k]. -/
  theorem spec_4 (mat : Matrix)
      (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
      (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
        ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
      (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
        (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
      (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)) :
      ∀ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
        (r.val = -1 ↔ ¬ ∃ x : Int, Common mat x) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mat : Matrix)
        (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
        (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
          ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
        (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
          (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
        (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)), ∀ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
          (r.val = -1 ↔ ¬ ∃ x : Int, Common mat x)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every integer x such that x occurs in every row (i.e. for every i with 0 <= i < len(mat) there exists j with 0 <= j < len(mat[i]) and mat[i][j] = x), we have r <= x.
    Preconditions: 1 <= len(mat) <= 500; there exists n with 1 <= n <= 500 such that len(mat[i]) = n for every i with 0 <= i < len(mat); for every i with 0 <= i < len(mat) and every j with 0 <= j < len(mat[i]), 1 <= mat[i][j] <= 10000; and every row is strictly increasing, i.e. for every i with 0 <= i < len(mat) and every j,k with 0 <= j < k < len(mat[i]), mat[i][j] < mat[i][k]. -/
  theorem spec_5 (mat : Matrix)
      (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
      (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
        ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
      (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
        (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
      (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)) :
      ∀ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
        r.val ≠ -1 → ∀ x : Int, Common mat x → r.val ≤ x := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mat : Matrix)
        (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
        (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
          ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
        (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
          (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
        (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)), ∀ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
          r.val ≠ -1 → ∀ x : Int, Common mat x → r.val ≤ x) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every i with 0 <= i < len(mat), mat[i][0] <= r <= mat[i][len(mat[i]) - 1].
    Preconditions: 1 <= len(mat) <= 500; there exists n with 1 <= n <= 500 such that len(mat[i]) = n for every i with 0 <= i < len(mat); for every i with 0 <= i < len(mat) and every j with 0 <= j < len(mat[i]), 1 <= mat[i][j] <= 10000; and every row is strictly increasing, i.e. for every i with 0 <= i < len(mat) and every j,k with 0 <= j < k < len(mat[i]), mat[i][j] < mat[i][k]. -/
  theorem spec_6 (mat : Matrix)
      (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
      (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
        ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
      (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
        (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
      (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)) :
      ∀ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
        r.val ≠ -1 →
          ∀ (i : Nat) (hi : i < mat.val.length) (first last : Int),
            IsFirst (mat.val[i]'hi) first → IsLast (mat.val[i]'hi) last →
              first ≤ r.val ∧ r.val ≤ last := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mat : Matrix)
        (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
        (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
          ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
        (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
          (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
        (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)), ∀ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
          r.val ≠ -1 →
            ∀ (i : Nat) (hi : i < mat.val.length) (first last : Int),
              IsFirst (mat.val[i]'hi) first → IsLast (mat.val[i]'hi) last →
                first ≤ r.val ∧ r.val ≤ last) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= 10000.
    Preconditions: 1 <= len(mat) <= 500; there exists n with 1 <= n <= 500 such that len(mat[i]) = n for every i with 0 <= i < len(mat); for every i with 0 <= i < len(mat) and every j with 0 <= j < len(mat[i]), 1 <= mat[i][j] <= 10000; and every row is strictly increasing, i.e. for every i with 0 <= i < len(mat) and every j,k with 0 <= j < k < len(mat[i]), mat[i][j] < mat[i][k]. -/
  theorem spec_7 (mat : Matrix)
      (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
      (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
        ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
      (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
        (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
      (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)) :
      ∀ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 10000) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (mat : Matrix)
        (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
        (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
          ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
        (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
          (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
        (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi)), ∀ r : I64, Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
          r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 10000)) := by
    sorry

  /-- For every mat satisfying the preconditions and every matrix mat' whose rows are exactly the rows of mat in some order (there is a bijection pi on row indices with mat'[i] = mat[pi(i)] for every i), if smallest_common_element(mat) returns r and smallest_common_element(mat') returns r', then r = r'.
    Preconditions: 1 <= len(mat) <= 500; there exists n with 1 <= n <= 500 such that len(mat[i]) = n for every i with 0 <= i < len(mat); for every i with 0 <= i < len(mat) and every j with 0 <= j < len(mat[i]), 1 <= mat[i][j] <= 10000; and every row is strictly increasing, i.e. for every i with 0 <= i < len(mat) and every j,k with 0 <= j < k < len(mat[i]), mat[i][j] < mat[i][k]. -/
  theorem spec_8 (mat mat' : Matrix)
      (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
      (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
        ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
      (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
        (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
      (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi))
      (π : Nat → Nat)
      (h_len' : mat'.val.length = mat.val.length)
      (h_π_maps : ∀ (i : Nat), i < mat.val.length → π i < mat.val.length)
      (h_π_inj : ∀ (i j : Nat), i < mat.val.length → j < mat.val.length → π i = π j → i = j)
      (h_π_surj : ∀ (k : Nat), k < mat.val.length → ∃ i : Nat, i < mat.val.length ∧ π i = k)
      (h_rows : ∀ (i : Nat) (hi : i < mat.val.length),
        (mat'.val[i]'(by omega)).val = (mat.val[π i]'(h_π_maps i hi)).val) :
      ∀ (r r' : I64), Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
        Aegis.SmallestCommonElement.smallest_common_element mat' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (mat mat' : Matrix)
        (h_size : 1 ≤ mat.val.length ∧ mat.val.length ≤ 500)
        (h_shape : ∃ n : Nat, 1 ≤ n ∧ n ≤ 500 ∧
          ∀ (i : Nat) (hi : i < mat.val.length), (mat.val[i]'hi).val.length = n)
        (h_bounds : ∀ (i : Nat) (hi : i < mat.val.length) (j : Nat)
          (hj : j < (mat.val[i]'hi).val.length), 1 ≤ entry mat i j hi hj ∧ entry mat i j hi hj ≤ 10000)
        (h_sorted : ∀ (i : Nat) (hi : i < mat.val.length), RowStrictlyIncreasing (mat.val[i]'hi))
        (π : Nat → Nat)
        (h_len' : mat'.val.length = mat.val.length)
        (h_π_maps : ∀ (i : Nat), i < mat.val.length → π i < mat.val.length)
        (h_π_inj : ∀ (i j : Nat), i < mat.val.length → j < mat.val.length → π i = π j → i = j)
        (h_π_surj : ∀ (k : Nat), k < mat.val.length → ∃ i : Nat, i < mat.val.length ∧ π i = k)
        (h_rows : ∀ (i : Nat) (hi : i < mat.val.length),
          (mat'.val[i]'(by omega)).val = (mat.val[π i]'(h_π_maps i hi)).val), ∀ (r r' : I64), Aegis.SmallestCommonElement.smallest_common_element mat = ok r →
          Aegis.SmallestCommonElement.smallest_common_element mat' = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.SmallestCommonElement
