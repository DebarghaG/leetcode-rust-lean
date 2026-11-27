import Aegis.CountGoodTriplets.Code.Funs

/-!
# Specifications of `Aegis.CountGoodTriplets.count_good_triplets`

LeetCode problem `count-good-triplets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountGoodTriplets

  def elemAt (arr : Aeneas.Std.Slice Aeneas.Std.I64) (i : Nat) : Int :=
    ((arr.val[i]?).map (fun x => x.val)).getD 0

  def choose3 (n : Nat) : Nat := n * (n - 1) * (n - 2) / 6

  def legOK (arr : Aeneas.Std.Slice Aeneas.Std.I64) (tol : Aeneas.Std.I64) (i j : Nat) : Prop :=
    |elemAt arr i - elemAt arr j| ≤ tol.val

  def tripleOK (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
      (i j k : Nat) : Prop :=
    legOK arr a i j ∧ legOK arr b j k ∧ legOK arr c i k

  noncomputable def indexTriples (n : Nat) (P : Nat → Nat → Nat → Prop) :
      Finset (Nat × Nat × Nat) := by
    classical
    exact ((Finset.range n).product ((Finset.range n).product (Finset.range n))).filter
      (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < n ∧ P t.1 t.2.1 t.2.2)

  noncomputable def goodIndexTriples (arr : Aeneas.Std.Slice Aeneas.Std.I64)
      (a b c : Aeneas.Std.I64) :
      Finset (Nat × Nat × Nat) :=
    indexTriples arr.val.length (fun i j k => tripleOK arr a b c i j k)

  noncomputable def numGoodTriples (arr : Aeneas.Std.Slice Aeneas.Std.I64)
      (a b c : Aeneas.Std.I64) : Nat :=
    (goodIndexTriples arr a b c).card

  noncomputable def abIndexTriples (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b : Aeneas.Std.I64) :
      Finset (Nat × Nat × Nat) :=
    indexTriples arr.val.length (fun i j k => legOK arr a i j ∧ legOK arr b j k)

  noncomputable def numABTriples (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b : Aeneas.Std.I64) : Nat :=
    (abIndexTriples arr a b).card

  def freq (arr : Aeneas.Std.Slice Aeneas.Std.I64) (v : Int) : Nat :=
    (arr.val.filter (fun x => x.val = v)).length

  def sumChoose3Freq (arr : Aeneas.Std.Slice Aeneas.Std.I64) : Int :=
    ∑ v ∈ (Finset.range arr.val.length).image (elemAt arr), (choose3 (freq arr v) : Int)

  /-- The function returns a result r, and r equals the number of triples of indices (i,j,k) such that 0 <= i < j < k < len(arr), |arr[i] - arr[j]| <= a, |arr[j] - arr[k]| <= b, and |arr[i] - arr[k]| <= c. Distinct index triples are counted separately even when their corresponding array values are equal.
    Preconditions: len(arr) >= 3, len(arr) <= 100, for every i with 0 <= i < len(arr) we have 0 <= arr[i] <= 1000, and 0 <= a <= 1000, 0 <= b <= 1000, 0 <= c <= 1000. -/
  theorem spec_1 (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
      (h_len_ge : 3 ≤ arr.val.length)
      (h_len_le : arr.val.length ≤ 100)
      (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
      (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
      (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
      (h_c : 0 ≤ c.val ∧ c.val ≤ 1000) :
      ∃ r : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
          r.val = (numGoodTriples arr a b c : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
        (h_len_ge : 3 ≤ arr.val.length)
        (h_len_le : arr.val.length ≤ 100)
        (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
        (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
        (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
        (h_c : 0 ≤ c.val ∧ c.val ≤ 1000), ∃ r : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
            r.val = (numGoodTriples arr a b c : Int)) := by
    sorry

  /-- The function does not fail: there exists an I64 value r such that count_good_triplets arr a b c returns r.
    Preconditions: len(arr) >= 3, len(arr) <= 100, for every i with 0 <= i < len(arr) we have 0 <= arr[i] <= 1000, and 0 <= a <= 1000, 0 <= b <= 1000, 0 <= c <= 1000. -/
  theorem spec_2 (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
      (h_len_ge : 3 ≤ arr.val.length)
      (h_len_le : arr.val.length ≤ 100)
      (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
      (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
      (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
      (h_c : 0 ≤ c.val ∧ c.val ≤ 1000) :
      ∃ r : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
        (h_len_ge : 3 ≤ arr.val.length)
        (h_len_le : arr.val.length ≤ 100)
        (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
        (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
        (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
        (h_c : 0 ≤ c.val ∧ c.val ≤ 1000), ∃ r : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r) := by
    sorry

  /-- The function returns a result r, and 0 <= r <= C(len(arr),3), where C(n,3) = n*(n-1)*(n-2)/6 is the number of index triples 0 <= i < j < k < n.
    Preconditions: len(arr) >= 3, len(arr) <= 100, for every i with 0 <= i < len(arr) we have 0 <= arr[i] <= 1000, and 0 <= a <= 1000, 0 <= b <= 1000, 0 <= c <= 1000. -/
  theorem spec_3 (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
      (h_len_ge : 3 ≤ arr.val.length)
      (h_len_le : arr.val.length ≤ 100)
      (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
      (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
      (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
      (h_c : 0 ≤ c.val ∧ c.val ≤ 1000) :
      ∃ r : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
          0 ≤ r.val ∧ r.val ≤ (choose3 arr.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
        (h_len_ge : 3 ≤ arr.val.length)
        (h_len_le : arr.val.length ≤ 100)
        (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
        (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
        (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
        (h_c : 0 ≤ c.val ∧ c.val ≤ 1000), ∃ r : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
            0 ≤ r.val ∧ r.val ≤ (choose3 arr.val.length : Int)) := by
    sorry

  /-- The function returns a result r, and r = 1 exactly when |arr[0] - arr[1]| <= a, |arr[1] - arr[2]| <= b, and |arr[0] - arr[2]| <= c; otherwise r = 0.
    Preconditions: len(arr) = 3, for every i with 0 <= i < len(arr) we have 0 <= arr[i] <= 1000, and 0 <= a <= 1000, 0 <= b <= 1000, 0 <= c <= 1000. -/
  theorem spec_4 (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
      (h_len : arr.val.length = 3)
      (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
      (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
      (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
      (h_c : 0 ≤ c.val ∧ c.val ≤ 1000) :
      ∃ r : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
          (r.val = 1 ↔ tripleOK arr a b c 0 1 2) ∧
            (r.val = 0 ↔ ¬ tripleOK arr a b c 0 1 2) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
        (h_len : arr.val.length = 3)
        (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
        (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
        (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
        (h_c : 0 ≤ c.val ∧ c.val ≤ 1000), ∃ r : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
            (r.val = 1 ↔ tripleOK arr a b c 0 1 2) ∧
              (r.val = 0 ↔ ¬ tripleOK arr a b c 0 1 2)) := by
    sorry

  /-- The function returns a result r, and r = len(arr)*(len(arr)-1)*(len(arr)-2)/6.
    Preconditions: len(arr) >= 3, len(arr) <= 100, there is an integer v such that arr[i] = v for every i with 0 <= i < len(arr), 0 <= v <= 1000, and 0 <= a <= 1000, 0 <= b <= 1000, 0 <= c <= 1000. -/
  theorem spec_5 (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
      (h_len_ge : 3 ≤ arr.val.length)
      (h_len_le : arr.val.length ≤ 100)
      (v : Int)
      (h_const : ∀ i, i < arr.val.length → elemAt arr i = v)
      (h_v : 0 ≤ v ∧ v ≤ 1000)
      (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
      (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
      (h_c : 0 ≤ c.val ∧ c.val ≤ 1000) :
      ∃ r : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
          r.val = (arr.val.length * (arr.val.length - 1) * (arr.val.length - 2) / 6 : Nat) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
        (h_len_ge : 3 ≤ arr.val.length)
        (h_len_le : arr.val.length ≤ 100)
        (v : Int)
        (h_const : ∀ i, i < arr.val.length → elemAt arr i = v)
        (h_v : 0 ≤ v ∧ v ≤ 1000)
        (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
        (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
        (h_c : 0 ≤ c.val ∧ c.val ≤ 1000), ∃ r : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
            r.val = (arr.val.length * (arr.val.length - 1) * (arr.val.length - 2) / 6 : Nat)) := by
    sorry

  /-- For every integer v, let f(v) be the number of indices i with 0 <= i < len(arr) and arr[i] = v. The function returns a result r, and r = sum over all integers v of f(v)*(f(v)-1)*(f(v)-2)/6.
    Preconditions: len(arr) >= 3, len(arr) <= 100, for every i with 0 <= i < len(arr) we have 0 <= arr[i] <= 1000, and a = 0, b = 0, c = 0. -/
  theorem spec_6 (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
      (h_len_ge : 3 ≤ arr.val.length)
      (h_len_le : arr.val.length ≤ 100)
      (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
      (h_a : a.val = 0)
      (h_b : b.val = 0)
      (h_c : c.val = 0) :
      ∃ r : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
          r.val = sumChoose3Freq arr := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
        (h_len_ge : 3 ≤ arr.val.length)
        (h_len_le : arr.val.length ≤ 100)
        (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
        (h_a : a.val = 0)
        (h_b : b.val = 0)
        (h_c : c.val = 0), ∃ r : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
            r.val = sumChoose3Freq arr) := by
    sorry

  /-- The function returns a result r, and r equals the number of triples of indices (i,j,k) such that 0 <= i < j < k < len(arr), |arr[i] - arr[j]| <= a, and |arr[j] - arr[k]| <= b.
    Preconditions: len(arr) >= 3, len(arr) <= 100, for every i with 0 <= i < len(arr) we have 0 <= arr[i] <= 1000, 0 <= a <= 1000, 0 <= b <= 1000, and c = 1000. -/
  theorem spec_7 (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
      (h_len_ge : 3 ≤ arr.val.length)
      (h_len_le : arr.val.length ≤ 100)
      (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
      (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
      (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
      (h_c : c.val = 1000) :
      ∃ r : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
          r.val = (numABTriples arr a b : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
        (h_len_ge : 3 ≤ arr.val.length)
        (h_len_le : arr.val.length ≤ 100)
        (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
        (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
        (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
        (h_c : c.val = 1000), ∃ r : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
            r.val = (numABTriples arr a b : Int)) := by
    sorry

  /-- If count_good_triplets arr a1 b1 c1 returns r1 and count_good_triplets arr a2 b2 c2 returns r2, then r1 <= r2.
    Preconditions: len(arr) >= 3, len(arr) <= 100, for every i with 0 <= i < len(arr) we have 0 <= arr[i] <= 1000, and each of a1,b1,c1,a2,b2,c2 lies in [0,1000], with a1 <= a2, b1 <= b2, and c1 <= c2. -/
  theorem spec_8 (arr : Aeneas.Std.Slice Aeneas.Std.I64)
      (a1 b1 c1 a2 b2 c2 : Aeneas.Std.I64)
      (h_len_ge : 3 ≤ arr.val.length)
      (h_len_le : arr.val.length ≤ 100)
      (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
      (h_a1 : 0 ≤ a1.val ∧ a1.val ≤ 1000)
      (h_b1 : 0 ≤ b1.val ∧ b1.val ≤ 1000)
      (h_c1 : 0 ≤ c1.val ∧ c1.val ≤ 1000)
      (h_a2 : 0 ≤ a2.val ∧ a2.val ≤ 1000)
      (h_b2 : 0 ≤ b2.val ∧ b2.val ≤ 1000)
      (h_c2 : 0 ≤ c2.val ∧ c2.val ≤ 1000)
      (h_a : a1.val ≤ a2.val)
      (h_b : b1.val ≤ b2.val)
      (h_c : c1.val ≤ c2.val) :
      ∀ r1 r2 : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a1 b1 c1 = ok r1 →
          Aegis.CountGoodTriplets.count_good_triplets arr a2 b2 c2 = ok r2 →
            r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Aeneas.Std.Slice Aeneas.Std.I64)
        (a1 b1 c1 a2 b2 c2 : Aeneas.Std.I64)
        (h_len_ge : 3 ≤ arr.val.length)
        (h_len_le : arr.val.length ≤ 100)
        (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
        (h_a1 : 0 ≤ a1.val ∧ a1.val ≤ 1000)
        (h_b1 : 0 ≤ b1.val ∧ b1.val ≤ 1000)
        (h_c1 : 0 ≤ c1.val ∧ c1.val ≤ 1000)
        (h_a2 : 0 ≤ a2.val ∧ a2.val ≤ 1000)
        (h_b2 : 0 ≤ b2.val ∧ b2.val ≤ 1000)
        (h_c2 : 0 ≤ c2.val ∧ c2.val ≤ 1000)
        (h_a : a1.val ≤ a2.val)
        (h_b : b1.val ≤ b2.val)
        (h_c : c1.val ≤ c2.val), ∀ r1 r2 : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a1 b1 c1 = ok r1 →
            Aegis.CountGoodTriplets.count_good_triplets arr a2 b2 c2 = ok r2 →
              r1.val ≤ r2.val) := by
    sorry

  /-- The function returns results r and s for (arr,a,b,c) and (arr2,a,b,c) respectively, and r = s.
    Preconditions: len(arr) >= 3, len(arr) <= 100, for every i with 0 <= i < len(arr) we have 0 <= arr[i] <= 1000, 0 <= a <= 1000, 0 <= b <= 1000, 0 <= c <= 1000, arr2 has the same length as arr, for every i with 0 <= i < len(arr) we have 0 <= arr2[i] <= 1000, and there exists an integer t such that arr2[i] = arr[i] + t for every i with 0 <= i < len(arr). -/
  theorem spec_9 (arr arr2 : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
      (h_len_ge : 3 ≤ arr.val.length)
      (h_len_le : arr.val.length ≤ 100)
      (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
      (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
      (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
      (h_c : 0 ≤ c.val ∧ c.val ≤ 1000)
      (h_len2 : arr2.val.length = arr.val.length)
      (h_arr2 : ∀ i, i < arr.val.length → 0 ≤ elemAt arr2 i ∧ elemAt arr2 i ≤ 1000)
      (h_shift : ∃ t : Int, ∀ i, i < arr.val.length → elemAt arr2 i = elemAt arr i + t) :
      ∃ r s : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
          Aegis.CountGoodTriplets.count_good_triplets arr2 a b c = ok s ∧
            r.val = s.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr arr2 : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
        (h_len_ge : 3 ≤ arr.val.length)
        (h_len_le : arr.val.length ≤ 100)
        (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
        (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
        (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
        (h_c : 0 ≤ c.val ∧ c.val ≤ 1000)
        (h_len2 : arr2.val.length = arr.val.length)
        (h_arr2 : ∀ i, i < arr.val.length → 0 ≤ elemAt arr2 i ∧ elemAt arr2 i ≤ 1000)
        (h_shift : ∃ t : Int, ∀ i, i < arr.val.length → elemAt arr2 i = elemAt arr i + t), ∃ r s : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
            Aegis.CountGoodTriplets.count_good_triplets arr2 a b c = ok s ∧
              r.val = s.val) := by
    sorry

  /-- The function returns r for (arr,a,b,c) and s for (arr2,b,a,c), and r = s.
    Preconditions: len(arr) = n with 3 <= n <= 100, for every i with 0 <= i < n we have 0 <= arr[i] <= 1000, 0 <= a <= 1000, 0 <= b <= 1000, 0 <= c <= 1000, arr2 has length n, and arr2[i] = arr[n-1-i] for every i with 0 <= i < n. -/
  theorem spec_10 (arr arr2 : Aeneas.Std.Slice Aeneas.Std.I64) (n : Nat)
      (a b c : Aeneas.Std.I64)
      (h_len : arr.val.length = n)
      (h_n_ge : 3 ≤ n)
      (h_n_le : n ≤ 100)
      (h_arr : ∀ i, i < n → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
      (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
      (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
      (h_c : 0 ≤ c.val ∧ c.val ≤ 1000)
      (h_len2 : arr2.val.length = n)
      (h_rev : ∀ i, i < n → elemAt arr2 i = elemAt arr (n - 1 - i)) :
      ∃ r s : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
          Aegis.CountGoodTriplets.count_good_triplets arr2 b a c = ok s ∧
            r.val = s.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr arr2 : Aeneas.Std.Slice Aeneas.Std.I64) (n : Nat)
        (a b c : Aeneas.Std.I64)
        (h_len : arr.val.length = n)
        (h_n_ge : 3 ≤ n)
        (h_n_le : n ≤ 100)
        (h_arr : ∀ i, i < n → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
        (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
        (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
        (h_c : 0 ≤ c.val ∧ c.val ≤ 1000)
        (h_len2 : arr2.val.length = n)
        (h_rev : ∀ i, i < n → elemAt arr2 i = elemAt arr (n - 1 - i)), ∃ r s : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
            Aegis.CountGoodTriplets.count_good_triplets arr2 b a c = ok s ∧
              r.val = s.val) := by
    sorry

  /-- The function returns a result r, and r > 0 if and only if there exist indices i,j,k such that 0 <= i < j < k < len(arr), |arr[i] - arr[j]| <= a, |arr[j] - arr[k]| <= b, and |arr[i] - arr[k]| <= c; equivalently, r = 0 exactly when no such index triple exists.
    Preconditions: len(arr) >= 3, len(arr) <= 100, for every i with 0 <= i < len(arr) we have 0 <= arr[i] <= 1000, and 0 <= a <= 1000, 0 <= b <= 1000, 0 <= c <= 1000. -/
  theorem spec_11 (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
      (h_len_ge : 3 ≤ arr.val.length)
      (h_len_le : arr.val.length ≤ 100)
      (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
      (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
      (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
      (h_c : 0 ≤ c.val ∧ c.val ≤ 1000) :
      ∃ r : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
          (0 < r.val ↔ ∃ i j k : Nat,
            i < j ∧ j < k ∧ k < arr.val.length ∧ tripleOK arr a b c i j k) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
        (h_len_ge : 3 ≤ arr.val.length)
        (h_len_le : arr.val.length ≤ 100)
        (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
        (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
        (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
        (h_c : 0 ≤ c.val ∧ c.val ≤ 1000), ∃ r : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
            (0 < r.val ↔ ∃ i j k : Nat,
              i < j ∧ j < k ∧ k < arr.val.length ∧ tripleOK arr a b c i j k)) := by
    sorry

  /-- Let M be the number of triples of indices (i,j,k) such that 0 <= i < j < k < len(arr), |arr[i] - arr[j]| <= a, and |arr[j] - arr[k]| <= b. The function returns a result r, and r <= M.
    Preconditions: len(arr) >= 3, len(arr) <= 100, for every i with 0 <= i < len(arr) we have 0 <= arr[i] <= 1000, and 0 <= a <= 1000, 0 <= b <= 1000, 0 <= c <= 1000. -/
  theorem spec_12 (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
      (h_len_ge : 3 ≤ arr.val.length)
      (h_len_le : arr.val.length ≤ 100)
      (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
      (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
      (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
      (h_c : 0 ≤ c.val ∧ c.val ≤ 1000) :
      ∃ r : Aeneas.Std.I64,
        Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
          r.val ≤ (numABTriples arr a b : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Aeneas.Std.Slice Aeneas.Std.I64) (a b c : Aeneas.Std.I64)
        (h_len_ge : 3 ≤ arr.val.length)
        (h_len_le : arr.val.length ≤ 100)
        (h_arr : ∀ i, i < arr.val.length → 0 ≤ elemAt arr i ∧ elemAt arr i ≤ 1000)
        (h_a : 0 ≤ a.val ∧ a.val ≤ 1000)
        (h_b : 0 ≤ b.val ∧ b.val ≤ 1000)
        (h_c : 0 ≤ c.val ∧ c.val ≤ 1000), ∃ r : Aeneas.Std.I64,
          Aegis.CountGoodTriplets.count_good_triplets arr a b c = ok r ∧
            r.val ≤ (numABTriples arr a b : Int)) := by
    sorry

  end AegisSpec.CountGoodTriplets
