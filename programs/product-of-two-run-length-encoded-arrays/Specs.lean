import Aegis.FindRleArray.Code.Funs

/-!
# Specifications of `Aegis.FindRleArray.find_rle_array`

LeetCode problem `product-of-two-run-length-encoded-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindRleArray

open Aegis.FindRleArray

abbrev Enc := Slice (alloc.vec.Vec Std.I64)

abbrev EncOut := alloc.vec.Vec (alloc.vec.Vec Std.I64)

def rowVals (v : alloc.vec.Vec Std.I64) : List Int :=
  v.slice.list.toList.map (fun x => x.val)

def row (enc : Enc) (i : Nat) : List Int :=
  (enc.list.toList.map rowVals)[i]?.getD []

def nthVal (r : List Int) (k : Nat) : Int :=
  (r[k]?).getD 0

def valAt (enc : Enc) (i : Nat) : Int := nthVal (row enc i) 0

def freqAt (enc : Enc) (i : Nat) : Int := nthVal (row enc i) 1

def ValidRow (r : List Int) : Prop :=
  r.length = 2 ∧ 1 ≤ nthVal r 0 ∧ nthVal r 0 ≤ 10000 ∧
    1 ≤ nthVal r 1 ∧ nthVal r 1 ≤ 10000

def totalFreq (enc : Enc) : Int :=
  ((List.range enc.leng).map (fun i => freqAt enc i)).sum

def expand (enc : Enc) : List Int :=
  (List.range enc.leng).flatMap (fun i =>
    List.replicate (freqAt enc i).toNat (valAt enc i))

def prod (enc1 enc2 : Enc) : List Int :=
  (expand enc1).zipWith (fun a b => a * b) (expand enc2)

/-- Define L = sum_{i=0}^{len(encoded1)-1} encoded1[i][1] (which equals sum_{j=0}^{len(encoded2)-1} encoded2[j][1] by the precondition). For an encoded array enc, define expand(enc) as the array of length sum_{i} enc[i][1] such that for each i and each t with 0 <= t < enc[i][1], expand(enc)[sum_{k<i} enc[k][1] + t] = enc[i][0]. Define prod as the array of length L with prod[t] = expand(encoded1)[t] * expand(encoded2)[t] for 0 <= t < L. The function returns a result r such that: (1) for every k with 0 <= k < len(r), len(r[k]) = 2; (2) for every k with 0 <= k < len(r), r[k][1] >= 1; (3) for every k with 0 <= k < len(r)-1, r[k][0] != r[k+1][0]; (4) expand(r) = prod; (5) len(r) is the minimum possible length among all arrays satisfying (1)-(4).
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_1 (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2) :
    ∃ r : EncOut,
      find_rle_array encoded1 encoded2 = ok r ∧
      (∀ k, k < r.slice.leng → (row r.slice k).length = 2) ∧
      (∀ k, k < r.slice.leng → 1 ≤ freqAt r.slice k) ∧
      (∀ k, k + 1 < r.slice.leng → valAt r.slice k ≠ valAt r.slice (k + 1)) ∧
      expand r.slice = prod encoded1 encoded2 ∧
      (∀ c : EncOut,
        (∀ k, k < c.slice.leng → (row c.slice k).length = 2) →
        (∀ k, k < c.slice.leng → 1 ≤ freqAt c.slice k) →
        (∀ k, k + 1 < c.slice.leng → valAt c.slice k ≠ valAt c.slice (k + 1)) →
        expand c.slice = prod encoded1 encoded2 →
        r.slice.leng ≤ c.slice.leng) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2), ∃ r : EncOut,
      find_rle_array encoded1 encoded2 = ok r ∧
      (∀ k, k < r.slice.leng → (row r.slice k).length = 2) ∧
      (∀ k, k < r.slice.leng → 1 ≤ freqAt r.slice k) ∧
      (∀ k, k + 1 < r.slice.leng → valAt r.slice k ≠ valAt r.slice (k + 1)) ∧
      expand r.slice = prod encoded1 encoded2 ∧
      (∀ c : EncOut,
        (∀ k, k < c.slice.leng → (row c.slice k).length = 2) →
        (∀ k, k < c.slice.leng → 1 ≤ freqAt c.slice k) →
        (∀ k, k + 1 < c.slice.leng → valAt c.slice k ≠ valAt c.slice (k + 1)) →
        expand c.slice = prod encoded1 encoded2 →
        r.slice.leng ≤ c.slice.leng)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow).
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_2 (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2) :
    ∃ r : EncOut, find_rle_array encoded1 encoded2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2), ∃ r : EncOut, find_rle_array encoded1 encoded2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(r), len(r[k]) = 2.
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_3 (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2) :
    ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      ∀ k, k < r.slice.leng → (row r.slice k).length = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2), ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      ∀ k, k < r.slice.leng → (row r.slice k).length = 2) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(r), 1 <= r[k][1] <= L, where L = sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1].
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_4 (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2) :
    ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      ∀ k, k < r.slice.leng →
        1 ≤ freqAt r.slice k ∧ freqAt r.slice k ≤ totalFreq encoded1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2), ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      ∀ k, k < r.slice.leng →
        1 ≤ freqAt r.slice k ∧ freqAt r.slice k ≤ totalFreq encoded1) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(r), 1 <= r[k][0] <= 100000000.
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_5 (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2) :
    ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      ∀ k, k < r.slice.leng →
        1 ≤ valAt r.slice k ∧ valAt r.slice k ≤ 100000000 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2), ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      ∀ k, k < r.slice.leng →
        1 ≤ valAt r.slice k ∧ valAt r.slice k ≤ 100000000) := by
  sorry

/-- Whenever the function returns a result r, sum_{k=0}^{len(r)-1} r[k][1] = L, where L = sum_{i=0}^{len(encoded1)-1} encoded1[i][1] (which equals sum_{j=0}^{len(encoded2)-1} encoded2[j][1]).
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_6 (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2) :
    ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      totalFreq r.slice = totalFreq encoded1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2), ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      totalFreq r.slice = totalFreq encoded1) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(r), there exist indices i with 0 <= i < len(encoded1) and j with 0 <= j < len(encoded2) such that r[k][0] = encoded1[i][0] * encoded2[j][0].
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_7 (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2) :
    ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      ∀ k, k < r.slice.leng →
        ∃ i, i < encoded1.leng ∧ ∃ j, j < encoded2.leng ∧
          valAt r.slice k = valAt encoded1 i * valAt encoded2 j := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2), ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      ∀ k, k < r.slice.leng →
        ∃ i, i < encoded1.leng ∧ ∃ j, j < encoded2.leng ∧
          valAt r.slice k = valAt encoded1 i * valAt encoded2 j) := by
  sorry

/-- For all encoded1, encoded2, encoded1', and encoded2' satisfying the preconditions, if find_rle_array(encoded1, encoded2) = Ok r and find_rle_array(encoded1', encoded2') = Ok r', then len(r) = len(r') and r[k] = r'[k] for every k with 0 <= k < len(r).
  Preconditions: encoded1, encoded2, encoded1', and encoded2' are slices of Vec<i64>. For each of the pairs (encoded1, encoded2) and (encoded1', encoded2'): 1 <= len(first) <= 100000, 1 <= len(second) <= 100000; for every i with 0 <= i < len(first), len(first[i]) = 2, 1 <= first[i][0] <= 10000, and 1 <= first[i][1] <= 10000; for every j with 0 <= j < len(second), len(second[j]) = 2, 1 <= second[j][0] <= 10000, and 1 <= second[j][1] <= 10000; and sum_{i=0}^{len(first)-1} first[i][1] = sum_{j=0}^{len(second)-1} second[j][1]. Additionally, expand(encoded1') = expand(encoded1) and expand(encoded2') = expand(encoded2), where for any encoded array enc, expand(enc) is the array of length sum_i enc[i][1] such that for each i and each t with 0 <= t < enc[i][1], expand(enc)[sum_{k<i} enc[k][1] + t] = enc[i][0]. -/
theorem spec_8 (encoded1 encoded2 encoded1' encoded2' : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2)
    (h1'_ne : 1 ≤ encoded1'.leng) (h2'_ne : 1 ≤ encoded2'.leng)
    (h1'_le : encoded1'.leng ≤ 100000) (h2'_le : encoded2'.leng ≤ 100000)
    (h1'_row : ∀ i, i < encoded1'.leng → ValidRow (row encoded1' i))
    (h2'_row : ∀ j, j < encoded2'.leng → ValidRow (row encoded2' j))
    (h_sum' : totalFreq encoded1' = totalFreq encoded2')
    (h_exp1 : expand encoded1' = expand encoded1)
    (h_exp2 : expand encoded2' = expand encoded2) :
    ∀ r r' : EncOut,
      find_rle_array encoded1 encoded2 = ok r →
      find_rle_array encoded1' encoded2' = ok r' →
      r.slice.leng = r'.slice.leng ∧
        ∀ k, k < r.slice.leng → row r.slice k = row r'.slice k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (encoded1 encoded2 encoded1' encoded2' : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2)
    (h1'_ne : 1 ≤ encoded1'.leng) (h2'_ne : 1 ≤ encoded2'.leng)
    (h1'_le : encoded1'.leng ≤ 100000) (h2'_le : encoded2'.leng ≤ 100000)
    (h1'_row : ∀ i, i < encoded1'.leng → ValidRow (row encoded1' i))
    (h2'_row : ∀ j, j < encoded2'.leng → ValidRow (row encoded2' j))
    (h_sum' : totalFreq encoded1' = totalFreq encoded2')
    (h_exp1 : expand encoded1' = expand encoded1)
    (h_exp2 : expand encoded2' = expand encoded2), ∀ r r' : EncOut,
      find_rle_array encoded1 encoded2 = ok r →
      find_rle_array encoded1' encoded2' = ok r' →
      r.slice.leng = r'.slice.leng ∧
        ∀ k, k < r.slice.leng → row r.slice k = row r'.slice k) := by
  sorry

/-- Let L = sum_{i=0}^{len(encoded1)-1} encoded1[i][1] (which equals sum_{j=0}^{len(encoded2)-1} encoded2[j][1]) and for any encoded array enc let expand(enc) be the array formed by replacing each pair [v, f] with f copies of v. If there exists a value c such that for every t with 0 <= t < L, expand(encoded1)[t] * expand(encoded2)[t] = c, then whenever the function returns a result r, len(r) = 1, r[0][0] = c, and r[0][1] = L.
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_9 (encoded1 encoded2 : Enc) (c : Int)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2)
    (h_const : ∀ t : Nat, (t : Int) < totalFreq encoded1 →
      (prod encoded1 encoded2)[t]? = some c) :
    ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      r.slice.leng = 1 ∧ valAt r.slice 0 = c ∧ freqAt r.slice 0 = totalFreq encoded1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (encoded1 encoded2 : Enc) (c : Int)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2)
    (h_const : ∀ t : Nat, (t : Int) < totalFreq encoded1 →
      (prod encoded1 encoded2)[t]? = some c), ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      r.slice.leng = 1 ∧ valAt r.slice 0 = c ∧ freqAt r.slice 0 = totalFreq encoded1) := by
  sorry

/-- Whenever the function returns a result r, r[0][0] = encoded1[0][0] * encoded2[0][0].
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_10 (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2) :
    ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      valAt r.slice 0 = valAt encoded1 0 * valAt encoded2 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2), ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      valAt r.slice 0 = valAt encoded1 0 * valAt encoded2 0) := by
  sorry

/-- Whenever the function returns a result r, r[len(r)-1][0] = encoded1[len(encoded1)-1][0] * encoded2[len(encoded2)-1][0].
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_11 (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2) :
    ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      valAt r.slice (r.slice.leng - 1) =
        valAt encoded1 (encoded1.leng - 1) * valAt encoded2 (encoded2.leng - 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2), ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      valAt r.slice (r.slice.leng - 1) =
        valAt encoded1 (encoded1.leng - 1) * valAt encoded2 (encoded2.leng - 1)) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= len(encoded1) + len(encoded2) - 1.
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_12 (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2) :
    ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      r.slice.leng ≤ encoded1.leng + encoded2.leng - 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2), ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      r.slice.leng ≤ encoded1.leng + encoded2.leng - 1) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(r)-1, r[k][0] != r[k+1][0].
  Preconditions: len(encoded1) >= 1, len(encoded2) >= 1, len(encoded1) <= 100000, len(encoded2) <= 100000. For every i with 0 <= i < len(encoded1), len(encoded1[i]) = 2 and 1 <= encoded1[i][0] <= 10000 and 1 <= encoded1[i][1] <= 10000. For every j with 0 <= j < len(encoded2), len(encoded2[j]) = 2 and 1 <= encoded2[j][0] <= 10000 and 1 <= encoded2[j][1] <= 10000. sum_{i=0}^{len(encoded1)-1} encoded1[i][1] = sum_{j=0}^{len(encoded2)-1} encoded2[j][1]. -/
theorem spec_13 (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2) :
    ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      ∀ k, k + 1 < r.slice.leng → valAt r.slice k ≠ valAt r.slice (k + 1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (encoded1 encoded2 : Enc)
    (h1_ne : 1 ≤ encoded1.leng) (h2_ne : 1 ≤ encoded2.leng)
    (h1_le : encoded1.leng ≤ 100000) (h2_le : encoded2.leng ≤ 100000)
    (h1_row : ∀ i, i < encoded1.leng → ValidRow (row encoded1 i))
    (h2_row : ∀ j, j < encoded2.leng → ValidRow (row encoded2 j))
    (h_sum : totalFreq encoded1 = totalFreq encoded2), ∀ r : EncOut, find_rle_array encoded1 encoded2 = ok r →
      ∀ k, k + 1 < r.slice.leng → valAt r.slice k ≠ valAt r.slice (k + 1)) := by
  sorry

end AegisSpec.FindRleArray
