import Aegis.MissingNumber.Code.Funs

/-!
# Specifications of `Aegis.MissingNumber.missing_number`

LeetCode problem `missing-number-in-arithmetic-progression`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.MissingNumber

  namespace AegisSpec.MissingNumber

  def elem (arr : Slice Std.I64) (i : Nat) : Int :=
    match arr.val[i]? with
    | some x => x.val
    | none => 0

  theorem elem_eq (arr : Slice Std.I64) (i : Nat) (h : i < arr.val.length) :
      elem arr i = (arr.val[i]'h).val := by
    simp [elem, List.getElem?_eq_getElem h]

  def total (arr : Slice Std.I64) : Int := (arr.val.map fun x => x.val).sum

  def IsValid (arr : Slice Std.I64) : Prop :=
    ∃ (d : Int) (k : Nat),
      1 ≤ k ∧ k < arr.val.length ∧
        (∀ i : Nat, i < k → elem arr i = elem arr 0 + (i : Int) * d) ∧
        (∀ i : Nat, k ≤ i → i < arr.val.length →
          elem arr i = elem arr 0 + ((i : Int) + 1) * d)

  def step3 (arr : Slice Std.I64) : Int := (elem arr 2 - elem arr 0) / 3

  def step (arr : Slice Std.I64) (n : Nat) : Int :=
    (elem arr (n - 1) - elem arr 0) / (n : Int)

  def reverseSlice (arr : Slice Std.I64) : Slice Std.I64 :=
    ⟨arr.val.reverse.length, Aeneas.Data.ListN.ListN.fromList arr.val.reverse, by
      simp only [Aeneas.Std.Slice.val, List.length_reverse,
        Aeneas.Data.ListN.ListN_length]
      exact arr.bound⟩

  /-- The function returns a result r and there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, for every i with k <= i < n arr[i] = arr[0] + (i+1)*d, and r = arr[0] + k*d.
    Preconditions: Let n = len(arr). The input satisfies 3 <= n <= 1000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. -/
  theorem spec_1 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr) :
      ∃ r : Std.I64, missing_number arr = ok r ∧
        ∃ (d : Int) (k : Nat),
          1 ≤ k ∧ k < n ∧
            (∀ i : Nat, i < k → elem arr i = elem arr 0 + (i : Int) * d) ∧
            (∀ i : Nat, k ≤ i → i < n →
              elem arr i = elem arr 0 + ((i : Int) + 1) * d) ∧
            r.val = elem arr 0 + (k : Int) * d := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr), ∃ r : Std.I64, missing_number arr = ok r ∧
          ∃ (d : Int) (k : Nat),
            1 ≤ k ∧ k < n ∧
              (∀ i : Nat, i < k → elem arr i = elem arr 0 + (i : Int) * d) ∧
              (∀ i : Nat, k ≤ i → i < n →
                elem arr i = elem arr 0 + ((i : Int) + 1) * d) ∧
              r.val = elem arr 0 + (k : Int) * d) := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: Let n = len(arr). The input satisfies 3 <= n <= 1000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. -/
  theorem spec_2 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr) :
      ∃ r : Std.I64, missing_number arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr), ∃ r : Std.I64, missing_number arr = ok r) := by
    sorry

  /-- The function returns a result r and min(arr[0], arr[n-1]) <= r <= max(arr[0], arr[n-1]).
    Preconditions: Let n = len(arr). The input satisfies 3 <= n <= 1000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. -/
  theorem spec_3 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr) :
      ∃ r : Std.I64, missing_number arr = ok r ∧
        min (elem arr 0) (elem arr (n - 1)) ≤ r.val ∧
        r.val ≤ max (elem arr 0) (elem arr (n - 1)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr), ∃ r : Std.I64, missing_number arr = ok r ∧
          min (elem arr 0) (elem arr (n - 1)) ≤ r.val ∧
          r.val ≤ max (elem arr 0) (elem arr (n - 1))) := by
    sorry

  /-- The function returns a result r and r = arr[0].
    Preconditions: Let n = len(arr). The input satisfies 3 <= n <= 1000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. Additionally, for every i and j with 0 <= i < n and 0 <= j < n, arr[i] = arr[j]. -/
  theorem spec_4 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr)
      (hconst : ∀ i j : Nat, i < n → j < n → elem arr i = elem arr j) :
      ∃ r : Std.I64, missing_number arr = ok r ∧ r.val = elem arr 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr)
        (hconst : ∀ i j : Nat, i < n → j < n → elem arr i = elem arr j), ∃ r : Std.I64, missing_number arr = ok r ∧ r.val = elem arr 0) := by
    sorry

  /-- The function returns a result r and for every i with 0 <= i < n, r != arr[i].
    Preconditions: Let n = len(arr). The input satisfies 3 <= n <= 1000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. Additionally, there exist i and j with 0 <= i < n and 0 <= j < n such that arr[i] != arr[j]. -/
  theorem spec_5 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr)
      (hne : ∃ i j : Nat, i < n ∧ j < n ∧ elem arr i ≠ elem arr j) :
      ∃ r : Std.I64, missing_number arr = ok r ∧
        ∀ i : Nat, i < n → r.val ≠ elem arr i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr)
        (hne : ∃ i j : Nat, i < n ∧ j < n ∧ elem arr i ≠ elem arr j), ∃ r : Std.I64, missing_number arr = ok r ∧
          ∀ i : Nat, i < n → r.val ≠ elem arr i) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} arr[i]. The function returns a result r and 2*r = (n+1)*(arr[0] + arr[n-1]) - 2*S.
    Preconditions: Let n = len(arr). The input satisfies 3 <= n <= 1000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. -/
  theorem spec_6 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr) :
      ∃ r : Std.I64, missing_number arr = ok r ∧
        2 * r.val = ((n : Int) + 1) * (elem arr 0 + elem arr (n - 1)) -
          2 * total arr := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr), ∃ r : Std.I64, missing_number arr = ok r ∧
          2 * r.val = ((n : Int) + 1) * (elem arr 0 + elem arr (n - 1)) -
            2 * total arr) := by
    sorry

  /-- Let d = (arr[2] - arr[0]) / 3, which is an integer by validity. The function returns a result r and: if d = 0 then r = arr[0]; otherwise r is the unique element of {arr[0] + d, arr[0] + 2*d} that is not equal to arr[1].
    Preconditions: Let n = len(arr). The input satisfies n = 3, 3 <= n <= 1000, and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. -/
  theorem spec_7 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3eq : n = 3) (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr) :
      ∃ r : Std.I64, missing_number arr = ok r ∧
        ((step3 arr = 0 ∧ r.val = elem arr 0) ∨
          (step3 arr ≠ 0 ∧
            (r.val = elem arr 0 + step3 arr ∨
              r.val = elem arr 0 + 2 * step3 arr) ∧
            r.val ≠ elem arr 1 ∧
            ∀ y : Int,
              (y = elem arr 0 + step3 arr ∨ y = elem arr 0 + 2 * step3 arr) →
                y ≠ elem arr 1 → y = r.val)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3eq : n = 3) (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr), ∃ r : Std.I64, missing_number arr = ok r ∧
          ((step3 arr = 0 ∧ r.val = elem arr 0) ∨
            (step3 arr ≠ 0 ∧
              (r.val = elem arr 0 + step3 arr ∨
                r.val = elem arr 0 + 2 * step3 arr) ∧
              r.val ≠ elem arr 1 ∧
              ∀ y : Int,
                (y = elem arr 0 + step3 arr ∨ y = elem arr 0 + 2 * step3 arr) →
                  y ≠ elem arr 1 → y = r.val))) := by
    sorry

  /-- The function returns a result r and there exists an index k with 1 <= k < n such that 2*r = arr[k-1] + arr[k].
    Preconditions: Let n = len(arr). The input satisfies 3 <= n <= 1000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. -/
  theorem spec_8 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr) :
      ∃ r : Std.I64, missing_number arr = ok r ∧
        ∃ k : Nat, 1 ≤ k ∧ k < n ∧ 2 * r.val = elem arr (k - 1) + elem arr k := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr), ∃ r : Std.I64, missing_number arr = ok r ∧
          ∃ k : Nat, 1 ≤ k ∧ k < n ∧ 2 * r.val = elem arr (k - 1) + elem arr k) := by
    sorry

  /-- Let d = (arr[n-1] - arr[0]) / n, which is an integer by validity. The function returns a result r and there exists an integer k with 1 <= k < n such that r = arr[0] + k*d.
    Preconditions: Let n = len(arr). The input satisfies 3 <= n <= 1000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. -/
  theorem spec_9 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr) :
      ∃ r : Std.I64, missing_number arr = ok r ∧
        ∃ k : Nat, 1 ≤ k ∧ k < n ∧ r.val = elem arr 0 + (k : Int) * step arr n := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr), ∃ r : Std.I64, missing_number arr = ok r ∧
          ∃ k : Nat, 1 ≤ k ∧ k < n ∧ r.val = elem arr 0 + (k : Int) * step arr n) := by
    sorry

  /-- The function returns a result r and min(arr[0], arr[n-1]) < r < max(arr[0], arr[n-1]).
    Preconditions: Let n = len(arr). The input satisfies 3 <= n <= 1000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. Additionally, arr[0] != arr[n-1]. -/
  theorem spec_10 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr)
      (hne : elem arr 0 ≠ elem arr (n - 1)) :
      ∃ r : Std.I64, missing_number arr = ok r ∧
        min (elem arr 0) (elem arr (n - 1)) < r.val ∧
        r.val < max (elem arr 0) (elem arr (n - 1)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr)
        (hne : elem arr 0 ≠ elem arr (n - 1)), ∃ r : Std.I64, missing_number arr = ok r ∧
          min (elem arr 0) (elem arr (n - 1)) < r.val ∧
          r.val < max (elem arr 0) (elem arr (n - 1))) := by
    sorry

  /-- Let rev be the slice of length n with rev[i] = arr[n-1-i] for 0 <= i < n. The function returns a result r on arr and a result r_rev on rev, and r = r_rev.
    Preconditions: Let n = len(arr). The input satisfies 3 <= n <= 1000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. -/
  theorem spec_11 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr) :
      ∃ r r_rev : Std.I64,
        missing_number arr = ok r ∧
        missing_number (reverseSlice arr) = ok r_rev ∧ r.val = r_rev.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr), ∃ r r_rev : Std.I64,
          missing_number arr = ok r ∧
          missing_number (reverseSlice arr) = ok r_rev ∧ r.val = r_rev.val) := by
    sorry

  /-- For every integer c such that 0 <= arr[i] + c <= 100000 for all i with 0 <= i < n, let arr_c be the slice with arr_c[i] = arr[i] + c. The function returns a result r on arr and a result r_c on arr_c, and r_c = r + c.
    Preconditions: Let n = len(arr). The input satisfies 3 <= n <= 1000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000. Also arr is valid: there exist integers d and k such that 1 <= k < n, for every i with 0 <= i < k arr[i] = arr[0] + i*d, and for every i with k <= i < n arr[i] = arr[0] + (i+1)*d. -/
  theorem spec_12 (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
      (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
      (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
      (hvalid : IsValid arr)
      (c : Int)
      (hc : ∀ i : Nat, i < n → 0 ≤ elem arr i + c ∧ elem arr i + c ≤ 100000)
      (arr_c : Slice Std.I64) (harrc : arr_c.val.length = n)
      (hshift : ∀ i : Nat, i < n → elem arr_c i = elem arr i + c) :
      ∃ r r_c : Std.I64,
        missing_number arr = ok r ∧
        missing_number arr_c = ok r_c ∧ r_c.val = r.val + c := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (hn : arr.val.length = n)
        (h3 : 3 ≤ n) (h1000 : n ≤ 1000)
        (hbounds : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 100000)
        (hvalid : IsValid arr)
        (c : Int)
        (hc : ∀ i : Nat, i < n → 0 ≤ elem arr i + c ∧ elem arr i + c ≤ 100000)
        (arr_c : Slice Std.I64) (harrc : arr_c.val.length = n)
        (hshift : ∀ i : Nat, i < n → elem arr_c i = elem arr i + c), ∃ r r_c : Std.I64,
          missing_number arr = ok r ∧
          missing_number arr_c = ok r_c ∧ r_c.val = r.val + c) := by
    sorry

  end AegisSpec.MissingNumber
