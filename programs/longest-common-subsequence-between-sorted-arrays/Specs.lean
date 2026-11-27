import Aegis.LongestCommonSubsequence.Code.Funs

/-!
# Specifications of `Aegis.LongestCommonSubsequence.longest_common_subsequence`

LeetCode problem `longest-common-subsequence-between-sorted-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestCommonSubsequence

  def vecVals (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

  def contents (arrays : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    arrays.val.map vecVals

  def StrictlyIncreasing (l : List Int) : Prop :=
    ∀ (j : Nat) (_ : j + 1 < l.length), l[j] < l[j+1]

  def OccursIn (x : Int) (l : List Int) : Prop :=
    ∃ (j : Nat) (_ : j < l.length), l[j] = x

  def OccursInAll (arrays : List (List Int)) (x : Int) : Prop :=
    ∀ (i : Nat) (_ : i < arrays.length), OccursIn x arrays[i]

  def IsSubsequence (l s : List Int) : Prop :=
    ∃ js : List Nat,
      js.length = l.length ∧ js.Pairwise (· < ·) ∧
        js.map (fun j => s[j]?) = l.map some

  def IsCommonSubsequence (l : List Int) (arrays : List (List Int)) : Prop :=
    ∀ (i : Nat) (_ : i < arrays.length), IsSubsequence l arrays[i]

  def commonCount (arrays : List (List Int)) : Nat :=
    ((List.range 100).filter
      (fun n : Nat => arrays.all (fun l => l.contains ((n : Int) + 1)))).length

  def IsLeastCommonValue (arrays : List (List Int)) (v : Int) : Prop :=
    1 ≤ v ∧ v ≤ 100 ∧ OccursInAll arrays v ∧
      ∀ x : Int, 1 ≤ x → x ≤ 100 → OccursInAll arrays x → v ≤ x

  def IsGreatestCommonValue (arrays : List (List Int)) (v : Int) : Prop :=
    1 ≤ v ∧ v ≤ 100 ∧ OccursInAll arrays v ∧
      ∀ x : Int, 1 ≤ x → x ≤ 100 → OccursInAll arrays x → x ≤ v

  def Constraints (arrays : List (List Int)) : Prop :=
    2 ≤ arrays.length ∧ arrays.length ≤ 100 ∧
      (∀ (i : Nat) (_ : i < arrays.length),
        1 ≤ (arrays[i]).length ∧ (arrays[i]).length ≤ 100) ∧
      (∀ (i : Nat) (_ : i < arrays.length), StrictlyIncreasing arrays[i]) ∧
      (∀ (i j : Nat) (_ : i < arrays.length) (_ : j < (arrays[i]).length),
        1 ≤ (arrays[i])[j] ∧ (arrays[i])[j] ≤ 100)

  /-- The function returns a result r such that: (1) r is a common subsequence of all arrays, i.e. for every i with 0 <= i < len(arrays) there exist indices j_0 < j_1 < ... < j_{len(r)-1} with 0 <= j_t < len(arrays[i]) and arrays[i][j_t] = r[t] for every t with 0 <= t < len(r); and (2) r has maximum length among all such common subsequences, i.e. for every list s of integers that is a common subsequence of every arrays[i], len(s) <= len(r).
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_1 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r ∧
          IsCommonSubsequence (vecVals r) (contents arrays) ∧
          (∀ s : List Int,
            IsCommonSubsequence s (contents arrays) → s.length ≤ (vecVals r).length) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r ∧
            IsCommonSubsequence (vecVals r) (contents arrays) ∧
            (∀ s : List Int,
              IsCommonSubsequence s (contents arrays) → s.length ≤ (vecVals r).length)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the constraints.
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_2 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r) := by
    sorry

  /-- Whenever the function returns a result r and the constraints hold, for every k with 0 <= k < len(r), 1 <= r[k] <= 100.
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_3 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r) :
      ∀ (k : Nat) (_ : k < (vecVals r).length),
        1 ≤ (vecVals r)[k] ∧ (vecVals r)[k] ≤ 100 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r), ∀ (k : Nat) (_ : k < (vecVals r).length),
          1 ≤ (vecVals r)[k] ∧ (vecVals r)[k] ≤ 100) := by
    sorry

  /-- Whenever the function returns a result r and the constraints hold, len(r) <= len(arrays[i]) for every i with 0 <= i < len(arrays).
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_4 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r) :
      ∀ (i : Nat) (_ : i < (contents arrays).length),
        (vecVals r).length ≤ (contents arrays)[i].length := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r), ∀ (i : Nat) (_ : i < (contents arrays).length),
          (vecVals r).length ≤ (contents arrays)[i].length) := by
    sorry

  /-- Whenever the function returns a result r and the constraints hold, for every k with 0 <= k < len(r)-1, r[k] < r[k+1].
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_5 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r) :
      ∀ (k : Nat) (_ : k + 1 < (vecVals r).length), (vecVals r)[k] < (vecVals r)[k+1] := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r), ∀ (k : Nat) (_ : k + 1 < (vecVals r).length), (vecVals r)[k] < (vecVals r)[k+1]) := by
    sorry

  /-- Whenever the function returns a result r and the constraints hold, for every k with 0 <= k < len(r) and every i with 0 <= i < len(arrays), there exists j with 0 <= j < len(arrays[i]) and arrays[i][j] = r[k].
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_6 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r) :
      ∀ (k : Nat) (_ : k < (vecVals r).length)
        (i : Nat) (_ : i < (contents arrays).length),
        ∃ (j : Nat) (_ : j < (contents arrays)[i].length),
          (contents arrays)[i][j] = (vecVals r)[k] := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r), ∀ (k : Nat) (_ : k < (vecVals r).length)
          (i : Nat) (_ : i < (contents arrays).length),
          ∃ (j : Nat) (_ : j < (contents arrays)[i].length),
            (contents arrays)[i][j] = (vecVals r)[k]) := by
    sorry

  /-- Whenever the function returns a result r and the constraints hold, for every i with 0 <= i < len(arrays), there exist indices j_0 < j_1 < ... < j_{len(r)-1} with 0 <= j_t < len(arrays[i]) and arrays[i][j_t] = r[t] for every t with 0 <= t < len(r).
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_7 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r) :
      ∀ (i : Nat) (_ : i < (contents arrays).length),
        IsSubsequence (vecVals r) (contents arrays)[i] := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r), ∀ (i : Nat) (_ : i < (contents arrays).length),
          IsSubsequence (vecVals r) (contents arrays)[i]) := by
    sorry

  /-- Whenever the function returns a result r and the constraints hold, for every integer x with 1 <= x <= 100, if for every i with 0 <= i < len(arrays) there exists j with 0 <= j < len(arrays[i]) and arrays[i][j] = x, then there exists k with 0 <= k < len(r) and r[k] = x.
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_8 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r) :
      ∀ x : Int, 1 ≤ x → x ≤ 100 → OccursInAll (contents arrays) x →
        ∃ (k : Nat) (_ : k < (vecVals r).length), (vecVals r)[k] = x := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r), ∀ x : Int, 1 ≤ x → x ≤ 100 → OccursInAll (contents arrays) x →
          ∃ (k : Nat) (_ : k < (vecVals r).length), (vecVals r)[k] = x) := by
    sorry

  /-- Whenever the function returns a result r and the constraints hold, len(r) is equal to the number of integers x with 1 <= x <= 100 such that for every i with 0 <= i < len(arrays) there exists j with 0 <= j < len(arrays[i]) and arrays[i][j] = x.
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_9 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r) :
      (vecVals r).length = commonCount (contents arrays) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r), (vecVals r).length = commonCount (contents arrays)) := by
    sorry

  /-- Whenever the function returns a result r and the constraints hold, len(r) = 0 if and only if there is no integer x with 1 <= x <= 100 such that for every i with 0 <= i < len(arrays) there exists j with 0 <= j < len(arrays[i]) and arrays[i][j] = x.
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_10 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r) :
      (vecVals r).length = 0 ↔
        ¬ ∃ x : Int, 1 ≤ x ∧ x ≤ 100 ∧ OccursInAll (contents arrays) x := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r), (vecVals r).length = 0 ↔
          ¬ ∃ x : Int, 1 ≤ x ∧ x ≤ 100 ∧ OccursInAll (contents arrays) x) := by
    sorry

  /-- Whenever the function returns a result r and the constraints hold, if there exists an integer x with 1 <= x <= 100 such that for every i with 0 <= i < len(arrays) there exists j with 0 <= j < len(arrays[i]) and arrays[i][j] = x, then len(r) > 0 and r[0] is the smallest such x.
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_11 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r) :
      (∃ x : Int, 1 ≤ x ∧ x ≤ 100 ∧ OccursInAll (contents arrays) x) →
        0 < (vecVals r).length ∧
          IsLeastCommonValue (contents arrays) (vecVals r)[0]! := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r), (∃ x : Int, 1 ≤ x ∧ x ≤ 100 ∧ OccursInAll (contents arrays) x) →
          0 < (vecVals r).length ∧
            IsLeastCommonValue (contents arrays) (vecVals r)[0]!) := by
    sorry

  /-- Whenever the function returns a result r and the constraints hold, if there exists an integer x with 1 <= x <= 100 such that for every i with 0 <= i < len(arrays) there exists j with 0 <= j < len(arrays[i]) and arrays[i][j] = x, then len(r) > 0 and r[len(r)-1] is the largest such x.
    Preconditions: The constraints hold: 2 <= len(arrays) <= 100; for every i with 0 <= i < len(arrays), 1 <= len(arrays[i]) <= 100 and arrays[i][j] < arrays[i][j+1] for every j with 0 <= j < len(arrays[i])-1; and for every i,j with 0 <= i < len(arrays) and 0 <= j < len(arrays[i]), 1 <= arrays[i][j] <= 100. -/
  theorem spec_12 (arrays : Slice (alloc.vec.Vec Std.I64))
      (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r) :
      (∃ x : Int, 1 ≤ x ∧ x ≤ 100 ∧ OccursInAll (contents arrays) x) →
        0 < (vecVals r).length ∧
          IsGreatestCommonValue (contents arrays)
            (vecVals r)[(vecVals r).length - 1]! := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arrays : Slice (alloc.vec.Vec Std.I64))
        (h : Constraints (contents arrays)) (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.LongestCommonSubsequence.longest_common_subsequence arrays = ok r), (∃ x : Int, 1 ≤ x ∧ x ≤ 100 ∧ OccursInAll (contents arrays) x) →
          0 < (vecVals r).length ∧
            IsGreatestCommonValue (contents arrays)
              (vecVals r)[(vecVals r).length - 1]!) := by
    sorry

  end AegisSpec.LongestCommonSubsequence
