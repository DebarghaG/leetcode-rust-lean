import Aegis.TransformArray.Code.Funs

/-!
# Specifications of `Aegis.TransformArray.transform_array`

LeetCode problem `array-transformation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TransformArray

open Aegis.TransformArray

def arrVals (arr : Slice Std.I64) : List Int := arr.val.map (fun x => x.val)

def resVals (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

def window? (a : List Int) (i : Nat) : Option (Int × Int × Int) :=
  if i = 0 then none
  else
    match a[i - 1]?, a[i]?, a[i + 1]? with
    | some l, some x, some r => some (l, x, r)
    | _, _, _ => none

def IsStrictMin (x l r : Int) : Prop := x < l ∧ x < r

def IsStrictMax (x l r : Int) : Prop := l < x ∧ r < x

def NotStrictExtremum (x l r : Int) : Prop := ¬ IsStrictMin x l r ∧ ¬ IsStrictMax x l r

def Between (x l r : Int) : Prop := min l r ≤ x ∧ x ≤ max l r

def step (a : List Int) : List Int :=
  List.ofFn (fun i : Fin a.length =>
    match window? a i.val with
    | some (l, x, r) =>
      if x < l ∧ x < r then x + 1
      else if l < x ∧ r < x then x - 1
      else x
    | none => a.get i)

def listMin : List Int → Int
  | [] => 0
  | x :: rest => rest.foldl min x

def listMax : List Int → Int
  | [] => 0
  | x :: rest => rest.foldl max x

def threePoint (a0 a1 a2 : Int) : Int :=
  if a1 < min a0 a2 then min a0 a2
  else if max a0 a2 < a1 then max a0 a2
  else a1

/-- The function returns a result r such that len(r) = len(arr) and there exists a non-negative integer K with the property that for every integer k >= K, step^k(arr) = r, where step is the day operation defined as follows: for an array a of length n, step(a) is the array b of length n with b[0] = a[0], b[n-1] = a[n-1], and for each i with 0 < i < n-1, b[i] = a[i]+1 if a[i] < a[i-1] and a[i] < a[i+1]; b[i] = a[i]-1 if a[i] > a[i-1] and a[i] > a[i+1]; and b[i] = a[i] otherwise. Equivalently, r is the unique array that is eventually reached by iterating step from arr and is a fixed point of step.
  Preconditions: len(arr) >= 3, len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_1 (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        (resVals r).length = (arrVals arr).length ∧
          step (resVals r) = resVals r ∧
            ∃ K : Nat, ∀ k : Nat, K ≤ k → (step^[k]) (arrVals arr) = resVals r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        (resVals r).length = (arrVals arr).length ∧
          step (resVals r) = resVals r ∧
            ∃ K : Nat, ∀ k : Nat, K ≤ k → (step^[k]) (arrVals arr) = resVals r) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, no arithmetic overflow, no out-of-bounds access).
  Preconditions: len(arr) >= 3, len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_2 (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64, transform_array arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100), ∃ r : alloc.vec.Vec Std.I64, transform_array arr = ok r) := by
  sorry

/-- For every i with 0 <= i < len(r), min(arr) <= r[i] <= max(arr), where min(arr) and max(arr) denote the minimum and maximum values in the initial array arr.
  Preconditions: len(arr) >= 3, len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_3 (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        ∀ (i : Nat) (x : Int),
          (resVals r)[i]? = some x → listMin (arrVals arr) ≤ x ∧ x ≤ listMax (arrVals arr) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        ∀ (i : Nat) (x : Int),
          (resVals r)[i]? = some x → listMin (arrVals arr) ≤ x ∧ x ≤ listMax (arrVals arr)) := by
  sorry

/-- r[0] = arr[0] and r[len(arr)-1] = arr[len(arr)-1].
  Preconditions: len(arr) >= 3, len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_4 (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        (resVals r)[0]? = (arrVals arr)[0]? ∧
          (resVals r)[(arrVals arr).length - 1]? = (arrVals arr)[(arrVals arr).length - 1]? := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        (resVals r)[0]? = (arrVals arr)[0]? ∧
          (resVals r)[(arrVals arr).length - 1]? = (arrVals arr)[(arrVals arr).length - 1]?) := by
  sorry

/-- step(r) = r, where step is the day operation defined in spec_1. Equivalently, for every i with 0 < i < len(r)-1, r[i] is between r[i-1] and r[i+1] inclusive, i.e., neither (r[i] < r[i-1] and r[i] < r[i+1]) nor (r[i] > r[i-1] and r[i] > r[i+1]) holds.
  Preconditions: len(arr) >= 3, len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_5 (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        step (resVals r) = resVals r ∧
          ∀ (i : Nat) (l x u : Int),
            window? (resVals r) i = some (l, x, u) → Between x l u := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        step (resVals r) = resVals r ∧
          ∀ (i : Nat) (l x u : Int),
            window? (resVals r) i = some (l, x, u) → Between x l u) := by
  sorry

/-- There exists a non-negative integer k and a sequence of arrays a_0, a_1, ..., a_k such that a_0 = arr, a_{j+1} = step(a_j) for every j with 0 <= j < k, and a_k = r, where step is the day operation defined in spec_1.
  Preconditions: len(arr) >= 3, len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_6 (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧ ∃ k : Nat, (step^[k]) (arrVals arr) = resVals r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧ ∃ k : Nat, (step^[k]) (arrVals arr) = resVals r) := by
  sorry

/-- r = arr.
  Preconditions: len(arr) >= 3, len(arr) <= 100, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100, and additionally for every i with 0 < i < len(arr)-1, arr[i] is between arr[i-1] and arr[i+1] inclusive (i.e., arr has no strict local extremum). -/
theorem spec_7 (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100)
    (h_no_ext : ∀ (i : Nat) (l x r : Int),
      window? (arrVals arr) i = some (l, x, r) → NotStrictExtremum x l r) :
    ∃ r : alloc.vec.Vec Std.I64, transform_array arr = ok r ∧ resVals r = arrVals arr := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100)
    (h_no_ext : ∀ (i : Nat) (l x r : Int),
      window? (arrVals arr) i = some (l, x, r) → NotStrictExtremum x l r), ∃ r : alloc.vec.Vec Std.I64, transform_array arr = ok r ∧ resVals r = arrVals arr) := by
  sorry

/-- r[0] = arr[0], r[2] = arr[2], and r[1] = min(arr[0], arr[2]) if arr[1] < min(arr[0], arr[2]); r[1] = max(arr[0], arr[2]) if arr[1] > max(arr[0], arr[2]); otherwise r[1] = arr[1].
  Preconditions: len(arr) = 3, and for every i with 0 <= i < 3, 1 <= arr[i] <= 100. -/
theorem spec_8 (arr : Slice Std.I64) (h_len : (arrVals arr).length = 3)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        resVals r =
          [ (arrVals arr).get ⟨0, by omega⟩
          , threePoint ((arrVals arr).get ⟨0, by omega⟩) ((arrVals arr).get ⟨1, by omega⟩)
              ((arrVals arr).get ⟨2, by omega⟩)
          , (arrVals arr).get ⟨2, by omega⟩ ] := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64) (h_len : (arrVals arr).length = 3)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        resVals r =
          [ (arrVals arr).get ⟨0, by omega⟩
          , threePoint ((arrVals arr).get ⟨0, by omega⟩) ((arrVals arr).get ⟨1, by omega⟩)
              ((arrVals arr).get ⟨2, by omega⟩)
          , (arrVals arr).get ⟨2, by omega⟩ ]) := by
  sorry

/-- If s is any array of the same length as arr such that step(s) = s and there exists a non-negative integer k with s = step^k(arr) (where step is the day operation defined in spec_1), then s = r.
  Preconditions: len(arr) >= 3, len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_9 (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100)
    (r : alloc.vec.Vec Std.I64) (hr : transform_array arr = ok r) (s : List Int)
    (hs_len : s.length = (arrVals arr).length) (hs_fix : step s = s)
    (hs_reach : ∃ k : Nat, (step^[k]) (arrVals arr) = s) :
    s = resVals r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100)
    (r : alloc.vec.Vec Std.I64) (hr : transform_array arr = ok r) (s : List Int)
    (hs_len : s.length = (arrVals arr).length) (hs_fix : step s = s)
    (hs_reach : ∃ k : Nat, (step^[k]) (arrVals arr) = s), s = resVals r) := by
  sorry

/-- For every i with 0 < i < len(arr)-1, if arr[i] is not a strict local extremum in arr (i.e., it is not the case that (arr[i] < arr[i-1] and arr[i] < arr[i+1]) and not the case that (arr[i] > arr[i-1] and arr[i] > arr[i+1])), then r[i] = arr[i].
  Preconditions: len(arr) >= 3, len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_10 (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        ∀ (i : Nat) (l x u : Int),
          window? (arrVals arr) i = some (l, x, u) → NotStrictExtremum x l u → (resVals r)[i]? = some x := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧
        ∀ (i : Nat) (l x u : Int),
          window? (arrVals arr) i = some (l, x, u) → NotStrictExtremum x l u → (resVals r)[i]? = some x) := by
  sorry

/-- len(r) = len(arr).
  Preconditions: len(arr) >= 3, len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_11 (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧ (resVals r).length = (arrVals arr).length := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64) (h_len_ge : 3 ≤ (arrVals arr).length)
    (h_len_le : (arrVals arr).length ≤ 100)
    (h_range : ∀ (i : Nat) (x : Int), (arrVals arr)[i]? = some x → 1 ≤ x ∧ x ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      transform_array arr = ok r ∧ (resVals r).length = (arrVals arr).length) := by
  sorry

end AegisSpec.TransformArray
