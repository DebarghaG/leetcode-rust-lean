import Aegis.NumberWays.Code.Funs

/-!
# Specifications of `Aegis.NumberWays.number_ways`

LeetCode problem `number-of-ways-to-wear-different-hats-to-each-other`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberWays

def rows (hats : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
  hats.val.map (fun v => v.val.map (fun x => x.val))

def occurs (h : ℤ) (l : List ℤ) : Prop := h ∈ l

def validAssign (hats : List (List ℤ)) (f : Fin hats.length → Fin 41) : Prop :=
  (∀ i : Fin hats.length, 1 ≤ (f i).val ∧ occurs ((f i).val : ℤ) (hats[i.val])) ∧
    ∀ i j : Fin hats.length, i ≠ j → f i ≠ f j

instance decidableValidAssign (hats : List (List ℤ)) : DecidablePred (validAssign hats) := by
  intro f
  unfold validAssign occurs
  infer_instance

def waysCount (hats : List (List ℤ)) : ℕ :=
  Fintype.card { f : Fin hats.length → Fin 41 // validAssign hats f }

def pairCount (l₀ l₁ : List ℤ) : ℕ :=
  ((l₀.toFinset ×ˢ l₁.toFinset).filter (fun p => p.1 ≠ p.2)).card

def allRowsSingleton (hats : List (List ℤ)) : Prop := ∀ l ∈ hats, l.length = 1

def forcedValues (hats : List (List ℤ)) : List ℤ := hats.map fun l => l.headD 0

def forcedValuesDistinct (hats : List (List ℤ)) : Prop := (forcedValues hats).Nodup

instance decidableForcedValuesDistinct (hats : List (List ℤ)) :
    Decidable (forcedValuesDistinct hats) := by
  unfold forcedValuesDistinct
  infer_instance

def rowsPairwiseDisjoint (hats : List (List ℤ)) : Prop :=
  ∀ (i j : ℕ) (hi : i < hats.length) (hj : j < hats.length),
    i < j → ∀ h : ℤ, occurs h hats[i] → occurs h hats[j] → False

def rowLengthProduct (hats : List (List ℤ)) : ℕ := (hats.map fun l => l.length).prod

def valuesUnion (hats : List (List ℤ)) : Finset ℤ :=
  hats.foldl (fun s l => s ∪ l.toFinset) ∅

def fallingFactorial (k n : ℕ) : ℕ := (Finset.range n).prod fun i => k - i

def commonValueSet (hats : List (List ℤ)) (S : Finset ℤ) : Prop :=
  ∀ (i : ℕ) (hi : i < hats.length) (h : ℤ), occurs h hats[i] ↔ h ∈ S

def isRowPermutation (rows' rows : List (List ℤ)) : Prop :=
  ∃ p : Equiv.Perm (Fin rows.length), ∀ i : Fin rows.length, rows'[(p i).val]? = some rows[i.val]

/-- The function returns a result r. Let n = len(hats). Let C be the number of functions f from {0, ..., n-1} to {1, ..., 40} such that for every i with 0 <= i < n, f(i) occurs in hats[i] (that is, there exists j with 0 <= j < len(hats[i]) and hats[i][j] = f(i)), and for every i and k with 0 <= i < k < n, f(i) != f(k). Then r = C mod 1000000007.
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_1 (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup) :
    ∃ r : I64,
      Aegis.NumberWays.number_ways hats = ok r ∧
        r.val = ((waysCount (rows hats) % 1000000007 : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup), ∃ r : I64,
      Aegis.NumberWays.number_ways hats = ok r ∧
        r.val = ((waysCount (rows hats) % 1000000007 : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, overflow, out-of-bounds access, or other runtime failure) for any input satisfying the preconditions.
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_2 (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup) :
    ∃ r : I64, Aegis.NumberWays.number_ways hats = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup), ∃ r : I64, Aegis.NumberWays.number_ways hats = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 1000000006.
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_3 (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup) :
    ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r),
      0 ≤ r.val ∧ r.val ≤ 1000000006 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup), ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r),
      0 ≤ r.val ∧ r.val ≤ 1000000006) := by
  sorry

/-- Whenever the function returns a result r, if len(hats) = 1, then r = len(hats[0]).
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_4 (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup) :
    ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (h1 : (rows hats).length = 1), r.val = (((rows hats)[0]).length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup), ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (h1 : (rows hats).length = 1), r.val = (((rows hats)[0]).length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if len(hats) = 2, then r is the cardinality of the set of all ordered pairs (a, b) such that a occurs in hats[0], b occurs in hats[1], and a != b.
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_5 (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup) :
    ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (h2 : (rows hats).length = 2),
      r.val = ((pairCount ((rows hats)[0]) ((rows hats)[1]) : ℕ) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup), ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (h2 : (rows hats).length = 2),
      r.val = ((pairCount ((rows hats)[0]) ((rows hats)[1]) : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if len(hats[i]) = 1 for every i with 0 <= i < len(hats), then r = 1 when the forced values hats[0][0], hats[1][0], ..., hats[len(hats)-1][0] are pairwise distinct, and r = 0 otherwise.
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_6 (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup) :
    ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hsingle : allRowsSingleton (rows hats)),
      r.val = (if forcedValuesDistinct (rows hats) then (1 : ℤ) else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup), ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hsingle : allRowsSingleton (rows hats)),
      r.val = (if forcedValuesDistinct (rows hats) then (1 : ℤ) else 0)) := by
  sorry

/-- Whenever the function returns a result r, if for every i and j with 0 <= i < j < len(hats) there is no integer h that occurs in both hats[i] and hats[j], then r = (product_{i=0}^{len(hats)-1} len(hats[i])) mod 1000000007.
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_7 (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup) :
    ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hdisj : rowsPairwiseDisjoint (rows hats)),
      r.val = ((rowLengthProduct (rows hats) % 1000000007 : ℕ) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup), ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hdisj : rowsPairwiseDisjoint (rows hats)),
      r.val = ((rowLengthProduct (rows hats) % 1000000007 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if the number of distinct integers appearing in at least one of the lists hats[i] for 0 <= i < len(hats) is strictly less than len(hats), then r = 0.
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_8 (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup) :
    ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hcard : (valuesUnion (rows hats)).card < (rows hats).length), r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup), ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hcard : (valuesUnion (rows hats)).card < (rows hats).length), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if there exists a set S of integers such that for every i with 0 <= i < len(hats), an integer h occurs in hats[i] exactly when h is in S, then let k be the number of elements of S and n = len(hats). If k >= n, r = (k * (k-1) * ... * (k-n+1)) mod 1000000007; if k < n, r = 0.
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_9 (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup) :
    ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r) (S : Finset ℤ)
      (hS : commonValueSet (rows hats) S),
        r.val = (if (rows hats).length ≤ S.card
          then ((fallingFactorial S.card (rows hats).length % 1000000007 : ℕ) : ℤ)
          else 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup), ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r) (S : Finset ℤ)
      (hS : commonValueSet (rows hats) S),
        r.val = (if (rows hats).length ≤ S.card
          then ((fallingFactorial S.card (rows hats).length % 1000000007 : ℕ) : ℤ)
          else 0)) := by
  sorry

/-- For every slice hats' satisfying the same preconditions as hats, if hats' is a permutation of the rows of hats (that is, there is a bijection p on {0, ..., len(hats)-1} such that hats'[p(i)] = hats[i] for every i), then whenever number_ways hats returns r and number_ways hats' returns r', we have r = r'.
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_10 (hats hats' : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup)
    (hne' : 1 ≤ (rows hats').length) (hle' : (rows hats').length ≤ 10)
    (hrow' : ∀ (i : ℕ) (hi : i < (rows hats').length),
      1 ≤ ((rows hats')[i]).length ∧ ((rows hats')[i]).length ≤ 40)
    (hval' : ∀ (i : ℕ) (hi : i < (rows hats').length) (j : ℕ)
      (hj : j < ((rows hats')[i]).length),
      1 ≤ ((rows hats')[i])[j] ∧ ((rows hats')[i])[j] ≤ 40)
    (hnd' : ∀ (i : ℕ) (hi : i < (rows hats').length), ((rows hats')[i]).Nodup)
    (hperm : isRowPermutation (rows hats') (rows hats)) :
    ∀ (r r' : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hr' : Aegis.NumberWays.number_ways hats' = ok r'), r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (hats hats' : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup)
    (hne' : 1 ≤ (rows hats').length) (hle' : (rows hats').length ≤ 10)
    (hrow' : ∀ (i : ℕ) (hi : i < (rows hats').length),
      1 ≤ ((rows hats')[i]).length ∧ ((rows hats')[i]).length ≤ 40)
    (hval' : ∀ (i : ℕ) (hi : i < (rows hats').length) (j : ℕ)
      (hj : j < ((rows hats')[i]).length),
      1 ≤ ((rows hats')[i])[j] ∧ ((rows hats')[i])[j] ≤ 40)
    (hnd' : ∀ (i : ℕ) (hi : i < (rows hats').length), ((rows hats')[i]).Nodup)
    (hperm : isRowPermutation (rows hats') (rows hats)), ∀ (r r' : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hr' : Aegis.NumberWays.number_ways hats' = ok r'), r = r') := by
  sorry

/-- For every slice hats' satisfying the same preconditions as hats with len(hats') = len(hats), and every bijection phi from {1, ..., 40} to itself, if len(hats'[i]) = len(hats[i]) and hats'[i][j] = phi(hats[i][j]) for every i with 0 <= i < len(hats) and every j with 0 <= j < len(hats[i]), then whenever number_ways hats returns r and number_ways hats' returns r', we have r = r'.
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_11 (hats hats' : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup)
    (hne' : 1 ≤ (rows hats').length) (hle' : (rows hats').length ≤ 10)
    (hrow' : ∀ (i : ℕ) (hi : i < (rows hats').length),
      1 ≤ ((rows hats')[i]).length ∧ ((rows hats')[i]).length ≤ 40)
    (hval' : ∀ (i : ℕ) (hi : i < (rows hats').length) (j : ℕ)
      (hj : j < ((rows hats')[i]).length),
      1 ≤ ((rows hats')[i])[j] ∧ ((rows hats')[i])[j] ≤ 40)
    (hnd' : ∀ (i : ℕ) (hi : i < (rows hats').length), ((rows hats')[i]).Nodup)
    (hlen : (rows hats').length = (rows hats).length)
    (φ : Equiv.Perm ℤ) (hφ : ∀ v : ℤ, 1 ≤ v → v ≤ 40 → 1 ≤ φ v ∧ φ v ≤ 40)
    (hφrows : (rows hats').map (fun l => l.map fun v => φ v) = rows hats) :
    ∀ (r r' : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hr' : Aegis.NumberWays.number_ways hats' = ok r'), r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (hats hats' : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup)
    (hne' : 1 ≤ (rows hats').length) (hle' : (rows hats').length ≤ 10)
    (hrow' : ∀ (i : ℕ) (hi : i < (rows hats').length),
      1 ≤ ((rows hats')[i]).length ∧ ((rows hats')[i]).length ≤ 40)
    (hval' : ∀ (i : ℕ) (hi : i < (rows hats').length) (j : ℕ)
      (hj : j < ((rows hats')[i]).length),
      1 ≤ ((rows hats')[i])[j] ∧ ((rows hats')[i])[j] ≤ 40)
    (hnd' : ∀ (i : ℕ) (hi : i < (rows hats').length), ((rows hats')[i]).Nodup)
    (hlen : (rows hats').length = (rows hats).length)
    (φ : Equiv.Perm ℤ) (hφ : ∀ v : ℤ, 1 ≤ v → v ≤ 40 → 1 ≤ φ v ∧ φ v ≤ 40)
    (hφrows : (rows hats').map (fun l => l.map fun v => φ v) = rows hats), ∀ (r r' : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hr' : Aegis.NumberWays.number_ways hats' = ok r'), r = r') := by
  sorry

/-- For every slice hats' satisfying the same preconditions as hats with len(hats') = len(hats), if for every i with 0 <= i < len(hats) the list hats'[i] is a reordering of the list hats[i], then whenever number_ways hats returns r and number_ways hats' returns r', we have r = r'.
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_12 (hats hats' : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup)
    (hne' : 1 ≤ (rows hats').length) (hle' : (rows hats').length ≤ 10)
    (hrow' : ∀ (i : ℕ) (hi : i < (rows hats').length),
      1 ≤ ((rows hats')[i]).length ∧ ((rows hats')[i]).length ≤ 40)
    (hval' : ∀ (i : ℕ) (hi : i < (rows hats').length) (j : ℕ)
      (hj : j < ((rows hats')[i]).length),
      1 ≤ ((rows hats')[i])[j] ∧ ((rows hats')[i])[j] ≤ 40)
    (hnd' : ∀ (i : ℕ) (hi : i < (rows hats').length), ((rows hats')[i]).Nodup)
    (hlen : (rows hats').length = (rows hats).length)
    (hrows : ∀ (i : ℕ) (hi : i < (rows hats).length),
      List.Perm ((rows hats')[i]) ((rows hats)[i])) :
    ∀ (r r' : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hr' : Aegis.NumberWays.number_ways hats' = ok r'), r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (hats hats' : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup)
    (hne' : 1 ≤ (rows hats').length) (hle' : (rows hats').length ≤ 10)
    (hrow' : ∀ (i : ℕ) (hi : i < (rows hats').length),
      1 ≤ ((rows hats')[i]).length ∧ ((rows hats')[i]).length ≤ 40)
    (hval' : ∀ (i : ℕ) (hi : i < (rows hats').length) (j : ℕ)
      (hj : j < ((rows hats')[i]).length),
      1 ≤ ((rows hats')[i])[j] ∧ ((rows hats')[i])[j] ≤ 40)
    (hnd' : ∀ (i : ℕ) (hi : i < (rows hats').length), ((rows hats')[i]).Nodup)
    (hlen : (rows hats').length = (rows hats).length)
    (hrows : ∀ (i : ℕ) (hi : i < (rows hats).length),
      List.Perm ((rows hats')[i]) ((rows hats)[i])), ∀ (r r' : I64) (hr : Aegis.NumberWays.number_ways hats = ok r)
      (hr' : Aegis.NumberWays.number_ways hats' = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r, if r > 0, then there exists a function f from {0, ..., len(hats)-1} to {1, ..., 40} such that for every i with 0 <= i < len(hats), f(i) occurs in hats[i], and for every i and j with 0 <= i < j < len(hats), f(i) != f(j).
  Preconditions: len(hats) is between 1 and 10 inclusive; for every i with 0 <= i < len(hats), 1 <= len(hats[i]) <= 40; for every i and j with 0 <= i < len(hats) and 0 <= j < len(hats[i]), 1 <= hats[i][j] <= 40; and for every i, the values hats[i][0], ..., hats[i][len(hats[i])-1] are pairwise distinct. -/
theorem spec_13 (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup) :
    ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r) (hpos : 0 < r.val),
      ∃ f : Fin (rows hats).length → Fin 41, validAssign (rows hats) f := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (hats : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ (rows hats).length) (hle : (rows hats).length ≤ 10)
    (hrow : ∀ (i : ℕ) (hi : i < (rows hats).length),
      1 ≤ ((rows hats)[i]).length ∧ ((rows hats)[i]).length ≤ 40)
    (hval : ∀ (i : ℕ) (hi : i < (rows hats).length) (j : ℕ)
      (hj : j < ((rows hats)[i]).length),
      1 ≤ ((rows hats)[i])[j] ∧ ((rows hats)[i])[j] ≤ 40)
    (hnd : ∀ (i : ℕ) (hi : i < (rows hats).length), ((rows hats)[i]).Nodup), ∀ (r : I64) (hr : Aegis.NumberWays.number_ways hats = ok r) (hpos : 0 < r.val),
      ∃ f : Fin (rows hats).length → Fin 41, validAssign (rows hats) f) := by
  sorry

end AegisSpec.NumberWays
