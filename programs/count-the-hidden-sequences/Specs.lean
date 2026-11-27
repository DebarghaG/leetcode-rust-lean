import Aegis.NumberOfArrays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfArrays.number_of_arrays`

LeetCode problem `count-the-hidden-sequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfArrays

open Aegis.NumberOfArrays (number_of_arrays)

def vals (s : Slice Std.I64) : List Int := s.val.map fun x => x.val

def AllIn (l : List Int) (lo hi : Int) : Prop := ∀ x ∈ l, lo ≤ x ∧ x ≤ hi

def prefixes (d : List Int) : List Int := d.scanl (· + ·) 0

def minPrefix (d : List Int) : Int := (prefixes d).min?.getD 0

def maxPrefix (d : List Int) : Int := (prefixes d).max?.getD 0

def IsValidSeq (d : List Int) (lower upper : Int) (h : List Int) : Prop :=
  (∀ i, i < d.length → h[i + 1]! - h[i]! = d[i]!) ∧
    (∀ j, j < h.length → lower ≤ h[j]! ∧ h[j]! ≤ upper)

def goodSeqs (d : List Int) (lower upper : Int) : Set (List Int) :=
  {h | h.length = d.length + 1 ∧ IsValidSeq d lower upper h}

def shiftedPrefixes (d : List Int) (x : Int) : List Int := (prefixes d).map fun p => x + p

/-- Whenever number_of_arrays(differences, lower, upper) returns a result r, r is exactly the number C of sequences h of n+1 integers such that: (1) for every i with 0 <= i < n, h[i+1] - h[i] = differences[i]; and (2) for every j with 0 <= j <= n, lower <= h[j] <= upper.
  Preconditions: Let n = len(differences). Assume 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= differences[i] <= 100000; and -100000 <= lower <= upper <= 100000. -/
theorem spec_1 (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000) :
    ∀ r, number_of_arrays differences lower upper = ok r →
      r.val = ((goodSeqs (vals differences) lower.val upper.val).ncard : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000), ∀ r, number_of_arrays differences lower upper = ok r →
      r.val = ((goodSeqs (vals differences) lower.val upper.val).ncard : Int)) := by
  sorry

/-- For every input satisfying the preconditions, number_of_arrays(differences, lower, upper) returns a result r; it does not fail, overflow, or panic.
  Preconditions: Let n = len(differences). Assume 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= differences[i] <= 100000; and -100000 <= lower <= upper <= 100000. -/
theorem spec_2 (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000) :
    ∃ r, number_of_arrays differences lower upper = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000), ∃ r, number_of_arrays differences lower upper = ok r) := by
  sorry

/-- Whenever number_of_arrays(differences, lower, upper) returns a result r, 0 <= r <= upper - lower + 1.
  Preconditions: Let n = len(differences). Assume 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= differences[i] <= 100000; and -100000 <= lower <= upper <= 100000. -/
theorem spec_3 (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000) :
    ∀ r, number_of_arrays differences lower upper = ok r →
      (0 : Int) ≤ r.val ∧ r.val ≤ upper.val - lower.val + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000), ∀ r, number_of_arrays differences lower upper = ok r →
      (0 : Int) ≤ r.val ∧ r.val ≤ upper.val - lower.val + 1) := by
  sorry

/-- Let P[0]=0 and P[i+1]=P[i]+differences[i] for every i with 0 <= i < n. Let mn = min_{0 <= i <= n} P[i] and mx = max_{0 <= i <= n} P[i]. Whenever number_of_arrays(differences, lower, upper) returns a result r, r = max(0, (upper - lower + 1) - (mx - mn)).
  Preconditions: Let n = len(differences). Assume 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= differences[i] <= 100000; and -100000 <= lower <= upper <= 100000. -/
theorem spec_4 (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000) :
    ∀ r, number_of_arrays differences lower upper = ok r →
      r.val = max 0 (upper.val - lower.val + 1 -
        (maxPrefix (vals differences) - minPrefix (vals differences))) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000), ∀ r, number_of_arrays differences lower upper = ok r →
      r.val = max 0 (upper.val - lower.val + 1 -
        (maxPrefix (vals differences) - minPrefix (vals differences)))) := by
  sorry

/-- If number_of_arrays(differences, lower_1, upper_1) returns r_1 and number_of_arrays(differences, lower_2, upper_2) returns r_2, then r_1 = r_2.
  Preconditions: Let n = len(differences). Assume 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= differences[i] <= 100000; for k=1,2, -100000 <= lower_k <= upper_k <= 100000; and upper_1 - lower_1 = upper_2 - lower_2. -/
theorem spec_5 (differences : Slice Std.I64) (lower₁ upper₁ lower₂ upper₂ : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow₁ : -100000 ≤ lower₁.val) (hlu₁ : lower₁.val ≤ upper₁.val)
    (hup₁ : upper₁.val ≤ 100000)
    (hlow₂ : -100000 ≤ lower₂.val) (hlu₂ : lower₂.val ≤ upper₂.val)
    (hup₂ : upper₂.val ≤ 100000)
    (hspan : upper₁.val - lower₁.val = upper₂.val - lower₂.val) :
    ∀ r₁ r₂, number_of_arrays differences lower₁ upper₁ = ok r₁ →
      number_of_arrays differences lower₂ upper₂ = ok r₂ → r₁ = r₂ := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (differences : Slice Std.I64) (lower₁ upper₁ lower₂ upper₂ : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow₁ : -100000 ≤ lower₁.val) (hlu₁ : lower₁.val ≤ upper₁.val)
    (hup₁ : upper₁.val ≤ 100000)
    (hlow₂ : -100000 ≤ lower₂.val) (hlu₂ : lower₂.val ≤ upper₂.val)
    (hup₂ : upper₂.val ≤ 100000)
    (hspan : upper₁.val - lower₁.val = upper₂.val - lower₂.val), ∀ r₁ r₂, number_of_arrays differences lower₁ upper₁ = ok r₁ →
      number_of_arrays differences lower₂ upper₂ = ok r₂ → r₁ = r₂) := by
  sorry

/-- If number_of_arrays(differences, lower, upper) returns r and number_of_arrays(neg_differences, lower, upper) returns r', then r = r'.
  Preconditions: Let n = len(differences). Assume 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= differences[i] <= 100000; and -100000 <= lower <= upper <= 100000. Let neg_differences be the array of length n with neg_differences[i] = -differences[i] for 0 <= i < n. -/
theorem spec_6 (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000) :
    ∀ (neg_differences : Slice Std.I64) (r r' : Std.I64),
      vals neg_differences = (vals differences).map (fun x => -x) →
      number_of_arrays differences lower upper = ok r →
      number_of_arrays neg_differences lower upper = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000), ∀ (neg_differences : Slice Std.I64) (r r' : Std.I64),
      vals neg_differences = (vals differences).map (fun x => -x) →
      number_of_arrays differences lower upper = ok r →
      number_of_arrays neg_differences lower upper = ok r' → r = r') := by
  sorry

/-- If number_of_arrays(differences, lower, upper) returns r and number_of_arrays(rev_differences, lower, upper) returns r', then r = r'.
  Preconditions: Let n = len(differences). Assume 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= differences[i] <= 100000; and -100000 <= lower <= upper <= 100000. Let rev_differences be the array of length n with rev_differences[i] = differences[n-1-i] for 0 <= i < n. -/
theorem spec_7 (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000) :
    ∀ (rev_differences : Slice Std.I64) (r r' : Std.I64),
      vals rev_differences = (vals differences).reverse →
      number_of_arrays differences lower upper = ok r →
      number_of_arrays rev_differences lower upper = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (differences : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences.val.length) (hn2 : differences.val.length ≤ 100000)
    (hd : AllIn (vals differences) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000), ∀ (rev_differences : Slice Std.I64) (r r' : Std.I64),
      vals rev_differences = (vals differences).reverse →
      number_of_arrays differences lower upper = ok r →
      number_of_arrays rev_differences lower upper = ok r' → r = r') := by
  sorry

/-- If number_of_arrays(differences1, lower, upper) returns r1 and number_of_arrays(differences2, lower, upper) returns r2, then r1 = r2.
  Preconditions: Let n1 = len(differences1) and n2 = len(differences2). Assume 1 <= n1 <= 100000, 1 <= n2 <= 100000; for every i with 0 <= i < n1, -100000 <= differences1[i] <= 100000; for every i with 0 <= i < n2, -100000 <= differences2[i] <= 100000; and -100000 <= lower <= upper <= 100000. Define P1[0]=0 and P1[i+1]=P1[i]+differences1[i] for 0<=i<n1; define P2[0]=0 and P2[i+1]=P2[i]+differences2[i] for 0<=i<n2. Let mn1=min P1, mx1=max P1, mn2=min P2, mx2=max P2. Assume mn1 = mn2 and mx1 = mx2. -/
theorem spec_8 (differences1 differences2 : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences1.val.length) (hn2 : differences1.val.length ≤ 100000)
    (hn3 : 1 ≤ differences2.val.length) (hn4 : differences2.val.length ≤ 100000)
    (hd1 : AllIn (vals differences1) (-100000) 100000)
    (hd2 : AllIn (vals differences2) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000)
    (hmin : minPrefix (vals differences1) = minPrefix (vals differences2))
    (hmax : maxPrefix (vals differences1) = maxPrefix (vals differences2)) :
    ∀ r1 r2, number_of_arrays differences1 lower upper = ok r1 →
      number_of_arrays differences2 lower upper = ok r2 → r1 = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (differences1 differences2 : Slice Std.I64) (lower upper : Std.I64)
    (hn1 : 1 ≤ differences1.val.length) (hn2 : differences1.val.length ≤ 100000)
    (hn3 : 1 ≤ differences2.val.length) (hn4 : differences2.val.length ≤ 100000)
    (hd1 : AllIn (vals differences1) (-100000) 100000)
    (hd2 : AllIn (vals differences2) (-100000) 100000)
    (hlow : -100000 ≤ lower.val) (hlu : lower.val ≤ upper.val)
    (hup : upper.val ≤ 100000)
    (hmin : minPrefix (vals differences1) = minPrefix (vals differences2))
    (hmax : maxPrefix (vals differences1) = maxPrefix (vals differences2)), ∀ r1 r2, number_of_arrays differences1 lower upper = ok r1 →
      number_of_arrays differences2 lower upper = ok r2 → r1 = r2) := by
  sorry

end AegisSpec.NumberOfArrays
