import Aegis.MakeArrayIncreasing.Code.Funs

/-!
# Specifications of `Aegis.MakeArrayIncreasing.make_array_increasing`

LeetCode problem `make-array-strictly-increasing`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MakeArrayIncreasing

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def OccursIn (v : ℤ) (s : Slice Std.I64) : Prop := v ∈ vals s

def ValuesInRange (s : Slice Std.I64) (lo hi : ℤ) : Prop :=
  ∀ v ∈ s.val, lo ≤ v.val ∧ v.val ≤ hi

def StrictlyIncr (b : List ℤ) : Prop :=
  ∀ (i : ℕ) (x y : ℤ), b[i]? = some x → b[i + 1]? = some y → x < y

def EntriesFrom (l1 l2 b : List ℤ) : Prop :=
  ∀ (i : ℕ) (v : ℤ), b[i]? = some v → l1[i]? = some v ∨ v ∈ l2

def Obtainable (l1 l2 b : List ℤ) : Prop :=
  b.length = l1.length ∧ EntriesFrom l1 l2 b ∧ StrictlyIncr b

def Cost (l1 b : List ℤ) : ℕ :=
  List.countP (fun p : ℤ × ℤ => decide (p.1 ≠ p.2)) (l1.zip b)

def Matches (l1 b : List ℤ) : ℕ :=
  List.countP (fun p : ℤ × ℤ => decide (p.1 = p.2)) (l1.zip b)

abbrev impl : Slice Std.I64 → Slice Std.I64 → Result Std.I64 :=
  Aegis.MakeArrayIncreasing.make_array_increasing

/-- Let n = len(arr1). Call a sequence b of length n obtainable if for every i with 0 <= i < n, either b[i] = arr1[i] or there exists j with 0 <= j < len(arr2) and b[i] = arr2[j]. Call b increasing if b[i] < b[i+1] for every 0 <= i < n-1. Let cost(b) be the number of indices i with 0 <= i < n and b[i] != arr1[i]. The function returns a result r such that either: (a) r = -1 and there is no obtainable increasing sequence b, or (b) r >= 0, there exists an obtainable increasing sequence b with cost(b) = r, and every obtainable increasing sequence b satisfies cost(b) >= r.
  Preconditions: 1 <= len(arr1) <= 2000, 1 <= len(arr2) <= 2000, 0 <= arr1[i] <= 10^9 for every 0 <= i < len(arr1), and 0 <= arr2[j] <= 10^9 for every 0 <= j < len(arr2). -/
theorem spec_1 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)) :
    ∃ r : Std.I64, impl arr1 arr2 = ok r ∧
      ((r.val = -1 ∧ ¬ ∃ b : List ℤ, Obtainable (vals arr1) (vals arr2) b) ∨
       (0 ≤ r.val ∧
        (∃ b : List ℤ, Obtainable (vals arr1) (vals arr2) b ∧
          (Cost (vals arr1) b : ℤ) = r.val) ∧
        (∀ b : List ℤ, Obtainable (vals arr1) (vals arr2) b →
          r.val ≤ (Cost (vals arr1) b : ℤ)))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)), ∃ r : Std.I64, impl arr1 arr2 = ok r ∧
      ((r.val = -1 ∧ ¬ ∃ b : List ℤ, Obtainable (vals arr1) (vals arr2) b) ∨
       (0 ≤ r.val ∧
        (∃ b : List ℤ, Obtainable (vals arr1) (vals arr2) b ∧
          (Cost (vals arr1) b : ℤ) = r.val) ∧
        (∀ b : List ℤ, Obtainable (vals arr1) (vals arr2) b →
          r.val ≤ (Cost (vals arr1) b : ℤ))))) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: 1 <= len(arr1) <= 2000, 1 <= len(arr2) <= 2000, 0 <= arr1[i] <= 10^9 for every 0 <= i < len(arr1), and 0 <= arr2[j] <= 10^9 for every 0 <= j < len(arr2). -/
theorem spec_2 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)) :
    ∃ r : Std.I64, impl arr1 arr2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)), ∃ r : Std.I64, impl arr1 arr2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r <= len(arr1).
  Preconditions: 1 <= len(arr1) <= 2000, 1 <= len(arr2) <= 2000, 0 <= arr1[i] <= 10^9 for every 0 <= i < len(arr1), and 0 <= arr2[j] <= 10^9 for every 0 <= j < len(arr2). -/
theorem spec_3 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)) :
    ∀ r : Std.I64, impl arr1 arr2 = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (arr1.val.length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)), ∀ r : Std.I64, impl arr1 arr2 = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (arr1.val.length : ℤ))) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if arr1 is strictly increasing, meaning arr1[i] < arr1[i+1] for every 0 <= i < len(arr1)-1.
  Preconditions: 1 <= len(arr1) <= 2000, 1 <= len(arr2) <= 2000, 0 <= arr1[i] <= 10^9 for every 0 <= i < len(arr1), and 0 <= arr2[j] <= 10^9 for every 0 <= j < len(arr2). -/
theorem spec_4 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)) :
    ∀ r : Std.I64, impl arr1 arr2 = ok r →
      (r.val = 0 ↔ StrictlyIncr (vals arr1)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)), ∀ r : Std.I64, impl arr1 arr2 = ok r →
      (r.val = 0 ↔ StrictlyIncr (vals arr1))) := by
  sorry

/-- Let n = len(arr1). The function returns r = -1 if and only if there is no sequence b of length n such that: (i) for every i with 0 <= i < n, either b[i] = arr1[i] or there exists j with 0 <= j < len(arr2) and b[i] = arr2[j], and (ii) b[i] < b[i+1] for every 0 <= i < n-1.
  Preconditions: 1 <= len(arr1) <= 2000, 1 <= len(arr2) <= 2000, 0 <= arr1[i] <= 10^9 for every 0 <= i < len(arr1), and 0 <= arr2[j] <= 10^9 for every 0 <= j < len(arr2). -/
theorem spec_5 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)) :
    ∀ r : Std.I64, impl arr1 arr2 = ok r →
      (r.val = -1 ↔ ¬ ∃ b : List ℤ, Obtainable (vals arr1) (vals arr2) b) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)), ∀ r : Std.I64, impl arr1 arr2 = ok r →
      (r.val = -1 ↔ ¬ ∃ b : List ℤ, Obtainable (vals arr1) (vals arr2) b)) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there exists a sequence b of length len(arr1) such that: (i) for every i with 0 <= i < len(arr1), either b[i] = arr1[i] or there exists j with 0 <= j < len(arr2) and b[i] = arr2[j]; (ii) b[i] < b[i+1] for every 0 <= i < len(arr1)-1; and (iii) the number of indices i with 0 <= i < len(arr1) and b[i] != arr1[i] is exactly r.
  Preconditions: 1 <= len(arr1) <= 2000, 1 <= len(arr2) <= 2000, 0 <= arr1[i] <= 10^9 for every 0 <= i < len(arr1), and 0 <= arr2[j] <= 10^9 for every 0 <= j < len(arr2). -/
theorem spec_6 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)) :
    ∀ r : Std.I64, impl arr1 arr2 = ok r → 0 ≤ r.val →
      ∃ b : List ℤ, Obtainable (vals arr1) (vals arr2) b ∧
        (Cost (vals arr1) b : ℤ) = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)), ∀ r : Std.I64, impl arr1 arr2 = ok r → 0 ≤ r.val →
      ∃ b : List ℤ, Obtainable (vals arr1) (vals arr2) b ∧
        (Cost (vals arr1) b : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for every sequence b of length len(arr1) satisfying: (i) for every i with 0 <= i < len(arr1), either b[i] = arr1[i] or there exists j with 0 <= j < len(arr2) and b[i] = arr2[j]; and (ii) b[i] < b[i+1] for every 0 <= i < len(arr1)-1, the number of indices i with b[i] != arr1[i] is at least r.
  Preconditions: 1 <= len(arr1) <= 2000, 1 <= len(arr2) <= 2000, 0 <= arr1[i] <= 10^9 for every 0 <= i < len(arr1), and 0 <= arr2[j] <= 10^9 for every 0 <= j < len(arr2). -/
theorem spec_7 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)) :
    ∀ r : Std.I64, impl arr1 arr2 = ok r → 0 ≤ r.val →
      ∀ b : List ℤ, Obtainable (vals arr1) (vals arr2) b →
        r.val ≤ (Cost (vals arr1) b : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)), ∀ r : Std.I64, impl arr1 arr2 = ok r → 0 ≤ r.val →
      ∀ b : List ℤ, Obtainable (vals arr1) (vals arr2) b →
        r.val ≤ (Cost (vals arr1) b : ℤ)) := by
  sorry

/-- If the function returns r on (arr1, arr2) and returns r' on (arr1, arr2'), then r = r'.
  Preconditions: 1 <= len(arr1) <= 2000, 1 <= len(arr2) <= 2000, 0 <= arr1[i] <= 10^9 for every 0 <= i < len(arr1), 0 <= arr2[j] <= 10^9 for every 0 <= j < len(arr2), and arr2' is any slice of i64 with 1 <= len(arr2') <= 2000 such that for every integer v, v occurs in arr2' if and only if v occurs in arr2. -/
theorem spec_8 (arr1 arr2 arr2' : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9))
    (h2'len : 1 ≤ arr2'.val.length) (h2'max : arr2'.val.length ≤ 2000)
    (hocc : ∀ v : ℤ, OccursIn v arr2' ↔ OccursIn v arr2) :
    ∀ r r' : Std.I64, impl arr1 arr2 = ok r → impl arr1 arr2' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr1 arr2 arr2' : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9))
    (h2'len : 1 ≤ arr2'.val.length) (h2'max : arr2'.val.length ≤ 2000)
    (hocc : ∀ v : ℤ, OccursIn v arr2' ↔ OccursIn v arr2), ∀ r r' : Std.I64, impl arr1 arr2 = ok r → impl arr1 arr2' = ok r' →
      r.val = r'.val) := by
  sorry

/-- Let r be the result of the function on (arr1, arr2) and r' the result on (arr1, arr2'). If r >= 0, then r' >= 0 and r' <= r.
  Preconditions: 1 <= len(arr1) <= 2000, 1 <= len(arr2) <= 2000, 0 <= arr1[i] <= 10^9 for every 0 <= i < len(arr1), 0 <= arr2[j] <= 10^9 for every 0 <= j < len(arr2), and arr2' is any slice of i64 with 1 <= len(arr2') <= 2000 and 0 <= arr2'[j] <= 10^9 for every j, such that every value occurring in arr2 also occurs in arr2'. -/
theorem spec_9 (arr1 arr2 arr2' : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9))
    (h2'len : 1 ≤ arr2'.val.length) (h2'max : arr2'.val.length ≤ 2000)
    (h2'range : ValuesInRange arr2' 0 ((10 : ℤ) ^ 9))
    (hsub : ∀ v : ℤ, OccursIn v arr2 → OccursIn v arr2') :
    ∀ r r' : Std.I64, impl arr1 arr2 = ok r → impl arr1 arr2' = ok r' →
      0 ≤ r.val → 0 ≤ r'.val ∧ r'.val ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr1 arr2 arr2' : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9))
    (h2'len : 1 ≤ arr2'.val.length) (h2'max : arr2'.val.length ≤ 2000)
    (h2'range : ValuesInRange arr2' 0 ((10 : ℤ) ^ 9))
    (hsub : ∀ v : ℤ, OccursIn v arr2 → OccursIn v arr2'), ∀ r r' : Std.I64, impl arr1 arr2 = ok r → impl arr1 arr2' = ok r' →
      0 ≤ r.val → 0 ≤ r'.val ∧ r'.val ≤ r.val) := by
  sorry

/-- If the function returns r on (arr1, arr2) and returns r' on (arr1', arr2'), then r = r'.
  Preconditions: 1 <= len(arr1) <= 2000, 1 <= len(arr2) <= 2000, 0 <= arr1[i] <= 10^9 for every 0 <= i < len(arr1), 0 <= arr2[j] <= 10^9 for every 0 <= j < len(arr2), and F is a function from integers to integers such that F(x) is in [0, 10^9] for every value x occurring in arr1 or arr2, and F(x) < F(y) whenever x < y and both x and y occur in arr1 or arr2. Define arr1'[i] = F(arr1[i]) and arr2'[j] = F(arr2[j]). -/
theorem spec_10 (arr1 arr2 arr1' arr2' : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9))
    (F : ℤ → ℤ)
    (hFrange : ∀ x : ℤ, x ∈ vals arr1 ∨ x ∈ vals arr2 →
      0 ≤ F x ∧ F x ≤ (10 : ℤ) ^ 9)
    (hFmono : ∀ x y : ℤ, x < y → (x ∈ vals arr1 ∨ x ∈ vals arr2) →
      (y ∈ vals arr1 ∨ y ∈ vals arr2) → F x < F y)
    (h1'len : 1 ≤ arr1'.val.length) (h1'max : arr1'.val.length ≤ 2000)
    (h2'len : 1 ≤ arr2'.val.length) (h2'max : arr2'.val.length ≤ 2000)
    (h1'def : vals arr1' = (vals arr1).map F)
    (h2'def : vals arr2' = (vals arr2).map F) :
    ∀ r r' : Std.I64, impl arr1 arr2 = ok r → impl arr1' arr2' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr1 arr2 arr1' arr2' : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9))
    (F : ℤ → ℤ)
    (hFrange : ∀ x : ℤ, x ∈ vals arr1 ∨ x ∈ vals arr2 →
      0 ≤ F x ∧ F x ≤ (10 : ℤ) ^ 9)
    (hFmono : ∀ x y : ℤ, x < y → (x ∈ vals arr1 ∨ x ∈ vals arr2) →
      (y ∈ vals arr1 ∨ y ∈ vals arr2) → F x < F y)
    (h1'len : 1 ≤ arr1'.val.length) (h1'max : arr1'.val.length ≤ 2000)
    (h2'len : 1 ≤ arr2'.val.length) (h2'max : arr2'.val.length ≤ 2000)
    (h1'def : vals arr1' = (vals arr1).map F)
    (h2'def : vals arr2' = (vals arr2).map F), ∀ r r' : Std.I64, impl arr1 arr2 = ok r → impl arr1' arr2' = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, the integer len(arr1) - r equals the maximum, over all sequences b of length len(arr1) such that: (i) for every i with 0 <= i < len(arr1), either b[i] = arr1[i] or there exists j with 0 <= j < len(arr2) and b[i] = arr2[j]; and (ii) b[i] < b[i+1] for every 0 <= i < len(arr1)-1, of the number of indices i with 0 <= i < len(arr1) and b[i] = arr1[i].
  Preconditions: 1 <= len(arr1) <= 2000, 1 <= len(arr2) <= 2000, 0 <= arr1[i] <= 10^9 for every 0 <= i < len(arr1), and 0 <= arr2[j] <= 10^9 for every 0 <= j < len(arr2). -/
theorem spec_11 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)) :
    ∀ r : Std.I64, impl arr1 arr2 = ok r → 0 ≤ r.val →
      ∃ M : ℕ,
        (∃ b : List ℤ, Obtainable (vals arr1) (vals arr2) b ∧ Matches (vals arr1) b = M) ∧
        (∀ b : List ℤ, Obtainable (vals arr1) (vals arr2) b →
          Matches (vals arr1) b ≤ M) ∧
        (arr1.val.length : ℤ) - r.val = (M : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1max : arr1.val.length ≤ 2000)
    (h2len : 1 ≤ arr2.val.length) (h2max : arr2.val.length ≤ 2000)
    (h1range : ValuesInRange arr1 0 ((10 : ℤ) ^ 9))
    (h2range : ValuesInRange arr2 0 ((10 : ℤ) ^ 9)), ∀ r : Std.I64, impl arr1 arr2 = ok r → 0 ≤ r.val →
      ∃ M : ℕ,
        (∃ b : List ℤ, Obtainable (vals arr1) (vals arr2) b ∧ Matches (vals arr1) b = M) ∧
        (∀ b : List ℤ, Obtainable (vals arr1) (vals arr2) b →
          Matches (vals arr1) b ≤ M) ∧
        (arr1.val.length : ℤ) - r.val = (M : ℤ)) := by
  sorry

end AegisSpec.MakeArrayIncreasing
