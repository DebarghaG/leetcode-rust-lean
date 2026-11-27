import Aegis.Candy.Code.Funs

/-!
# Specifications of `Aegis.Candy.candy`

LeetCode problem `candy`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.Candy

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def lastOf (r : List ℤ) : ℤ := r.getLastD 0

def decFrontRun : List ℤ → ℕ
  | [] => 1
  | [_] => 1
  | x :: y :: t => if x > y then 1 + decFrontRun (y :: t) else 1

def incFrontRun : List ℤ → ℕ
  | [] => 1
  | [_] => 1
  | x :: y :: t => if x < y then 1 + incFrontRun (y :: t) else 1

def incRunEnding (r : List ℤ) (i : ℕ) : ℕ := decFrontRun (r.take (i + 1)).reverse

def decRunStarting (r : List ℤ) (i : ℕ) : ℕ := decFrontRun (r.drop i)

def decRunEnding (r : List ℤ) (i : ℕ) : ℕ := incFrontRun (r.take (i + 1)).reverse

def ValidAssign (r : List ℤ) (c : Fin r.length → ℤ) : Prop :=
  (∀ i : Fin r.length, 1 ≤ c i) ∧
    ∀ i j : Fin r.length, j.val = i.val + 1 →
      (r.get i < r.get j → c i < c j) ∧ (r.get j < r.get i → c j < c i)

def totalSet (r : List ℤ) : Set ℤ :=
  {v | ∃ c : Fin r.length → ℤ, ValidAssign r c ∧ (∑ i, c i) = v}

def witness (r : List ℤ) (i : Fin r.length) : ℤ :=
  ((max (incRunEnding r i.val) (decRunStarting r i.val) : ℕ) : ℤ)

def AllEq (r : List ℤ) : Prop := ∀ i j : Fin r.length, r.get i = r.get j

def AdjIncr (r : List ℤ) : Prop := ∀ i j : Fin r.length, j.val = i.val + 1 → r.get i < r.get j

def AdjDecr (r : List ℤ) : Prop := ∀ i j : Fin r.length, j.val = i.val + 1 → r.get j < r.get i

def SameOrder (r r' : List ℤ) : Prop :=
  r.length = r'.length ∧
    ∀ (i j : ℕ) (hi : i < r.length) (hj : j < r.length) (hi' : i < r'.length)
      (hj' : j < r'.length),
      (r.get ⟨i, hi⟩ < r.get ⟨j, hj⟩ ↔ r'.get ⟨i, hi'⟩ < r'.get ⟨j, hj'⟩) ∧
        (r.get ⟨i, hi⟩ = r.get ⟨j, hj⟩ ↔ r'.get ⟨i, hi'⟩ = r'.get ⟨j, hj'⟩)

/-- Whenever the function returns a result r, r equals the minimum, over all functions c from {0,...,n-1} to the integers, of the sum sum_{i=0}^{n-1} c[i], subject to the constraints: (i) for every i with 0 <= i < n, c[i] >= 1; (ii) for every i with 0 <= i < n-1, if ratings[i] < ratings[i+1] then c[i] < c[i+1], and if ratings[i] > ratings[i+1] then c[i] > c[i+1]. (If ratings[i] = ratings[i+1], there is no constraint between c[i] and c[i+1].)
  Preconditions: n = len(ratings); 1 <= n <= 20000; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. -/
theorem spec_1 (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hres : Aegis.Candy.candy ratings = ok r) :
    IsLeast (totalSet (vals ratings)) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hres : Aegis.Candy.candy ratings = ok r), IsLeast (totalSet (vals ratings)) r.val) := by
  sorry

/-- The function returns a result r (it does not panic, overflow, or otherwise fail).
  Preconditions: n = len(ratings); 1 <= n <= 20000; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. -/
theorem spec_2 (ratings : Slice Std.I64) (n : Usize)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000) :
    ∃ r : Std.I64, Aegis.Candy.candy ratings = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (ratings : Slice Std.I64) (n : Usize)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000), ∃ r : Std.I64, Aegis.Candy.candy ratings = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= n.
  Preconditions: n = len(ratings); 1 <= n <= 20000; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. -/
theorem spec_3 (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hres : Aegis.Candy.candy ratings = ok r) :
    (n.val : ℤ) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hres : Aegis.Candy.candy ratings = ok r), (n.val : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= n*(n+1)/2.
  Preconditions: n = len(ratings); 1 <= n <= 20000; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. -/
theorem spec_4 (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hres : Aegis.Candy.candy ratings = ok r) :
    r.val ≤ (n.val : ℤ) * ((n.val : ℤ) + 1) / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hres : Aegis.Candy.candy ratings = ok r), r.val ≤ (n.val : ℤ) * ((n.val : ℤ) + 1) / 2) := by
  sorry

/-- Whenever the function returns a result r, define for each i with 0 <= i < n: a_i = the largest integer k >= 1 such that for every j with 0 <= j < k-1, the index i-k+1+j >= 0 and ratings[i-k+1+j] < ratings[i-k+2+j] (equivalently, a_i is the length of the maximal contiguous strictly increasing run of ratings ending at index i); b_i = the largest integer k >= 1 such that for every j with 0 <= j < k-1, the index i+j+1 < n and ratings[i+j] > ratings[i+j+1] (equivalently, b_i is the length of the maximal contiguous strictly decreasing run of ratings starting at index i). Then the assignment c* given by c*[i] = max(a_i, b_i) for 0 <= i < n is a valid assignment (as defined in spec_1) and satisfies sum_{i=0}^{n-1} c*[i] = r.
  Preconditions: n = len(ratings); 1 <= n <= 20000; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. -/
theorem spec_5 (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hres : Aegis.Candy.candy ratings = ok r) :
    ValidAssign (vals ratings) (witness (vals ratings)) ∧
      (∑ i : Fin (vals ratings).length, witness (vals ratings) i) = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hres : Aegis.Candy.candy ratings = ok r), ValidAssign (vals ratings) (witness (vals ratings)) ∧
      (∑ i : Fin (vals ratings).length, witness (vals ratings) i) = r.val) := by
  sorry

/-- Whenever the function returns a result r, there is exactly one valid assignment c (as defined in spec_1) with sum_{i=0}^{n-1} c[i] = r.
  Preconditions: n = len(ratings); 1 <= n <= 20000; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. -/
theorem spec_6 (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hres : Aegis.Candy.candy ratings = ok r) :
    ∃! c : Fin (vals ratings).length → ℤ,
      ValidAssign (vals ratings) c ∧ (∑ i, c i) = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hres : Aegis.Candy.candy ratings = ok r), ∃! c : Fin (vals ratings).length → ℤ,
      ValidAssign (vals ratings) c ∧ (∑ i, c i) = r.val) := by
  sorry

/-- Whenever the function returns a result r and ratings[i] = ratings[0] for every i with 0 <= i < n, r = n.
  Preconditions: n = len(ratings); 1 <= n <= 20000; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. -/
theorem spec_7 (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hconst : AllEq (vals ratings))
    (hres : Aegis.Candy.candy ratings = ok r) :
    r.val = (n.val : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hconst : AllEq (vals ratings))
    (hres : Aegis.Candy.candy ratings = ok r), r.val = (n.val : ℤ)) := by
  sorry

/-- Whenever the function returns a result r and ratings[i] < ratings[i+1] for every i with 0 <= i < n-1, r = n*(n+1)/2.
  Preconditions: n = len(ratings); 1 <= n <= 20000; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. -/
theorem spec_8 (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hincr : AdjIncr (vals ratings))
    (hres : Aegis.Candy.candy ratings = ok r) :
    r.val = (n.val : ℤ) * ((n.val : ℤ) + 1) / 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hincr : AdjIncr (vals ratings))
    (hres : Aegis.Candy.candy ratings = ok r), r.val = (n.val : ℤ) * ((n.val : ℤ) + 1) / 2) := by
  sorry

/-- Whenever the function returns a result r and ratings[i] > ratings[i+1] for every i with 0 <= i < n-1, r = n*(n+1)/2.
  Preconditions: n = len(ratings); 1 <= n <= 20000; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. -/
theorem spec_9 (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hdecr : AdjDecr (vals ratings))
    (hres : Aegis.Candy.candy ratings = ok r) :
    r.val = (n.val : ℤ) * ((n.val : ℤ) + 1) / 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (ratings : Slice Std.I64) (n : Usize) (r : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hdecr : AdjDecr (vals ratings))
    (hres : Aegis.Candy.candy ratings = ok r), r.val = (n.val : ℤ) * ((n.val : ℤ) + 1) / 2) := by
  sorry

/-- Whenever the function returns a result r on ratings and a result r' on rev, r = r'.
  Preconditions: Let ratings be any slice with n = len(ratings); 1 <= n <= 20000; for every i, 0 <= ratings[i] <= 20000. Let rev be the slice of length n defined by rev[i] = ratings[n-1-i] for 0 <= i < n. -/
theorem spec_10 (ratings rev : Slice Std.I64) (n : Usize)
    (hn : n = Slice.len ratings) (hnrev : n = Slice.len rev)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hrev : vals rev = (vals ratings).reverse)
    (r r' : Std.I64)
    (hres : Aegis.Candy.candy ratings = ok r) (hres' : Aegis.Candy.candy rev = ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (ratings rev : Slice Std.I64) (n : Usize)
    (hn : n = Slice.len ratings) (hnrev : n = Slice.len rev)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hrev : vals rev = (vals ratings).reverse)
    (r r' : Std.I64)
    (hres : Aegis.Candy.candy ratings = ok r) (hres' : Aegis.Candy.candy rev = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r on ratings and a result r' on ratings', r = r'.
  Preconditions: Let ratings and ratings' be two slices of the same length n; 1 <= n <= 20000; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000 and 0 <= ratings'[i] <= 20000. Suppose for all i, j with 0 <= i, j < n: ratings[i] < ratings[j] if and only if ratings'[i] < ratings'[j], and ratings[i] = ratings[j] if and only if ratings'[i] = ratings'[j]. -/
theorem spec_11 (ratings ratings' : Slice Std.I64) (n : Usize)
    (hn : n = Slice.len ratings) (hn' : n = Slice.len ratings')
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hrat' : ∀ x ∈ ratings'.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hord : SameOrder (vals ratings) (vals ratings'))
    (r r' : Std.I64)
    (hres : Aegis.Candy.candy ratings = ok r) (hres' : Aegis.Candy.candy ratings' = ok r') :
    r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (ratings ratings' : Slice Std.I64) (n : Usize)
    (hn : n = Slice.len ratings) (hn' : n = Slice.len ratings')
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20000)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hrat' : ∀ x ∈ ratings'.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hord : SameOrder (vals ratings) (vals ratings'))
    (r r' : Std.I64)
    (hres : Aegis.Candy.candy ratings = ok r) (hres' : Aegis.Candy.candy ratings' = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r on ratings and a result r' on ratings', r' = r + 1.
  Preconditions: Let ratings be a slice of length n with 1 <= n <= 19999; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. Let v = ratings[n-1]. Let ratings' be the slice of length n+1 defined by ratings'[i] = ratings[i] for 0 <= i < n and ratings'[n] = v. -/
theorem spec_12 (ratings ratings' : Slice Std.I64) (n : Usize)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 19999)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlen' : (vals ratings').length = (vals ratings).length + 1)
    (hcat : vals ratings' = vals ratings ++ [lastOf (vals ratings)])
    (r r' : Std.I64)
    (hres : Aegis.Candy.candy ratings = ok r) (hres' : Aegis.Candy.candy ratings' = ok r') :
    r'.val = r.val + 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (ratings ratings' : Slice Std.I64) (n : Usize)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 19999)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlen' : (vals ratings').length = (vals ratings).length + 1)
    (hcat : vals ratings' = vals ratings ++ [lastOf (vals ratings)])
    (r r' : Std.I64)
    (hres : Aegis.Candy.candy ratings = ok r) (hres' : Aegis.Candy.candy ratings' = ok r'), r'.val = r.val + 1) := by
  sorry

/-- Whenever the function returns a result r on ratings and a result r' on ratings', r' = r + a + 1.
  Preconditions: Let ratings be a slice of length n with 1 <= n <= 19999; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. Let a be the length of the maximal contiguous strictly increasing run ending at index n-1 in ratings, i.e., the largest integer k >= 1 such that for every j with 0 <= j < k-1, ratings[n-k+j] < ratings[n-k+1+j]. Let v be an integer with ratings[n-1] < v <= 20000. Let ratings' be the slice of length n+1 defined by ratings'[i] = ratings[i] for 0 <= i < n and ratings'[n] = v. -/
theorem spec_13 (ratings ratings' : Slice Std.I64) (n : Usize) (v : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 19999)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hv1 : lastOf (vals ratings) < v.val) (hv2 : v.val ≤ 20000)
    (hlen' : (vals ratings').length = (vals ratings).length + 1)
    (hcat : vals ratings' = vals ratings ++ [v.val])
    (r r' : Std.I64)
    (hres : Aegis.Candy.candy ratings = ok r) (hres' : Aegis.Candy.candy ratings' = ok r') :
    r'.val = r.val + ((incRunEnding (vals ratings) (n.val - 1) : ℕ) : ℤ) + 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (ratings ratings' : Slice Std.I64) (n : Usize) (v : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 19999)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hv1 : lastOf (vals ratings) < v.val) (hv2 : v.val ≤ 20000)
    (hlen' : (vals ratings').length = (vals ratings).length + 1)
    (hcat : vals ratings' = vals ratings ++ [v.val])
    (r r' : Std.I64)
    (hres : Aegis.Candy.candy ratings = ok r) (hres' : Aegis.Candy.candy ratings' = ok r'), r'.val = r.val + ((incRunEnding (vals ratings) (n.val - 1) : ℕ) : ℤ) + 1) := by
  sorry

/-- Whenever the function returns a result r on ratings and a result r' on ratings', r' = r + d + (if a <= d then 1 else 0). Equivalently, r' = r + d + 1 when a <= d, and r' = r + d when a > d.
  Preconditions: Let ratings be a slice of length n with 1 <= n <= 19999; for every i with 0 <= i < n, 0 <= ratings[i] <= 20000. Let d be the length of the maximal contiguous strictly decreasing run ending at index n-1 in ratings, i.e., the largest integer k >= 1 such that for every j with 0 <= j < k-1, ratings[n-k+j] > ratings[n-k+1+j]. Let s = n - d. Let a be the length of the maximal contiguous strictly increasing run ending at index s in ratings, i.e., the largest integer k >= 1 such that for every j with 0 <= j < k-1, s-k+1+j >= 0 and ratings[s-k+1+j] < ratings[s-k+2+j]. Let v be an integer with 0 <= v < ratings[n-1]. Let ratings' be the slice of length n+1 defined by ratings'[i] = ratings[i] for 0 <= i < n and ratings'[n] = v. -/
theorem spec_14 (ratings ratings' : Slice Std.I64) (n : Usize) (v : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 19999)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hv1 : 0 ≤ v.val) (hv2 : v.val < lastOf (vals ratings))
    (hlen' : (vals ratings').length = (vals ratings).length + 1)
    (hcat : vals ratings' = vals ratings ++ [v.val])
    (r r' : Std.I64)
    (hres : Aegis.Candy.candy ratings = ok r) (hres' : Aegis.Candy.candy ratings' = ok r') :
    r'.val = r.val + ((decRunEnding (vals ratings) (n.val - 1) : ℕ) : ℤ) +
      (if incRunEnding (vals ratings) (n.val - decRunEnding (vals ratings) (n.val - 1)) ≤
          decRunEnding (vals ratings) (n.val - 1) then 1 else 0) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (ratings ratings' : Slice Std.I64) (n : Usize) (v : Std.I64)
    (hn : n = Slice.len ratings) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 19999)
    (hrat : ∀ x ∈ ratings.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hv1 : 0 ≤ v.val) (hv2 : v.val < lastOf (vals ratings))
    (hlen' : (vals ratings').length = (vals ratings).length + 1)
    (hcat : vals ratings' = vals ratings ++ [v.val])
    (r r' : Std.I64)
    (hres : Aegis.Candy.candy ratings = ok r) (hres' : Aegis.Candy.candy ratings' = ok r'), r'.val = r.val + ((decRunEnding (vals ratings) (n.val - 1) : ℕ) : ℤ) +
      (if incRunEnding (vals ratings) (n.val - decRunEnding (vals ratings) (n.val - 1)) ≤
          decRunEnding (vals ratings) (n.val - 1) then 1 else 0)) := by
  sorry

end AegisSpec.Candy
