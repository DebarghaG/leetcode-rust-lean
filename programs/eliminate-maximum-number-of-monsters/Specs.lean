import Aegis.EliminateMaximum.Code.Funs
import Mathlib.Data.Real.Basic

/-!
# Specifications of `Aegis.EliminateMaximum.eliminate_maximum`

LeetCode problem `eliminate-maximum-number-of-monsters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.EliminateMaximum

namespace AegisSpec.EliminateMaximum

def get64 (s : Slice Std.I64) (i : ℕ) : ℤ := (s.val.getD i default).val

def lenOf (dist : Slice Std.I64) : ℕ := dist.val.length

noncomputable def ratio (dist speed : Slice Std.I64) (i : ℕ) : ℝ :=
  (get64 dist i : ℝ) / (get64 speed i : ℝ)

noncomputable def ratios (dist speed : Slice Std.I64) : List ℝ :=
  (List.range (lenOf dist)).map (fun i => ratio dist speed i)

noncomputable def b (dist speed : Slice Std.I64) : List ℝ := by
  classical
  exact List.insertionSort (fun x y : ℝ => x ≤ y) (ratios dist speed)

def entry (l : List ℝ) (j : ℤ) : ℝ := l.getD j.toNat 0

noncomputable def bget (dist speed : Slice Std.I64) (j : ℤ) : ℝ := entry (b dist speed) j

def C (dist speed : Slice Std.I64) (k : ℤ) : ℕ :=
  ((Finset.range (lenOf dist)).filter
    (fun i => get64 dist i ≤ k * get64 speed i)).card

def Pre (dist speed : Slice Std.I64) : Prop :=
  lenOf speed = lenOf dist ∧
    1 ≤ lenOf dist ∧ lenOf dist ≤ 100000 ∧
    (∀ i : ℕ, i < lenOf dist → 1 ≤ get64 dist i ∧ get64 dist i ≤ 100000) ∧
    (∀ i : ℕ, i < lenOf dist → 1 ≤ get64 speed i ∧ get64 speed i ≤ 100000)

noncomputable def IsAnswer (dist speed : Slice Std.I64) (r : ℤ) : Prop :=
  0 ≤ r ∧ r ≤ (lenOf dist : ℤ) ∧
    (∀ j : ℤ, 0 ≤ j → j < r → (j : ℝ) < bget dist speed j) ∧
    (r < (lenOf dist : ℤ) → bget dist speed r ≤ (r : ℝ))

/-- The function returns a result r and, letting b be the nondecreasing list of the n real numbers dist[i]/speed[i] for 0 <= i < n, r is the unique integer with 0 <= r <= n such that: (a) for every integer j with 0 <= j < r, b[j] > j; and (b) if r < n, then b[r] <= r.
  Preconditions: Let n = len(dist) = len(speed). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= dist[i] <= 100000 and 1 <= speed[i] <= 100000. -/
theorem spec_1 (dist speed : Slice Std.I64) (h : Pre dist speed) :
    ∃ r : Std.I64,
      eliminate_maximum dist speed = ok r ∧ IsAnswer dist speed r.val ∧
        ∀ r' : ℤ, IsAnswer dist speed r' → r' = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (dist speed : Slice Std.I64) (h : Pre dist speed), ∃ r : Std.I64,
      eliminate_maximum dist speed = ok r ∧ IsAnswer dist speed r.val ∧
        ∀ r' : ℤ, IsAnswer dist speed r' → r' = r.val) := by
  sorry

/-- The function returns a result r and 0 <= r <= n.
  Preconditions: Let n = len(dist) = len(speed). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= dist[i] <= 100000 and 1 <= speed[i] <= 100000. -/
theorem spec_2 (dist speed : Slice Std.I64) (h : Pre dist speed) :
    ∃ r : Std.I64,
      eliminate_maximum dist speed = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (lenOf dist : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (dist speed : Slice Std.I64) (h : Pre dist speed), ∃ r : Std.I64,
      eliminate_maximum dist speed = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (lenOf dist : ℤ)) := by
  sorry

/-- The function does not fail: it returns some result r.
  Preconditions: Let n = len(dist) = len(speed). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= dist[i] <= 100000 and 1 <= speed[i] <= 100000. -/
theorem spec_3 (dist speed : Slice Std.I64) (h : Pre dist speed) :
    ∃ r : Std.I64, eliminate_maximum dist speed = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (dist speed : Slice Std.I64) (h : Pre dist speed), ∃ r : Std.I64, eliminate_maximum dist speed = ok r) := by
  sorry

/-- The function returns a result r and r >= 1.
  Preconditions: Let n = len(dist) = len(speed). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= dist[i] <= 100000 and 1 <= speed[i] <= 100000. -/
theorem spec_4 (dist speed : Slice Std.I64) (h : Pre dist speed) :
    ∃ r : Std.I64, eliminate_maximum dist speed = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (dist speed : Slice Std.I64) (h : Pre dist speed), ∃ r : Std.I64, eliminate_maximum dist speed = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns the result 1.
  Preconditions: Let n = len(dist) = len(speed), n = 1, and assume 1 <= dist[0] <= 100000 and 1 <= speed[0] <= 100000. -/
theorem spec_5 (dist speed : Slice Std.I64) (h : Pre dist speed) (h1 : lenOf dist = 1) :
    eliminate_maximum dist speed = ok (1#i64) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (dist speed : Slice Std.I64) (h : Pre dist speed) (h1 : lenOf dist = 1), eliminate_maximum dist speed = ok (1#i64)) := by
  sorry

/-- The function returns a result r with 0 <= r <= n and, for every integer k with 0 <= k < r, C(k) <= k, where C(k) denotes the number of indices i with 0 <= i < n and dist[i] <= k*speed[i].
  Preconditions: Let n = len(dist) = len(speed). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= dist[i] <= 100000 and 1 <= speed[i] <= 100000. -/
theorem spec_6 (dist speed : Slice Std.I64) (h : Pre dist speed) :
    ∃ r : Std.I64,
      eliminate_maximum dist speed = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (lenOf dist : ℤ) ∧
        ∀ k : ℤ, 0 ≤ k → k < r.val → (C dist speed k : ℤ) ≤ k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (dist speed : Slice Std.I64) (h : Pre dist speed), ∃ r : Std.I64,
      eliminate_maximum dist speed = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (lenOf dist : ℤ) ∧
        ∀ k : ℤ, 0 ≤ k → k < r.val → (C dist speed k : ℤ) ≤ k) := by
  sorry

/-- The function returns a result r with 0 <= r <= n and, if r < n, then C(r) >= r+1, where C(k) denotes the number of indices i with 0 <= i < n and dist[i] <= k*speed[i].
  Preconditions: Let n = len(dist) = len(speed). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= dist[i] <= 100000 and 1 <= speed[i] <= 100000. -/
theorem spec_7 (dist speed : Slice Std.I64) (h : Pre dist speed) :
    ∃ r : Std.I64,
      eliminate_maximum dist speed = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (lenOf dist : ℤ) ∧
        (r.val < (lenOf dist : ℤ) → r.val + 1 ≤ (C dist speed r.val : ℤ)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (dist speed : Slice Std.I64) (h : Pre dist speed), ∃ r : Std.I64,
      eliminate_maximum dist speed = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (lenOf dist : ℤ) ∧
        (r.val < (lenOf dist : ℤ) → r.val + 1 ≤ (C dist speed r.val : ℤ))) := by
  sorry

/-- The function returns a result r with 0 <= r <= n, and r = n if and only if C(k) <= k for every integer k with 0 <= k < n, where C(k) denotes the number of indices i with 0 <= i < n and dist[i] <= k*speed[i].
  Preconditions: Let n = len(dist) = len(speed). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= dist[i] <= 100000 and 1 <= speed[i] <= 100000. -/
theorem spec_8 (dist speed : Slice Std.I64) (h : Pre dist speed) :
    ∃ r : Std.I64,
      eliminate_maximum dist speed = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (lenOf dist : ℤ) ∧
        (r.val = (lenOf dist : ℤ) ↔
          ∀ k : ℤ, 0 ≤ k → k < (lenOf dist : ℤ) → (C dist speed k : ℤ) ≤ k) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (dist speed : Slice Std.I64) (h : Pre dist speed), ∃ r : Std.I64,
      eliminate_maximum dist speed = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (lenOf dist : ℤ) ∧
        (r.val = (lenOf dist : ℤ) ↔
          ∀ k : ℤ, 0 ≤ k → k < (lenOf dist : ℤ) → (C dist speed k : ℤ) ≤ k)) := by
  sorry

/-- The function returns the result n.
  Preconditions: Let n = len(dist) = len(speed). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= dist[i] <= 100000 and 1 <= speed[i] <= 100000. Also assume that for every i with 0 <= i < n, dist[i] > (n-1)*speed[i]. -/
theorem spec_9 (dist speed : Slice Std.I64) (h : Pre dist speed)
    (hbig : ∀ i : ℕ, i < lenOf dist → ((lenOf dist : ℤ) - 1) * get64 speed i < get64 dist i) :
    ∃ r : Std.I64, eliminate_maximum dist speed = ok r ∧ r.val = (lenOf dist : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (dist speed : Slice Std.I64) (h : Pre dist speed)
    (hbig : ∀ i : ℕ, i < lenOf dist → ((lenOf dist : ℤ) - 1) * get64 speed i < get64 dist i), ∃ r : Std.I64, eliminate_maximum dist speed = ok r ∧ r.val = (lenOf dist : ℤ)) := by
  sorry

/-- Whenever eliminate_maximum(dist, speed) returns r and eliminate_maximum(dist2, speed2) returns r2, we have r = r2.
  Preconditions: Let dist and speed satisfy the general preconditions with n = len(dist) = len(speed). Let dist2 and speed2 be slices of length n satisfying 1 <= dist2[i] <= 100000 and 1 <= speed2[i] <= 100000 for all i. Suppose there is a permutation pi of {0,...,n-1} such that dist2[i] = dist[pi(i)] and speed2[i] = speed[pi(i)] for every i with 0 <= i < n. -/
theorem spec_10 (dist speed dist2 speed2 : Slice Std.I64)
    (h : Pre dist speed) (h2 : Pre dist2 speed2) (hlen : lenOf dist2 = lenOf dist)
    (hperm : ∃ π : Equiv.Perm (Fin (lenOf dist)),
      ∀ i : Fin (lenOf dist),
        get64 dist2 i.val = get64 dist (π i).val ∧
          get64 speed2 i.val = get64 speed (π i).val) :
    ∀ r r2 : Std.I64,
      eliminate_maximum dist speed = ok r → eliminate_maximum dist2 speed2 = ok r2 → r = r2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (dist speed dist2 speed2 : Slice Std.I64)
    (h : Pre dist speed) (h2 : Pre dist2 speed2) (hlen : lenOf dist2 = lenOf dist)
    (hperm : ∃ π : Equiv.Perm (Fin (lenOf dist)),
      ∀ i : Fin (lenOf dist),
        get64 dist2 i.val = get64 dist (π i).val ∧
          get64 speed2 i.val = get64 speed (π i).val), ∀ r r2 : Std.I64,
      eliminate_maximum dist speed = ok r → eliminate_maximum dist2 speed2 = ok r2 → r = r2) := by
  sorry

/-- Whenever eliminate_maximum(dist, speed) returns r and eliminate_maximum on the scaled slices dist2[i] = c*dist[i] and speed2[i] = c*speed[i] returns r2, we have r = r2.
  Preconditions: Let dist and speed satisfy the general preconditions with n = len(dist) = len(speed). Let c be a positive integer such that 1 <= c*dist[i] <= 100000 and 1 <= c*speed[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_11 (dist speed dist2 speed2 : Slice Std.I64) (c : ℤ)
    (h : Pre dist speed) (hc : 0 < c)
    (hcd : ∀ i : ℕ, i < lenOf dist → 1 ≤ c * get64 dist i ∧ c * get64 dist i ≤ 100000)
    (hcs : ∀ i : ℕ, i < lenOf dist → 1 ≤ c * get64 speed i ∧ c * get64 speed i ≤ 100000)
    (h2 : Pre dist2 speed2) (hlen : lenOf dist2 = lenOf dist)
    (hd2 : ∀ i : ℕ, i < lenOf dist → get64 dist2 i = c * get64 dist i)
    (hs2 : ∀ i : ℕ, i < lenOf dist → get64 speed2 i = c * get64 speed i) :
    ∀ r r2 : Std.I64,
      eliminate_maximum dist speed = ok r → eliminate_maximum dist2 speed2 = ok r2 → r = r2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (dist speed dist2 speed2 : Slice Std.I64) (c : ℤ)
    (h : Pre dist speed) (hc : 0 < c)
    (hcd : ∀ i : ℕ, i < lenOf dist → 1 ≤ c * get64 dist i ∧ c * get64 dist i ≤ 100000)
    (hcs : ∀ i : ℕ, i < lenOf dist → 1 ≤ c * get64 speed i ∧ c * get64 speed i ≤ 100000)
    (h2 : Pre dist2 speed2) (hlen : lenOf dist2 = lenOf dist)
    (hd2 : ∀ i : ℕ, i < lenOf dist → get64 dist2 i = c * get64 dist i)
    (hs2 : ∀ i : ℕ, i < lenOf dist → get64 speed2 i = c * get64 speed i), ∀ r r2 : Std.I64,
      eliminate_maximum dist speed = ok r → eliminate_maximum dist2 speed2 = ok r2 → r = r2) := by
  sorry

/-- For every integer k with 0 <= k < n, if C(k) >= k+1, then the function returns a result r with r <= k, where C(k) denotes the number of indices i with 0 <= i < n and dist[i] <= k*speed[i].
  Preconditions: Let n = len(dist) = len(speed). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= dist[i] <= 100000 and 1 <= speed[i] <= 100000. -/
theorem spec_12 (dist speed : Slice Std.I64) (h : Pre dist speed) (k : ℤ)
    (hk0 : 0 ≤ k) (hkn : k < (lenOf dist : ℤ)) (hkC : k + 1 ≤ (C dist speed k : ℤ)) :
    ∃ r : Std.I64, eliminate_maximum dist speed = ok r ∧ r.val ≤ k := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (dist speed : Slice Std.I64) (h : Pre dist speed) (k : ℤ)
    (hk0 : 0 ≤ k) (hkn : k < (lenOf dist : ℤ)) (hkC : k + 1 ≤ (C dist speed k : ℤ)), ∃ r : Std.I64, eliminate_maximum dist speed = ok r ∧ r.val ≤ k) := by
  sorry

end AegisSpec.EliminateMaximum
