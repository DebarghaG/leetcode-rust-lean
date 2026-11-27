import Aegis.EscapeGhosts.Code.Funs

/-!
# Specifications of `Aegis.EscapeGhosts.escape_ghosts`

LeetCode problem `escape-the-ghosts`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.EscapeGhosts

def inRange (x : ℤ) : Prop := -10000 ≤ x ∧ x ≤ 10000

def pt2 (l : List I64) (h : l.length = 2) : ℤ × ℤ :=
  ((l.get ⟨0, by omega⟩).val, (l.get ⟨1, by omega⟩).val)

def l1dist (p q : ℤ × ℤ) : ℤ := |p.1 - q.1| + |p.2 - q.2|

def playerDist (t : ℤ × ℤ) : ℤ := |t.1| + |t.2|

/-- Whenever the function returns a result r, r = true if and only if for every i with 0 <= i < len(ghosts), |ghosts[i][0] - target[0]| + |ghosts[i][1] - target[1]| > |target[0]| + |target[1]|. Equivalently, r = false if and only if there exists i with 0 <= i < len(ghosts) such that |ghosts[i][0] - target[0]| + |ghosts[i][1] - target[1]| <= |target[0]| + |target[1]|.
  Preconditions: len(target) = 2; 1 <= len(ghosts) <= 100; for every i with 0 <= i < len(ghosts), len(ghosts[i]) = 2; every coordinate appearing in target or in any ghosts[i] lies in the interval [-10000, 10000]. -/
theorem spec_1
    (ghosts : Slice (alloc.vec.Vec I64)) (target : Slice I64)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 100)
    (htarget_len : target.val.length = 2)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (r : Bool) (hr : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r) :
    (r = true ↔
      ∀ (i : ℕ) (hi : i < ghosts.val.length),
        l1dist (pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi))
            (pt2 target.val htarget_len)
          > playerDist (pt2 target.val htarget_len)) ∧
    (r = false ↔
      ∃ (i : ℕ) (hi : i < ghosts.val.length),
        l1dist (pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi))
            (pt2 target.val htarget_len)
          ≤ playerDist (pt2 target.val htarget_len)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (ghosts : Slice (alloc.vec.Vec I64)) (target : Slice I64)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 100)
    (htarget_len : target.val.length = 2)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (r : Bool) (hr : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r), (r = true ↔
      ∀ (i : ℕ) (hi : i < ghosts.val.length),
        l1dist (pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi))
            (pt2 target.val htarget_len)
          > playerDist (pt2 target.val htarget_len)) ∧
    (r = false ↔
      ∃ (i : ℕ) (hi : i < ghosts.val.length),
        l1dist (pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi))
            (pt2 target.val htarget_len)
          ≤ playerDist (pt2 target.val htarget_len))) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not overflow, panic, or perform an out-of-bounds access.
  Preconditions: len(target) = 2; 1 <= len(ghosts) <= 100; for every i with 0 <= i < len(ghosts), len(ghosts[i]) = 2; every coordinate appearing in target or in any ghosts[i] lies in the interval [-10000, 10000]. -/
theorem spec_2
    (ghosts : Slice (alloc.vec.Vec I64)) (target : Slice I64)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 100)
    (htarget_len : target.val.length = 2)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val) :
    ∃ r : Bool, Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (ghosts : Slice (alloc.vec.Vec I64)) (target : Slice I64)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 100)
    (htarget_len : target.val.length = 2)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val), ∃ r : Bool, Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r) := by
  sorry

/-- If escape_ghosts(ghosts, target) returns true, then escape_ghosts(ghosts2, target) returns a result equal to true.
  Preconditions: len(target) = 2; 1 <= len(ghosts) <= 100; 1 <= len(ghosts2) <= 100; len(ghosts) = len(ghosts2); for every i with 0 <= i < len(ghosts), len(ghosts[i]) = 2 and len(ghosts2[i]) = 2; every coordinate appearing in target, ghosts, or ghosts2 lies in [-10000, 10000]; for every i with 0 <= i < len(ghosts), |ghosts2[i][0] - target[0]| + |ghosts2[i][1] - target[1]| >= |ghosts[i][0] - target[0]| + |ghosts[i][1] - target[1]|. -/
theorem spec_3
    (ghosts ghosts2 : Slice (alloc.vec.Vec I64)) (target : Slice I64)
    (htarget_len : target.val.length = 2)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 100)
    (hghosts2_nonempty : 1 ≤ ghosts2.val.length)
    (hghosts2_len : ghosts2.val.length ≤ 100)
    (hsame_len : ghosts2.val.length = ghosts.val.length)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (hghosts2_rows : ∀ (i : ℕ) (hi : i < ghosts2.val.length),
      (ghosts2.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (hghosts2_range : ∀ (i : ℕ) (hi : i < ghosts2.val.length) (x : I64),
      x ∈ (ghosts2.val.get ⟨i, hi⟩).val → inRange x.val)
    (hpointwise : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      l1dist (pt2 ((ghosts2.val.get ⟨i, by have := hsame_len; omega⟩).val)
          (hghosts2_rows i (by have := hsame_len; omega)))
          (pt2 target.val htarget_len)
        ≥ l1dist (pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi))
          (pt2 target.val htarget_len)) :
    Aegis.EscapeGhosts.escape_ghosts ghosts target = ok true →
      ∃ r : Bool, Aegis.EscapeGhosts.escape_ghosts ghosts2 target = ok r ∧ r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (ghosts ghosts2 : Slice (alloc.vec.Vec I64)) (target : Slice I64)
    (htarget_len : target.val.length = 2)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 100)
    (hghosts2_nonempty : 1 ≤ ghosts2.val.length)
    (hghosts2_len : ghosts2.val.length ≤ 100)
    (hsame_len : ghosts2.val.length = ghosts.val.length)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (hghosts2_rows : ∀ (i : ℕ) (hi : i < ghosts2.val.length),
      (ghosts2.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (hghosts2_range : ∀ (i : ℕ) (hi : i < ghosts2.val.length) (x : I64),
      x ∈ (ghosts2.val.get ⟨i, hi⟩).val → inRange x.val)
    (hpointwise : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      l1dist (pt2 ((ghosts2.val.get ⟨i, by have := hsame_len; omega⟩).val)
          (hghosts2_rows i (by have := hsame_len; omega)))
          (pt2 target.val htarget_len)
        ≥ l1dist (pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi))
          (pt2 target.val htarget_len)), Aegis.EscapeGhosts.escape_ghosts ghosts target = ok true →
      ∃ r : Bool, Aegis.EscapeGhosts.escape_ghosts ghosts2 target = ok r ∧ r = true) := by
  sorry

/-- Whenever escape_ghosts(ghosts, target) returns r1 and escape_ghosts(ghosts2, target) returns r2, r1 = r2.
  Preconditions: len(target) = 2; len(ghosts) = len(ghosts2) = n with 1 <= n <= 100; for every i with 0 <= i < n, len(ghosts[i]) = 2 and len(ghosts2[i]) = 2; every coordinate appearing in target, ghosts, or ghosts2 lies in [-10000, 10000]; there exists a permutation pi of {0, ..., n-1} such that ghosts2[i][0] = ghosts[pi(i)][0] and ghosts2[i][1] = ghosts[pi(i)][1] for every i with 0 <= i < n. -/
theorem spec_4
    (ghosts ghosts2 : Slice (alloc.vec.Vec I64)) (target : Slice I64) (n : ℕ)
    (htarget_len : target.val.length = 2)
    (hn_nonempty : 1 ≤ n) (hn_len : n ≤ 100)
    (hlen : ghosts.val.length = n)
    (hlen2 : ghosts2.val.length = n)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (hghosts2_rows : ∀ (i : ℕ) (hi : i < ghosts2.val.length),
      (ghosts2.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (hghosts2_range : ∀ (i : ℕ) (hi : i < ghosts2.val.length) (x : I64),
      x ∈ (ghosts2.val.get ⟨i, hi⟩).val → inRange x.val)
    (hperm : ∃ pi : Fin n → Fin n, Function.Bijective pi ∧ ∀ (i : Fin n),
      pt2 ((ghosts2.val.get ⟨i.val, by have := i.isLt; omega⟩).val)
          (hghosts2_rows i.val (by have := i.isLt; omega))
        = pt2 ((ghosts.val.get ⟨(pi i).val, by have := (pi i).isLt; omega⟩).val)
          (hghosts_rows (pi i).val (by have := (pi i).isLt; omega)))
    (r1 r2 : Bool)
    (hr1 : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r1)
    (hr2 : Aegis.EscapeGhosts.escape_ghosts ghosts2 target = ok r2) :
    r1 = r2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (ghosts ghosts2 : Slice (alloc.vec.Vec I64)) (target : Slice I64) (n : ℕ)
    (htarget_len : target.val.length = 2)
    (hn_nonempty : 1 ≤ n) (hn_len : n ≤ 100)
    (hlen : ghosts.val.length = n)
    (hlen2 : ghosts2.val.length = n)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (hghosts2_rows : ∀ (i : ℕ) (hi : i < ghosts2.val.length),
      (ghosts2.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (hghosts2_range : ∀ (i : ℕ) (hi : i < ghosts2.val.length) (x : I64),
      x ∈ (ghosts2.val.get ⟨i, hi⟩).val → inRange x.val)
    (hperm : ∃ pi : Fin n → Fin n, Function.Bijective pi ∧ ∀ (i : Fin n),
      pt2 ((ghosts2.val.get ⟨i.val, by have := i.isLt; omega⟩).val)
          (hghosts2_rows i.val (by have := i.isLt; omega))
        = pt2 ((ghosts.val.get ⟨(pi i).val, by have := (pi i).isLt; omega⟩).val)
          (hghosts_rows (pi i).val (by have := (pi i).isLt; omega)))
    (r1 r2 : Bool)
    (hr1 : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r1)
    (hr2 : Aegis.EscapeGhosts.escape_ghosts ghosts2 target = ok r2), r1 = r2) := by
  sorry

/-- Let target' = [target[1], target[0]] and for each i let ghosts'[i] = [ghosts[i][1], ghosts[i][0]]. Whenever escape_ghosts(ghosts, target) returns r1 and escape_ghosts(ghosts', target') returns r2, r1 = r2.
  Preconditions: len(target) = 2; 1 <= len(ghosts) <= 100; for every i with 0 <= i < len(ghosts), len(ghosts[i]) = 2; every coordinate appearing in target or in any ghosts[i] lies in [-10000, 10000]. -/
theorem spec_5
    (ghosts ghosts' : Slice (alloc.vec.Vec I64)) (target target' : Slice I64)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 100)
    (htarget_len : target.val.length = 2)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (htarget'_len : target'.val.length = 2)
    (hghosts'_len : ghosts'.val.length = ghosts.val.length)
    (hghosts'_rows : ∀ (i : ℕ) (hi : i < ghosts'.val.length),
      (ghosts'.val.get ⟨i, hi⟩).val.length = 2)
    (htarget' : pt2 target'.val htarget'_len
        = ((pt2 target.val htarget_len).2, (pt2 target.val htarget_len).1))
    (hghosts' : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      pt2 ((ghosts'.val.get ⟨i, by have := hghosts'_len; omega⟩).val)
          (hghosts'_rows i (by have := hghosts'_len; omega))
        = ((pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi)).2,
           (pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi)).1))
    (r1 r2 : Bool)
    (hr1 : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r1)
    (hr2 : Aegis.EscapeGhosts.escape_ghosts ghosts' target' = ok r2) :
    r1 = r2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (ghosts ghosts' : Slice (alloc.vec.Vec I64)) (target target' : Slice I64)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 100)
    (htarget_len : target.val.length = 2)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (htarget'_len : target'.val.length = 2)
    (hghosts'_len : ghosts'.val.length = ghosts.val.length)
    (hghosts'_rows : ∀ (i : ℕ) (hi : i < ghosts'.val.length),
      (ghosts'.val.get ⟨i, hi⟩).val.length = 2)
    (htarget' : pt2 target'.val htarget'_len
        = ((pt2 target.val htarget_len).2, (pt2 target.val htarget_len).1))
    (hghosts' : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      pt2 ((ghosts'.val.get ⟨i, by have := hghosts'_len; omega⟩).val)
          (hghosts'_rows i (by have := hghosts'_len; omega))
        = ((pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi)).2,
           (pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi)).1))
    (r1 r2 : Bool)
    (hr1 : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r1)
    (hr2 : Aegis.EscapeGhosts.escape_ghosts ghosts' target' = ok r2), r1 = r2) := by
  sorry

/-- Let target' = [target[0], -target[1]] and for each i let ghosts'[i] = [ghosts[i][0], -ghosts[i][1]]. Whenever escape_ghosts(ghosts, target) returns r1 and escape_ghosts(ghosts', target') returns r2, r1 = r2.
  Preconditions: len(target) = 2; 1 <= len(ghosts) <= 100; for every i with 0 <= i < len(ghosts), len(ghosts[i]) = 2; every coordinate appearing in target or in any ghosts[i] lies in [-10000, 10000]. -/
theorem spec_6
    (ghosts ghosts' : Slice (alloc.vec.Vec I64)) (target target' : Slice I64)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 100)
    (htarget_len : target.val.length = 2)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (htarget'_len : target'.val.length = 2)
    (hghosts'_len : ghosts'.val.length = ghosts.val.length)
    (hghosts'_rows : ∀ (i : ℕ) (hi : i < ghosts'.val.length),
      (ghosts'.val.get ⟨i, hi⟩).val.length = 2)
    (htarget' : pt2 target'.val htarget'_len
        = ((pt2 target.val htarget_len).1, -((pt2 target.val htarget_len).2)))
    (hghosts' : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      pt2 ((ghosts'.val.get ⟨i, by have := hghosts'_len; omega⟩).val)
          (hghosts'_rows i (by have := hghosts'_len; omega))
        = ((pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi)).1,
           -((pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi)).2)))
    (r1 r2 : Bool)
    (hr1 : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r1)
    (hr2 : Aegis.EscapeGhosts.escape_ghosts ghosts' target' = ok r2) :
    r1 = r2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (ghosts ghosts' : Slice (alloc.vec.Vec I64)) (target target' : Slice I64)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 100)
    (htarget_len : target.val.length = 2)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (htarget'_len : target'.val.length = 2)
    (hghosts'_len : ghosts'.val.length = ghosts.val.length)
    (hghosts'_rows : ∀ (i : ℕ) (hi : i < ghosts'.val.length),
      (ghosts'.val.get ⟨i, hi⟩).val.length = 2)
    (htarget' : pt2 target'.val htarget'_len
        = ((pt2 target.val htarget_len).1, -((pt2 target.val htarget_len).2)))
    (hghosts' : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      pt2 ((ghosts'.val.get ⟨i, by have := hghosts'_len; omega⟩).val)
          (hghosts'_rows i (by have := hghosts'_len; omega))
        = ((pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi)).1,
           -((pt2 ((ghosts.val.get ⟨i, hi⟩).val) (hghosts_rows i hi)).2)))
    (r1 r2 : Bool)
    (hr1 : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r1)
    (hr2 : Aegis.EscapeGhosts.escape_ghosts ghosts' target' = ok r2), r1 = r2) := by
  sorry

/-- Whenever escape_ghosts(ghosts, target) returns r1 and escape_ghosts(ghosts', target) returns r2, r1 = r2.
  Preconditions: len(target) = 2; len(ghosts) = n with 1 <= n <= 99; for every i with 0 <= i < n, len(ghosts[i]) = 2; every coordinate appearing in target or in any ghosts[i] lies in [-10000, 10000]; let ghosts' be the slice of length n+1 obtained by appending one additional copy of ghosts[i] for some fixed i with 0 <= i < n. -/
theorem spec_7
    (ghosts ghosts' : Slice (alloc.vec.Vec I64)) (target : Slice I64) (n : ℕ)
    (htarget_len : target.val.length = 2)
    (hn_nonempty : 1 ≤ n) (hn_len : n ≤ 99)
    (hlen : ghosts.val.length = n)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (hghosts'_rows : ∀ (i : ℕ) (hi : i < ghosts'.val.length),
      (ghosts'.val.get ⟨i, hi⟩).val.length = 2)
    (hghosts'_range : ∀ (i : ℕ) (hi : i < ghosts'.val.length) (x : I64),
      x ∈ (ghosts'.val.get ⟨i, hi⟩).val → inRange x.val)
    (hduplicate : ghosts'.val.length = n + 1 ∧
      ∃ (i : ℕ) (hi : i < ghosts.val.length),
        ghosts'.val = ghosts.val ++ [ghosts.val.get ⟨i, hi⟩])
    (r1 r2 : Bool)
    (hr1 : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r1)
    (hr2 : Aegis.EscapeGhosts.escape_ghosts ghosts' target = ok r2) :
    r1 = r2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (ghosts ghosts' : Slice (alloc.vec.Vec I64)) (target : Slice I64) (n : ℕ)
    (htarget_len : target.val.length = 2)
    (hn_nonempty : 1 ≤ n) (hn_len : n ≤ 99)
    (hlen : ghosts.val.length = n)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (hghosts'_rows : ∀ (i : ℕ) (hi : i < ghosts'.val.length),
      (ghosts'.val.get ⟨i, hi⟩).val.length = 2)
    (hghosts'_range : ∀ (i : ℕ) (hi : i < ghosts'.val.length) (x : I64),
      x ∈ (ghosts'.val.get ⟨i, hi⟩).val → inRange x.val)
    (hduplicate : ghosts'.val.length = n + 1 ∧
      ∃ (i : ℕ) (hi : i < ghosts.val.length),
        ghosts'.val = ghosts.val ++ [ghosts.val.get ⟨i, hi⟩])
    (r1 r2 : Bool)
    (hr1 : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r1)
    (hr2 : Aegis.EscapeGhosts.escape_ghosts ghosts' target = ok r2), r1 = r2) := by
  sorry

/-- Whenever escape_ghosts(ghosts, target) returns r1 and escape_ghosts(ghosts', target) returns r2, r2 = true if and only if r1 = true and |g[0] - target[0]| + |g[1] - target[1]| > |target[0]| + |target[1]|. Equivalently, appending one ghost preserves escape exactly when its distance to the target is strictly larger than the player's distance, and otherwise forces false.
  Preconditions: len(target)=2; 1 <= len(ghosts) <= 99; for every i with 0 <= i < len(ghosts), len(ghosts[i])=2; len(g)=2; every coordinate appearing in target, in any ghosts[i], or in g lies in [-10000,10000]; ghosts' is the slice of length len(ghosts)+1 obtained by appending g to ghosts. -/
theorem spec_8
    (ghosts ghosts' : Slice (alloc.vec.Vec I64)) (target : Slice I64) (g : Slice I64)
    (htarget_len : target.val.length = 2)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 99)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (hg_len : g.val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (hg_range : ∀ x ∈ g.val, inRange x.val)
    (happend : ghosts'.val = ghosts.val ++ [alloc.vec.Vec.mk g])
    (r1 r2 : Bool)
    (hr1 : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r1)
    (hr2 : Aegis.EscapeGhosts.escape_ghosts ghosts' target = ok r2) :
    (r2 = true ↔
      r1 = true ∧
        l1dist (pt2 g.val hg_len) (pt2 target.val htarget_len)
          > playerDist (pt2 target.val htarget_len)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (ghosts ghosts' : Slice (alloc.vec.Vec I64)) (target : Slice I64) (g : Slice I64)
    (htarget_len : target.val.length = 2)
    (hghosts_nonempty : 1 ≤ ghosts.val.length)
    (hghosts_len : ghosts.val.length ≤ 99)
    (hghosts_rows : ∀ (i : ℕ) (hi : i < ghosts.val.length),
      (ghosts.val.get ⟨i, hi⟩).val.length = 2)
    (hg_len : g.val.length = 2)
    (htarget_range : ∀ x ∈ target.val, inRange x.val)
    (hghosts_range : ∀ (i : ℕ) (hi : i < ghosts.val.length) (x : I64),
      x ∈ (ghosts.val.get ⟨i, hi⟩).val → inRange x.val)
    (hg_range : ∀ x ∈ g.val, inRange x.val)
    (happend : ghosts'.val = ghosts.val ++ [alloc.vec.Vec.mk g])
    (r1 r2 : Bool)
    (hr1 : Aegis.EscapeGhosts.escape_ghosts ghosts target = ok r1)
    (hr2 : Aegis.EscapeGhosts.escape_ghosts ghosts' target = ok r2), (r2 = true ↔
      r1 = true ∧
        l1dist (pt2 g.val hg_len) (pt2 target.val htarget_len)
          > playerDist (pt2 target.val htarget_len))) := by
  sorry

end AegisSpec.EscapeGhosts
