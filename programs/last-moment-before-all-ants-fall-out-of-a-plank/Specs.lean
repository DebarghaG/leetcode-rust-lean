import Aegis.GetLastMoment.Code.Funs

/-!
# Specifications of `Aegis.GetLastMoment.get_last_moment`

LeetCode problem `last-moment-before-all-ants-fall-out-of-a-plank`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.GetLastMoment

namespace AegisSpec.GetLastMoment

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def IsMaxOf (s : Finset ℤ) (x : ℤ) : Prop := x ∈ s ∧ ∀ y ∈ s, y ≤ x

def IsMinOf (s : Finset ℤ) (x : ℤ) : Prop := x ∈ s ∧ ∀ y ∈ s, x ≤ y

def momentSet (n : ℤ) (left right : Slice Std.I64) : Finset ℤ :=
  (vals left).toFinset ∪ ((vals right).toFinset).image (fun y => n - y)

def IsMaxMoment (n : ℤ) (left right : Slice Std.I64) (x : ℤ) : Prop :=
  IsMaxOf (momentSet n left right) x

def IsLubMoment (n : ℤ) (left right : Slice Std.I64) (x : ℤ) : Prop :=
  (∀ y ∈ vals left, y ≤ x) ∧ (∀ y ∈ vals right, n - y ≤ x) ∧
    ∀ t : ℤ, (∀ y ∈ vals left, y ≤ t) → (∀ y ∈ vals right, n - y ≤ t) → x ≤ t

/-- Whenever the function returns a result r, r is the maximum of the finite nonempty set T = { left[i] | 0 <= i < len(left) } union { n - right[j] | 0 <= j < len(right) }. Equivalently, r is the least integer t such that t >= left[i] for every i with 0 <= i < len(left) and t >= n - right[j] for every j with 0 <= j < len(right).
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays). -/
theorem spec_1 (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (r : Std.I64) (hr : get_last_moment n left right = ok r) :
    IsMaxMoment n.val left right r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (r : Std.I64) (hr : get_last_moment n left right = ok r), IsMaxMoment n.val left right r.val) := by
  sorry

/-- The function returns a result r (it does not fail with integer overflow, out-of-bounds access, or panic).
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays). -/
theorem spec_2 (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup) :
    ∃ r : Std.I64, get_last_moment n left right = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup), ∃ r : Std.I64, get_last_moment n left right = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n.
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays). -/
theorem spec_3 (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (r : Std.I64) (hr : get_last_moment n left right = ok r) :
    0 ≤ r.val ∧ r.val ≤ n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (r : Std.I64) (hr : get_last_moment n left right = ok r), 0 ≤ r.val ∧ r.val ≤ n.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(left), r >= left[i], and for every j with 0 <= j < len(right), r >= n - right[j].
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays). -/
theorem spec_4 (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (r : Std.I64) (hr : get_last_moment n left right = ok r) :
    (∀ x ∈ vals left, x ≤ r.val) ∧ (∀ y ∈ vals right, n.val - y ≤ r.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (r : Std.I64) (hr : get_last_moment n left right = ok r), (∀ x ∈ vals left, x ≤ r.val) ∧ (∀ y ∈ vals right, n.val - y ≤ r.val)) := by
  sorry

/-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(left) such that left[i] = r, or there exists an index j with 0 <= j < len(right) such that n - right[j] = r.
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays). -/
theorem spec_5 (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (r : Std.I64) (hr : get_last_moment n left right = ok r) :
    (∃ x ∈ vals left, x = r.val) ∨ (∃ y ∈ vals right, n.val - y = r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (r : Std.I64) (hr : get_last_moment n left right = ok r), (∃ x ∈ vals left, x = r.val) ∨ (∃ y ∈ vals right, n.val - y = r.val)) := by
  sorry

/-- Whenever the function returns a result r, r = n - m, where m is the minimum of the nonempty set { right[j] | 0 <= j < len(right) }.
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays); len(left) = 0. -/
theorem spec_6 (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hleft_nil : left.val.length = 0)
    (r : Std.I64) (hr : get_last_moment n left right = ok r) :
    ∃ m : ℤ, IsMinOf (vals right).toFinset m ∧ r.val = n.val - m := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hleft_nil : left.val.length = 0)
    (r : Std.I64) (hr : get_last_moment n left right = ok r), ∃ m : ℤ, IsMinOf (vals right).toFinset m ∧ r.val = n.val - m) := by
  sorry

/-- Whenever the function returns a result r, r = M, where M is the maximum of the nonempty set { left[i] | 0 <= i < len(left) }.
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays); len(right) = 0. -/
theorem spec_7 (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hright_nil : right.val.length = 0)
    (r : Std.I64) (hr : get_last_moment n left right = ok r) :
    ∃ M : ℤ, IsMaxOf (vals left).toFinset M ∧ r.val = M := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hright_nil : right.val.length = 0)
    (r : Std.I64) (hr : get_last_moment n left right = ok r), ∃ M : ℤ, IsMaxOf (vals left).toFinset M ∧ r.val = M) := by
  sorry

/-- Whenever the function returns a result r, r = n.
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays); either there exists i with 0 <= i < len(left) and left[i] = n, or there exists j with 0 <= j < len(right) and right[j] = 0. -/
theorem spec_8 (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hsat : (∃ x ∈ vals left, x = n.val) ∨ (∃ y ∈ vals right, y = 0))
    (r : Std.I64) (hr : get_last_moment n left right = ok r) :
    r.val = n.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hsat : (∃ x ∈ vals left, x = n.val) ∨ (∃ y ∈ vals right, y = 0))
    (r : Std.I64) (hr : get_last_moment n left right = ok r), r.val = n.val) := by
  sorry

/-- Whenever the function returns a result r, if len(left) = 1 then r = left[0], and if len(right) = 1 then r = n - right[0].
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays); len(left) + len(right) = 1. -/
theorem spec_9 (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hone : left.val.length + right.val.length = 1)
    (r : Std.I64) (hr : get_last_moment n left right = ok r) :
    (∀ (_ : left.val.length = 1), r.val = left.val[0].val) ∧
      (∀ (_ : right.val.length = 1), r.val = n.val - right.val[0].val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hone : left.val.length + right.val.length = 1)
    (r : Std.I64) (hr : get_last_moment n left right = ok r), (∀ (_ : left.val.length = 1), r.val = left.val[0].val) ∧
      (∀ (_ : right.val.length = 1), r.val = n.val - right.val[0].val)) := by
  sorry

/-- Let L be any array that is a permutation of left, and let R be any array that is a permutation of right. Whenever the call on (n, left, right) returns r and the call on (n, L, R) returns r', we have r = r'.
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays). -/
theorem spec_10 (n : Std.I64) (left right L R : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hL : L.val.Perm left.val) (hR : R.val.Perm right.val)
    (r r' : Std.I64)
    (hr : get_last_moment n left right = ok r)
    (hr' : get_last_moment n L R = ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (left right L R : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hL : L.val.Perm left.val) (hR : R.val.Perm right.val)
    (r r' : Std.I64)
    (hr : get_last_moment n left right = ok r)
    (hr' : get_last_moment n L R = ok r'), r = r') := by
  sorry

/-- Define L' to be the array of length len(right) with L'[j] = n - right[j] for 0 <= j < len(right), and define R' to be the array of length len(left) with R'[i] = n - left[i] for 0 <= i < len(left). Whenever the call on (n, left, right) returns r and the call on (n, L', R') returns r', we have r = r'.
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays). -/
theorem spec_11 (n : Std.I64) (left right L' R' : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hL' : vals L' = (vals right).map (fun y => n.val - y))
    (hR' : vals R' = (vals left).map (fun y => n.val - y))
    (r r' : Std.I64)
    (hr : get_last_moment n left right = ok r)
    (hr' : get_last_moment n L' R' = ok r') :
    r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (left right L' R' : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hL' : vals L' = (vals right).map (fun y => n.val - y))
    (hR' : vals R' = (vals left).map (fun y => n.val - y))
    (r r' : Std.I64)
    (hr : get_last_moment n left right = ok r)
    (hr' : get_last_moment n L' R' = ok r'), r = r') := by
  sorry

/-- Suppose i is an index with 0 <= i < len(left) and left[i] < max{ left[k] | 0 <= k < len(left) }. Let left' be the array obtained by deleting left[i] from left. Whenever the call on (n, left, right) returns r and the call on (n, left', right) returns r', we have r = r'.
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays). -/
theorem spec_12 (n : Std.I64) (left right left' : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (i : ℕ) (hi : i < left.val.length)
    (hnot_max : ∃ M : ℤ, IsMaxOf (vals left).toFinset M ∧ left.val[i].val < M)
    (hleft' : left'.val = left.val.erase left.val[i])
    (r r' : Std.I64)
    (hr : get_last_moment n left right = ok r)
    (hr' : get_last_moment n left' right = ok r') :
    r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (left right left' : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (i : ℕ) (hi : i < left.val.length)
    (hnot_max : ∃ M : ℤ, IsMaxOf (vals left).toFinset M ∧ left.val[i].val < M)
    (hleft' : left'.val = left.val.erase left.val[i])
    (r r' : Std.I64)
    (hr : get_last_moment n left right = ok r)
    (hr' : get_last_moment n left' right = ok r'), r = r') := by
  sorry

/-- Suppose j is an index with 0 <= j < len(right) and right[j] > min{ right[k] | 0 <= k < len(right) }. Let right' be the array obtained by deleting right[j] from right. Whenever the call on (n, left, right) returns r and the call on (n, left, right') returns r', we have r = r'.
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), 0 <= left[i] <= n; for every j with 0 <= j < len(right), 0 <= right[j] <= n; all values occurring in left and in right are pairwise distinct (no value occurs more than once across both arrays). -/
theorem spec_13 (n : Std.I64) (left right right' : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (j : ℕ) (hj : j < right.val.length)
    (hnot_min : ∃ m : ℤ, IsMinOf (vals right).toFinset m ∧ m < right.val[j].val)
    (hright' : right'.val = right.val.erase right.val[j])
    (r r' : Std.I64)
    (hr : get_last_moment n left right = ok r)
    (hr' : get_last_moment n left right' = ok r') :
    r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (left right right' : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (j : ℕ) (hj : j < right.val.length)
    (hnot_min : ∃ m : ℤ, IsMinOf (vals right).toFinset m ∧ m < right.val[j].val)
    (hright' : right'.val = right.val.erase right.val[j])
    (r r' : Std.I64)
    (hr : get_last_moment n left right = ok r)
    (hr' : get_last_moment n left right' = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: n is an integer with 1 <= n <= 10000; len(left) and len(right) are nonnegative; len(left) <= n + 1 and len(right) <= n + 1; 1 <= len(left) + len(right) <= n + 1; for every i with 0 <= i < len(left), left[i] = 0; for every j with 0 <= j < len(right), right[j] = n; all values occurring in left and in right are pairwise distinct. -/
theorem spec_14 (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_zero : ∀ x ∈ left.val, x.val = 0)
    (hr_n : ∀ y ∈ right.val, y.val = n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (r : Std.I64) (hr : get_last_moment n left right = ok r) :
    r.val = 0 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (left right : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_zero : ∀ x ∈ left.val, x.val = 0)
    (hr_n : ∀ y ∈ right.val, y.val = n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (r : Std.I64) (hr : get_last_moment n left right = ok r), r.val = 0) := by
  sorry

/-- Whenever the call on (n, left, right) returns r and the call on (n, left', right') returns r', we have r' >= r.
  Preconditions: n is an integer with 1 <= n <= 10000; left, right, left', and right' are arrays of integers satisfying the S1 preconditions for both (n, left, right) and (n, left', right'); every value occurring in left occurs in left', and every value occurring in right occurs in right' (so ants are only added, not removed or moved). -/
theorem spec_15 (n : Std.I64) (left right left' right' : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hl'_ub : (left'.val.length : ℤ) ≤ n.val + 1)
    (hr'_ub : (right'.val.length : ℤ) ≤ n.val + 1)
    (hlen'_lo : (1 : ℤ) ≤ (left'.val.length : ℤ) + (right'.val.length : ℤ))
    (hlen'_hi : (left'.val.length : ℤ) + (right'.val.length : ℤ) ≤ n.val + 1)
    (hl'_bounds : ∀ x ∈ left'.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr'_bounds : ∀ y ∈ right'.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup' : (left'.val ++ right'.val).Nodup)
    (hsub_left : ∀ x ∈ vals left, x ∈ vals left')
    (hsub_right : ∀ y ∈ vals right, y ∈ vals right')
    (r r' : Std.I64)
    (hr : get_last_moment n left right = ok r)
    (hr' : get_last_moment n left' right' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n : Std.I64) (left right left' right' : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hl_ub : (left.val.length : ℤ) ≤ n.val + 1)
    (hr_ub : (right.val.length : ℤ) ≤ n.val + 1)
    (hlen_lo : (1 : ℤ) ≤ (left.val.length : ℤ) + (right.val.length : ℤ))
    (hlen_hi : (left.val.length : ℤ) + (right.val.length : ℤ) ≤ n.val + 1)
    (hl_bounds : ∀ x ∈ left.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr_bounds : ∀ y ∈ right.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup : (left.val ++ right.val).Nodup)
    (hl'_ub : (left'.val.length : ℤ) ≤ n.val + 1)
    (hr'_ub : (right'.val.length : ℤ) ≤ n.val + 1)
    (hlen'_lo : (1 : ℤ) ≤ (left'.val.length : ℤ) + (right'.val.length : ℤ))
    (hlen'_hi : (left'.val.length : ℤ) + (right'.val.length : ℤ) ≤ n.val + 1)
    (hl'_bounds : ∀ x ∈ left'.val, 0 ≤ x.val ∧ x.val ≤ n.val)
    (hr'_bounds : ∀ y ∈ right'.val, 0 ≤ y.val ∧ y.val ≤ n.val)
    (hnodup' : (left'.val ++ right'.val).Nodup)
    (hsub_left : ∀ x ∈ vals left, x ∈ vals left')
    (hsub_right : ∀ y ∈ vals right, y ∈ vals right')
    (r r' : Std.I64)
    (hr : get_last_moment n left right = ok r)
    (hr' : get_last_moment n left' right' = ok r'), r.val ≤ r'.val) := by
  sorry

end AegisSpec.GetLastMoment
