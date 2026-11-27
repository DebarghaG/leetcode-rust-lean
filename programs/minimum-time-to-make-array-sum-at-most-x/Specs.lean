import Aegis.MinimumTime.Code.Funs

/-!
# Specifications of `Aegis.MinimumTime.minimum_time`

LeetCode problem `minimum-time-to-make-array-sum-at-most-x`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumTime

open Aegis.MinimumTime (minimum_time)

def pairs (nums1 nums2 : Slice Std.I64) : List (Std.I64 × Std.I64) := nums1.val.zip nums2.val

def vals (l : List Std.I64) : List ℤ := l.map (fun a => a.val)

def totalSum (l : List Std.I64) : ℤ := (vals l).sum

def feasibleChoice (ps : List (Std.I64 × Std.I64)) (x : ℤ) (T : ℤ) (s : Fin ps.length → ℤ) : Prop :=
  (∀ i, 0 ≤ s i ∧ s i ≤ T) ∧
  (∀ i j, i ≠ j → 0 < s i → 0 < s j → s i ≠ s j) ∧
  (∑ i : Fin ps.length,
      (if s i = 0 then (ps.get i).1.val + T * (ps.get i).2.val
       else (T - s i) * (ps.get i).2.val)) ≤ x

def feasible (ps : List (Std.I64 × Std.I64)) (x T : ℤ) : Prop :=
  ∃ s : Fin ps.length → ℤ, feasibleChoice ps x T s

def topSum (l : List ℤ) (k : ℕ) : ℤ := ((List.sublistsLen k l).map List.sum).foldr max 0

def toTop (r : ℤ) : WithTop ℤ := if r = -1 then ⊤ else r

def ple (l1 l2 : List Std.I64) : Prop := List.Forall₂ (fun a b => a.val ≤ b.val) l1 l2

/-- Call an integer T >= 0 feasible if there exist integers s_i, one for each i with 0 <= i < n, such that 0 <= s_i <= T, the positive s_i are pairwise distinct, and, writing v_i = nums1[i] + T*nums2[i] when s_i = 0 and v_i = (T - s_i)*nums2[i] when s_i > 0, we have sum_{i=0}^{n-1} v_i <= x. Here s_i = 0 means index i is never reset, and a positive s_i is the last second at which index i is reset. The function returns a result r, and r is completely characterized by: r = -1 if and only if no integer T >= 0 is feasible; and if r >= 0 then r is feasible and every integer T with 0 <= T < r is not feasible.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. All values are integers in the Lean Std.I64 range. -/
theorem spec_1 (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000) :
    ∃ r : Std.I64,
      minimum_time nums1 nums2 x = ok r ∧
      (r.val = -1 ↔ ¬ ∃ T : ℤ, 0 ≤ T ∧ feasible (pairs nums1 nums2) x.val T) ∧
      (0 ≤ r.val →
        feasible (pairs nums1 nums2) x.val r.val ∧
        ∀ T : ℤ, 0 ≤ T → T < r.val → ¬ feasible (pairs nums1 nums2) x.val T) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000), ∃ r : Std.I64,
      minimum_time nums1 nums2 x = ok r ∧
      (r.val = -1 ↔ ¬ ∃ T : ℤ, 0 ≤ T ∧ feasible (pairs nums1 nums2) x.val T) ∧
      (0 ≤ r.val →
        feasible (pairs nums1 nums2) x.val r.val ∧
        ∀ T : ℤ, 0 ≤ T → T < r.val → ¬ feasible (pairs nums1 nums2) x.val T)) := by
  sorry

/-- Under these preconditions, the function returns a result r; it does not fail, panic, index out of bounds, or overflow.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. All values are integers in the Lean Std.I64 range. -/
theorem spec_2 (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000) :
    ∃ r : Std.I64, minimum_time nums1 nums2 x = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000), ∃ r : Std.I64, minimum_time nums1 nums2 x = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r <= n, where n = len(nums1).
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. All values are integers in the Lean Std.I64 range. -/
theorem spec_3 (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000) :
    ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (nums1.val.length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000), ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (nums1.val.length : ℤ))) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if sum_{i=0}^{n-1} nums1[i] <= x.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. All values are integers in the Lean Std.I64 range. -/
theorem spec_4 (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000) :
    ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      (r.val = 0 ↔ totalSum nums1.val ≤ x.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000), ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      (r.val = 0 ↔ totalSum nums1.val ≤ x.val)) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if for every integer T with 0 <= T <= n there do not exist integers s_i, one for each i with 0 <= i < n, such that 0 <= s_i <= T, the positive s_i are pairwise distinct, and, writing v_i = nums1[i] + T*nums2[i] when s_i = 0 and v_i = (T - s_i)*nums2[i] when s_i > 0, we have sum_{i=0}^{n-1} v_i <= x.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. All values are integers in the Lean Std.I64 range. -/
theorem spec_5 (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000) :
    ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      (r.val = -1 ↔
        ∀ T : ℤ, 0 ≤ T → T ≤ (nums1.val.length : ℤ) →
          ¬ feasible (pairs nums1 nums2) x.val T) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000), ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      (r.val = -1 ↔
        ∀ T : ℤ, 0 ≤ T → T ≤ (nums1.val.length : ℤ) →
          ¬ feasible (pairs nums1 nums2) x.val T)) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there exist integers s_i for 0 <= i < n such that 0 <= s_i <= r, the positive s_i are pairwise distinct, and sum_{i=0}^{n-1} (if s_i = 0 then nums1[i] + r*nums2[i] else (r - s_i)*nums2[i]) <= x.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. All values are integers in the Lean Std.I64 range. -/
theorem spec_6 (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000) :
    ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r → 0 ≤ r.val →
      feasible (pairs nums1 nums2) x.val r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000), ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r → 0 ≤ r.val →
      feasible (pairs nums1 nums2) x.val r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for every integer T with 0 <= T < r there do not exist integers s_i for 0 <= i < n such that 0 <= s_i <= T, the positive s_i are pairwise distinct, and sum_{i=0}^{n-1} (if s_i = 0 then nums1[i] + T*nums2[i] else (T - s_i)*nums2[i]) <= x.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. All values are integers in the Lean Std.I64 range. -/
theorem spec_7 (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000) :
    ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r → 0 ≤ r.val →
      ∀ T : ℤ, 0 ≤ T → T < r.val → ¬ feasible (pairs nums1 nums2) x.val T := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000), ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r → 0 ≤ r.val →
      ∀ T : ℤ, 0 ≤ T → T < r.val → ¬ feasible (pairs nums1 nums2) x.val T) := by
  sorry

/-- Whenever the function returns a result r = -1, for every integer T >= 0 and every choice of integers s_i for 0 <= i < n with 0 <= s_i <= T and positive s_i pairwise distinct, we have sum_{i=0}^{n-1} (if s_i = 0 then nums1[i] + T*nums2[i] else (T - s_i)*nums2[i]) > x.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. All values are integers in the Lean Std.I64 range. -/
theorem spec_8 (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000) :
    ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r → r.val = -1 →
      ∀ T : ℤ, 0 ≤ T → ¬ feasible (pairs nums1 nums2) x.val T := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000), ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r → r.val = -1 →
      ∀ T : ℤ, 0 ≤ T → ¬ feasible (pairs nums1 nums2) x.val T) := by
  sorry

/-- Whenever the function returns a result r under these additional assumptions, define top_k = max over subsets S of {0,...,n-1} with size k of sum_{i in S} nums1[i], for 0 <= k <= n, with top_0 = 0. Then r is the least integer k with 0 <= k <= n such that sum_{i=0}^{n-1} nums1[i] - top_k <= x.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. Additionally assume nums2[i] = 0 for every i with 0 <= i < n. All values are integers in the Lean Std.I64 range. -/
theorem spec_9 (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000)
    (h2 : ∀ p ∈ pairs nums1 nums2, p.2.val = 0) :
    ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      ∃ k : ℕ,
        k ≤ nums1.val.length ∧
        r.val = (k : ℤ) ∧
        totalSum nums1.val - topSum (vals nums1.val) k ≤ x.val ∧
        ∀ k' : ℕ, k' < k → ¬ totalSum nums1.val - topSum (vals nums1.val) k' ≤ x.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000)
    (h2 : ∀ p ∈ pairs nums1 nums2, p.2.val = 0), ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      ∃ k : ℕ,
        k ≤ nums1.val.length ∧
        r.val = (k : ℤ) ∧
        totalSum nums1.val - topSum (vals nums1.val) k ≤ x.val ∧
        ∀ k' : ℕ, k' < k → ¬ totalSum nums1.val - topSum (vals nums1.val) k' ≤ x.val) := by
  sorry

/-- Whenever n = 1 and the function returns a result r, r = 0 if nums1[0] <= x, and r = 1 otherwise.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. Additionally assume n = 1. All values are integers in the Lean Std.I64 range. -/
theorem spec_10 (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000)
    (h1 : nums1.val.length = 1) :
    ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      ((nums1.val.get ⟨0, by omega⟩).val ≤ x.val → r.val = 0) ∧
      (x.val < (nums1.val.get ⟨0, by omega⟩).val → r.val = 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000)
    (h1 : nums1.val.length = 1), ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      ((nums1.val.get ⟨0, by omega⟩).val ≤ x.val → r.val = 0) ∧
      (x.val < (nums1.val.get ⟨0, by omega⟩).val → r.val = 1)) := by
  sorry

/-- Whenever the function returns r on (nums1, nums2, x) and returns r' on (nums1', nums2', x), we have r = r'.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. Let pi be any permutation of {0,...,n-1}, and define nums1'[i] = nums1[pi(i)] and nums2'[i] = nums2[pi(i)] for 0 <= i < n; these also satisfy the same bounds. All values are integers in the Lean Std.I64 range. -/
theorem spec_11 (nums1 nums1' nums2 nums2' : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000)
    (hlen1 : nums1'.val.length = nums1.val.length)
    (hlen2 : nums2'.val.length = nums2.val.length)
    (hb' : ∀ p ∈ pairs nums1' nums2',
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hperm : (pairs nums1 nums2).Perm (pairs nums1' nums2')) :
    ∀ r r' : Std.I64,
      minimum_time nums1 nums2 x = ok r →
      minimum_time nums1' nums2' x = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums1' nums2 nums2' : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000)
    (hlen1 : nums1'.val.length = nums1.val.length)
    (hlen2 : nums2'.val.length = nums2.val.length)
    (hb' : ∀ p ∈ pairs nums1' nums2',
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hperm : (pairs nums1 nums2).Perm (pairs nums1' nums2')), ∀ r r' : Std.I64,
      minimum_time nums1 nums2 x = ok r →
      minimum_time nums1' nums2' x = ok r' → r = r') := by
  sorry

/-- Whenever the function returns r1 on (nums1, nums2, x1) and r2 on (nums1, nums2, x2), then, treating -1 as +infinity, we have r2 <= r1.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000. Let x1 and x2 satisfy 0 <= x1 <= x2 <= 1000000. All values are integers in the Lean Std.I64 range. -/
theorem spec_12 (nums1 nums2 : Slice Std.I64) (x1 x2 : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx1 : 0 ≤ x1.val)
    (hx12 : x1.val ≤ x2.val)
    (hx2 : x2.val ≤ 1000000) :
    ∀ r1 r2 : Std.I64,
      minimum_time nums1 nums2 x1 = ok r1 →
      minimum_time nums1 nums2 x2 = ok r2 → toTop r2.val ≤ toTop r1.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x1 x2 : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx1 : 0 ≤ x1.val)
    (hx12 : x1.val ≤ x2.val)
    (hx2 : x2.val ≤ 1000000), ∀ r1 r2 : Std.I64,
      minimum_time nums1 nums2 x1 = ok r1 →
      minimum_time nums1 nums2 x2 = ok r2 → toTop r2.val ≤ toTop r1.val) := by
  sorry

/-- Whenever the function returns r on (nums1, nums2, x) and r' on (nums1, nums2', x), then, treating -1 as +infinity, we have r' >= r.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. Let nums2' be another list of length n such that for every i with 0 <= i < n, 0 <= nums2'[i] <= 1000 and nums2[i] <= nums2'[i]. All values are integers in the Lean Std.I64 range. -/
theorem spec_13 (nums1 nums2 nums2' : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000)
    (hlen2 : nums2'.val.length = nums1.val.length)
    (hb2 : ∀ p ∈ pairs nums1 nums2', 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hmono : ple nums2.val nums2'.val) :
    ∀ r r' : Std.I64,
      minimum_time nums1 nums2 x = ok r →
      minimum_time nums1 nums2' x = ok r' → toTop r.val ≤ toTop r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums1 nums2 nums2' : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000)
    (hlen2 : nums2'.val.length = nums1.val.length)
    (hb2 : ∀ p ∈ pairs nums1 nums2', 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hmono : ple nums2.val nums2'.val), ∀ r r' : Std.I64,
      minimum_time nums1 nums2 x = ok r →
      minimum_time nums1 nums2' x = ok r' → toTop r.val ≤ toTop r'.val) := by
  sorry

/-- Whenever the function returns r on (nums1, nums2, x) and r' on (nums1', nums2, x), then, treating -1 as +infinity, we have r' <= r.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and 0 <= x <= 1000000. Let nums1' be another list of length n such that for every i with 0 <= i < n, 1 <= nums1'[i] <= 1000 and nums1'[i] <= nums1[i]. All values are integers in the Lean Std.I64 range. -/
theorem spec_14 (nums1 nums1' nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000)
    (hlen1 : nums1'.val.length = nums1.val.length)
    (hb1 : ∀ p ∈ pairs nums1' nums2, 1 ≤ p.1.val ∧ p.1.val ≤ 1000)
    (hmono : ple nums1'.val nums1.val) :
    ∀ r r' : Std.I64,
      minimum_time nums1 nums2 x = ok r →
      minimum_time nums1' nums2 x = ok r' → toTop r'.val ≤ toTop r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums1 nums1' nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 1000000)
    (hlen1 : nums1'.val.length = nums1.val.length)
    (hb1 : ∀ p ∈ pairs nums1' nums2, 1 ≤ p.1.val ∧ p.1.val ≤ 1000)
    (hmono : ple nums1'.val nums1.val), ∀ r r' : Std.I64,
      minimum_time nums1 nums2 x = ok r →
      minimum_time nums1' nums2 x = ok r' → toTop r'.val ≤ toTop r.val) := by
  sorry

/-- Whenever x = 0 and the function returns a result r, if there are at least two distinct indices i with nums2[i] > 0 then r = -1; otherwise r = n.
  Preconditions: Let n = len(nums1). We assume len(nums1) = len(nums2), 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000, and x = 0. All values are integers in the Lean Std.I64 range. -/
theorem spec_15 (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx0 : x.val = 0) :
    ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      ((∃ i j : Fin (pairs nums1 nums2).length,
          i ≠ j ∧
          0 < ((pairs nums1 nums2).get i).2.val ∧
          0 < ((pairs nums1 nums2).get j).2.val) → r.val = -1) ∧
      (¬ (∃ i j : Fin (pairs nums1 nums2).length,
          i ≠ j ∧
          0 < ((pairs nums1 nums2).get i).2.val ∧
          0 < ((pairs nums1 nums2).get j).2.val) →
        r.val = (nums1.val.length : ℤ)) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (x : Std.I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 1 ≤ nums1.val.length)
    (hn_hi : nums1.val.length ≤ 1000)
    (hb : ∀ p ∈ pairs nums1 nums2,
      1 ≤ p.1.val ∧ p.1.val ≤ 1000 ∧ 0 ≤ p.2.val ∧ p.2.val ≤ 1000)
    (hx0 : x.val = 0), ∀ r : Std.I64, minimum_time nums1 nums2 x = ok r →
      ((∃ i j : Fin (pairs nums1 nums2).length,
          i ≠ j ∧
          0 < ((pairs nums1 nums2).get i).2.val ∧
          0 < ((pairs nums1 nums2).get j).2.val) → r.val = -1) ∧
      (¬ (∃ i j : Fin (pairs nums1 nums2).length,
          i ≠ j ∧
          0 < ((pairs nums1 nums2).get i).2.val ∧
          0 < ((pairs nums1 nums2).get j).2.val) →
        r.val = (nums1.val.length : ℤ))) := by
  sorry

end AegisSpec.MinimumTime
