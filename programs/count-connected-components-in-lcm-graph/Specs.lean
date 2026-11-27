import Aegis.CountComponents.Code.Funs

/-!
# Specifications of `Aegis.CountComponents.count_components`

LeetCode problem `count-connected-components-in-lcm-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountComponents

def valueOf (l : List Aeneas.Std.I64) (i : Nat) : Int := (l.getD i 0#i64).val

def lcmVal (a b : Int) : Int := ((Int.lcm a b : Nat) : Int)

def Edge (l : List Aeneas.Std.I64) (n : Nat) (t : Int) (i j : Nat) : Prop :=
  i < n ∧ j < n ∧ i ≠ j ∧ lcmVal (valueOf l i) (valueOf l j) ≤ t

inductive Reach (l : List Aeneas.Std.I64) (n : Nat) (t : Int) : Nat → Nat → Prop where
  | refl : ∀ i, i < n → Reach l n t i i
  | step : ∀ i j k, Reach l n t i j → Edge l n t j k → Reach l n t i k

noncomputable def component (l : List Aeneas.Std.I64) (n : Nat) (t : Int) (i : Nat) :
    Finset Nat := by
  classical
  exact (Finset.range n).filter (fun j => Reach l n t i j)

noncomputable def componentCount (l : List Aeneas.Std.I64) (n : Nat) (t : Int) : Nat := by
  classical
  exact ((Finset.range n).image (fun i => component l n t i)).card

def maxValue (l : List Aeneas.Std.I64) : Int := (l.map (fun x => x.val)).foldr max 0

def countAbove (l : List Aeneas.Std.I64) (t : Int) : Nat :=
  (l.map (fun x => x.val)).countP (fun v => decide (t < v))

/-- Whenever count_components(nums, threshold) returns a result r, r equals the number of connected components of the undirected graph G whose vertices are the indices 0,1,...,n-1 and in which distinct indices i,j are joined by an edge if and only if lcm(nums[i], nums[j]) <= threshold. A connected component is an equivalence class of the relation i and j are connected, where i and j are connected iff i = j or there is a finite sequence i = p0, p1, ..., pk = j with k >= 0 such that for every t with 1 <= t <= k the pair {p_{t-1}, p_t} is an edge of G. Equivalently, it is a maximal nonempty set of vertices that is connected and has no edge to its complement. The value r is the i64 representation of this count.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; for all distinct i,j with 0 <= i,j < n, nums[i] != nums[j]; and 1 <= threshold <= 200000. -/
theorem spec_1 (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000) :
    ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      r.val = (componentCount nums.val nums.val.length threshold.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000), ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      r.val = (componentCount nums.val nums.val.length threshold.val : Int)) := by
  sorry

/-- For every input satisfying the preconditions, count_components(nums, threshold) returns a result r; in particular it does not panic, fail by arithmetic overflow or underflow, or access nums out of bounds.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; for all distinct i,j with 0 <= i,j < n, nums[i] != nums[j]; and 1 <= threshold <= 200000. -/
theorem spec_2 (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000) :
    ∃ r, Aegis.CountComponents.count_components nums threshold = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000), ∃ r, Aegis.CountComponents.count_components nums threshold = ok r) := by
  sorry

/-- Whenever count_components(nums, threshold) returns a result r, 1 <= r <= n, where n = len(nums).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; for all distinct i,j with 0 <= i,j < n, nums[i] != nums[j]; and 1 <= threshold <= 200000. -/
theorem spec_3 (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000) :
    ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000), ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever count_components(nums, threshold) returns a result r, r = 1.
  Preconditions: Let n = len(nums). Assume n = 1, 1 <= nums[0] <= 1000000000, and 1 <= threshold <= 200000. -/
theorem spec_4 (nums : Slice I64) (threshold : I64)
    (hn : nums.val.length = 1)
    (hpos : 1 ≤ valueOf nums.val 0)
    (hbound : valueOf nums.val 0 ≤ 1000000000)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000) :
    ∀ r, Aegis.CountComponents.count_components nums threshold = ok r → r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (threshold : I64)
    (hn : nums.val.length = 1)
    (hpos : 1 ≤ valueOf nums.val 0)
    (hbound : valueOf nums.val 0 ≤ 1000000000)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000), ∀ r, Aegis.CountComponents.count_components nums threshold = ok r → r.val = 1) := by
  sorry

/-- Whenever count_components(nums, threshold) returns a result r, r = n if and only if for every i,j with 0 <= i < j < n, lcm(nums[i], nums[j]) > threshold. Equivalently, the returned count equals the number of vertices exactly when the graph G has no edges.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; for all distinct i,j with 0 <= i,j < n, nums[i] != nums[j]; and 1 <= threshold <= 200000. -/
theorem spec_5 (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000) :
    ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      (r.val = (nums.val.length : Int) ↔
        ∀ i j, i < j → j < nums.val.length →
          threshold.val < lcmVal (valueOf nums.val i) (valueOf nums.val j)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000), ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      (r.val = (nums.val.length : Int) ↔
        ∀ i j, i < j → j < nums.val.length →
          threshold.val < lcmVal (valueOf nums.val i) (valueOf nums.val j))) := by
  sorry

/-- Whenever count_components(nums, threshold) returns a result r, if for every i,j with 0 <= i < j < n we have lcm(nums[i], nums[j]) <= threshold, then r = 1.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; for all distinct i,j with 0 <= i,j < n, nums[i] != nums[j]; and 1 <= threshold <= 200000. -/
theorem spec_6 (nums : Slice I64) (threshold : I64)
    (hn1 : 2 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hcomplete : ∀ i j, i < j → j < nums.val.length →
      lcmVal (valueOf nums.val i) (valueOf nums.val j) ≤ threshold.val) :
    ∀ r, Aegis.CountComponents.count_components nums threshold = ok r → r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (threshold : I64)
    (hn1 : 2 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hcomplete : ∀ i j, i < j → j < nums.val.length →
      lcmVal (valueOf nums.val i) (valueOf nums.val j) ≤ threshold.val), ∀ r, Aegis.CountComponents.count_components nums threshold = ok r → r.val = 1) := by
  sorry

/-- Whenever count_components(nums, threshold) returns a result r, if threshold = 1 then r = n.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; for all distinct i,j with 0 <= i,j < n, nums[i] != nums[j]; and 1 <= threshold <= 200000. -/
theorem spec_7 (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hteq : threshold.val = 1) :
    ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      r.val = (nums.val.length : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hteq : threshold.val = 1), ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      r.val = (nums.val.length : Int)) := by
  sorry

/-- Whenever count_components(nums, threshold) returns a result r, if there exists k with 0 <= k < n and nums[k] = 1, and if threshold >= M, then r = 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; for all distinct i,j with 0 <= i,j < n, nums[i] != nums[j]; and 1 <= threshold <= 200000. Let M = max{nums[i] | 0 <= i < n}. -/
theorem spec_8 (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hone : ∃ k, k < nums.val.length ∧ valueOf nums.val k = 1)
    (hmax : maxValue nums.val ≤ threshold.val) :
    ∀ r, Aegis.CountComponents.count_components nums threshold = ok r → r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hone : ∃ k, k < nums.val.length ∧ valueOf nums.val k = 1)
    (hmax : maxValue nums.val ≤ threshold.val), ∀ r, Aegis.CountComponents.count_components nums threshold = ok r → r.val = 1) := by
  sorry

/-- Whenever count_components(nums, threshold) returns r and count_components(nums2, threshold) returns r2, we have r = r2.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; for all distinct i,j with 0 <= i,j < n, nums[i] != nums[j]; and 1 <= threshold <= 200000. Let nums2 be any other slice of length n whose entries are a permutation of the entries of nums: there exists a bijection pi from {0,...,n-1} to itself such that nums2[pi(i)] = nums[i] for every i. -/
theorem spec_9 (nums nums2 : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hlen : nums2.val.length = nums.val.length)
    (hperm : ∃ pi : Nat → Nat,
      (∀ i, i < nums.val.length → pi i < nums.val.length) ∧
      (∀ i j, i < nums.val.length → j < nums.val.length → pi i = pi j → i = j) ∧
      (∀ j, j < nums.val.length → ∃ i, i < nums.val.length ∧ pi i = j) ∧
      (∀ i, i < nums.val.length → valueOf nums2.val (pi i) = valueOf nums.val i))
    (r r2 : I64)
    (hr : Aegis.CountComponents.count_components nums threshold = ok r)
    (hr2 : Aegis.CountComponents.count_components nums2 threshold = ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums2 : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hlen : nums2.val.length = nums.val.length)
    (hperm : ∃ pi : Nat → Nat,
      (∀ i, i < nums.val.length → pi i < nums.val.length) ∧
      (∀ i j, i < nums.val.length → j < nums.val.length → pi i = pi j → i = j) ∧
      (∀ j, j < nums.val.length → ∃ i, i < nums.val.length ∧ pi i = j) ∧
      (∀ i, i < nums.val.length → valueOf nums2.val (pi i) = valueOf nums.val i))
    (r r2 : I64)
    (hr : Aegis.CountComponents.count_components nums threshold = ok r)
    (hr2 : Aegis.CountComponents.count_components nums2 threshold = ok r2), r.val = r2.val) := by
  sorry

/-- Whenever count_components(nums, t1) returns r1 and count_components(nums, t2) returns r2, we have r2 <= r1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; for all distinct i,j with 0 <= i,j < n, nums[i] != nums[j]; and let t1,t2 be integers with 1 <= t1 <= t2 <= 200000. -/
theorem spec_10 (nums : Slice I64) (t1 t2 : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ t1.val) (hmono : t1.val ≤ t2.val) (ht2 : t2.val ≤ 200000)
    (r1 r2 : I64)
    (hr1 : Aegis.CountComponents.count_components nums t1 = ok r1)
    (hr2 : Aegis.CountComponents.count_components nums t2 = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (t1 t2 : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ t1.val) (hmono : t1.val ≤ t2.val) (ht2 : t2.val ≤ 200000)
    (r1 r2 : I64)
    (hr1 : Aegis.CountComponents.count_components nums t1 = ok r1)
    (hr2 : Aegis.CountComponents.count_components nums t2 = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Whenever count_components(nums, threshold) returns a result r, r <= n - 1.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; for all distinct i,j with 0 <= i,j < n, nums[i] != nums[j]; 1 <= threshold <= 200000; and there exist distinct indices i,j with 0 <= i,j < n such that lcm(nums[i], nums[j]) <= threshold. -/
theorem spec_11 (nums : Slice I64) (threshold : I64)
    (hn1 : 2 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hedge : ∃ i j, i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
      lcmVal (valueOf nums.val i) (valueOf nums.val j) ≤ threshold.val) :
    ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      r.val ≤ (nums.val.length : Int) - 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (threshold : I64)
    (hn1 : 2 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hedge : ∃ i j, i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
      lcmVal (valueOf nums.val i) (valueOf nums.val j) ≤ threshold.val), ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      r.val ≤ (nums.val.length : Int) - 1) := by
  sorry

/-- Whenever count_components(nums, threshold) returns a result r, r = 1 + the number of indices i with 0 <= i < n and nums[i] > threshold.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; for all distinct i,j with 0 <= i,j < n, nums[i] != nums[j]; 1 <= threshold <= 200000; and there exists k with 0 <= k < n and nums[k] = 1. -/
theorem spec_12 (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hone : ∃ k, k < nums.val.length ∧ valueOf nums.val k = 1) :
    ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      r.val = 1 + (countAbove nums.val threshold.val : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (threshold : I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hpos : ∀ i, i < nums.val.length → 1 ≤ valueOf nums.val i)
    (hbound : ∀ i, i < nums.val.length → valueOf nums.val i ≤ 1000000000)
    (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
      valueOf nums.val i ≠ valueOf nums.val j)
    (ht1 : 1 ≤ threshold.val) (ht2 : threshold.val ≤ 200000)
    (hone : ∃ k, k < nums.val.length ∧ valueOf nums.val k = 1), ∀ r, Aegis.CountComponents.count_components nums threshold = ok r →
      r.val = 1 + (countAbove nums.val threshold.val : Int)) := by
  sorry

end AegisSpec.CountComponents
