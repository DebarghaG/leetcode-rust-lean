import Aegis.FindXSum.Code.Funs

/-!
# Specifications of `Aegis.FindXSum.find_x_sum`

LeetCode problem `find-x-sum-of-all-k-long-subarrays-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindXSum

def entries (nums : Slice I64) : List ℤ := nums.val.map (fun v => v.val)

def outLen (nums : Slice I64) (k : I64) : ℕ := nums.length - k.val.toNat + 1

def winList (nums : Slice I64) (k i : ℕ) : List ℤ := ((entries nums).drop i).take k

def win (nums : Slice I64) (k i : ℕ) : Multiset ℤ := (winList nums k i : Multiset ℤ)

def freq (nums : Slice I64) (k i : ℕ) (v : ℤ) : ℕ := (win nums k i).count v

def distinctVals (nums : Slice I64) (k i : ℕ) : Finset ℤ := (win nums k i).toFinset

def keptSum (w : Multiset ℤ) (S : Finset ℤ) : ℤ := ∑ v ∈ S, v * (w.count v : ℤ)

def IsKept (w : Multiset ℤ) (x : ℕ) (S : Finset ℤ) : Prop :=
  S ⊆ w.toFinset ∧ S.card = min x w.toFinset.card ∧
    ∀ u ∈ S, ∀ v ∈ w.toFinset, v ∉ S →
      w.count v < w.count u ∨ (w.count v = w.count u ∧ v < u)

def keptValues (w : Multiset ℤ) (x : ℕ) : Finset ℤ :=
  w.toFinset.filter
    (fun v => (w.toFinset.filter
      (fun u => w.count v < w.count u ∨ (w.count u = w.count v ∧ v < u))).card < x)

def topValues (T : Finset ℤ) (x : ℕ) : Finset ℤ :=
  T.filter (fun v => (T.filter (fun u => v < u)).card < x)

def getI (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

/-- The function returns a result r such that len(r) = n - k + 1, and for every i with 0 <= i < n - k + 1: let W_i be the multiset of entries nums[j] with i <= j < i+k. For each integer v let f_i(v) be the number of occurrences of v in W_i, and let D_i = {v | f_i(v) > 0}. Then r[i] = sum_{v in S_i} v * f_i(v), where S_i is the unique subset of D_i with |S_i| = min(x, |D_i|) such that for every u in S_i and every v in D_i \ S_i, either f_i(u) > f_i(v), or f_i(u) = f_i(v) and u > v. Equivalently, S_i consists of the min(x, |D_i|) distinct values whose pairs (f_i(v), v) are largest in lexicographic descending order.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting k and x as mathematical integers, 1 <= k <= n and 1 <= x <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. -/
theorem spec_1 (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k →
          ∃ S : Finset ℤ,
            IsKept (win nums k.val.toNat i) x.val.toNat S ∧
              getI r.val i = keptSum (win nums k.val.toNat i) S := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000), ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k →
          ∃ S : Finset ℤ,
            IsKept (win nums k.val.toNat i) x.val.toNat S ∧
              getI r.val i = keptSum (win nums k.val.toNat i) S) := by
  sorry

/-- The function returns a result r and len(r) = n - k + 1.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting k and x as mathematical integers, 1 <= k <= n and 1 <= x <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. -/
theorem spec_2 (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧ r.val.length = outLen nums k := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000), ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧ r.val.length = outLen nums k) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < n - k + 1, r[i] >= x (comparing the mathematical integer value of r[i] with the mathematical integer value of x).
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting k and x as mathematical integers, 1 <= k <= n and 1 <= x <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. -/
theorem spec_3 (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → x.val ≤ getI r.val i := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000), ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → x.val ≤ getI r.val i) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < n - k + 1, r[i] <= sum_{j=i}^{i+k-1} nums[j]. That is, the x-sum of a window never exceeds the ordinary sum of all entries in that window.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting k and x as mathematical integers, 1 <= k <= n and 1 <= x <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. -/
theorem spec_4 (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → getI r.val i ≤ (winList nums k.val.toNat i).sum := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000), ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → getI r.val i ≤ (winList nums k.val.toNat i).sum) := by
  sorry

/-- The function returns a result r; in particular, under the stated constraints it does not fail, panic, access out of bounds, or overflow in computing lengths, frequencies, or sums.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting k and x as mathematical integers, 1 <= k <= n and 1 <= x <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. -/
theorem spec_5 (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000) :
    ∃ r : alloc.vec.Vec I64, Aegis.FindXSum.find_x_sum nums k x = ok r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000), ∃ r : alloc.vec.Vec I64, Aegis.FindXSum.find_x_sum nums k x = ok r) := by
  sorry

/-- The function returns a result r such that len(r) = n and for every i with 0 <= i < n, r[i] = nums[i].
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting k and x as mathematical integers, 1 <= k <= n and 1 <= x <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. Also k = 1. -/
theorem spec_6 (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000)
    (hk_eq : k.val = 1) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = nums.length ∧
        ∀ i, i < nums.length → getI r.val i = getI (entries nums) i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000)
    (hk_eq : k.val = 1), ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = nums.length ∧
        ∀ i, i < nums.length → getI r.val i = getI (entries nums) i) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < n - k + 1: let W_i be the multiset of entries nums[j] with i <= j < i+k and let f_i(v) be the number of occurrences of v in W_i. If v_i is a value occurring in W_i that maximizes the pair (f_i(v), v) in lexicographic descending order, then r[i] = v_i * f_i(v_i).
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting k and x as mathematical integers, 1 <= k <= n and 1 <= x <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. Also x = 1. -/
theorem spec_7 (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000)
    (hx_eq : x.val = 1) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → ∀ v : ℤ,
          v ∈ distinctVals nums k.val.toNat i →
            (∀ u ∈ distinctVals nums k.val.toNat i,
              freq nums k.val.toNat i u < freq nums k.val.toNat i v ∨
                (freq nums k.val.toNat i u = freq nums k.val.toNat i v ∧ u ≤ v)) →
            getI r.val i = v * (freq nums k.val.toNat i v : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000)
    (hx_eq : x.val = 1), ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → ∀ v : ℤ,
          v ∈ distinctVals nums k.val.toNat i →
            (∀ u ∈ distinctVals nums k.val.toNat i,
              freq nums k.val.toNat i u < freq nums k.val.toNat i v ∨
                (freq nums k.val.toNat i u = freq nums k.val.toNat i v ∧ u ≤ v)) →
            getI r.val i = v * (freq nums k.val.toNat i v : ℤ)) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < n - k + 1, if the k entries of the window nums[i..i+k-1] are pairwise distinct, then r[i] equals the sum of the x largest values in that window (if x = k this is the sum of all k entries).
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting k and x as mathematical integers, 1 <= k <= n and 1 <= x <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. -/
theorem spec_8 (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → (winList nums k.val.toNat i).Nodup →
          getI r.val i
            = ∑ v ∈ topValues (distinctVals nums k.val.toNat i) x.val.toNat, v := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000), ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → (winList nums k.val.toNat i).Nodup →
          getI r.val i
            = ∑ v ∈ topValues (distinctVals nums k.val.toNat i) x.val.toNat, v) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < n - k + 1, if the number of distinct values occurring in nums[i..i+k-1] is at most x, then r[i] = sum_{j=i}^{i+k-1} nums[j].
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting k and x as mathematical integers, 1 <= k <= n and 1 <= x <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. -/
theorem spec_9 (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k →
          (distinctVals nums k.val.toNat i).card ≤ x.val.toNat →
            getI r.val i = (winList nums k.val.toNat i).sum := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000), ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k →
          (distinctVals nums k.val.toNat i).card ≤ x.val.toNat →
            getI r.val i = (winList nums k.val.toNat i).sum) := by
  sorry

/-- Let r1 = find_x_sum(nums, k, x1) and r2 = find_x_sum(nums, k, x2). Both calls return results, len(r1) = len(r2) = n - k + 1, and for every i with 0 <= i < n - k + 1, r1[i] <= r2[i] (as mathematical integers).
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting x1, x2, and k as mathematical integers, 1 <= k <= n and 1 <= x1 <= x2 <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. -/
theorem spec_10 (nums : Slice I64) (k x1 x2 : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx1_pos : 1 ≤ x1.val) (hx12 : x1.val ≤ x2.val) (hx2_le : x2.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000) :
    ∃ r1 r2 : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x1 = ok r1 ∧
        Aegis.FindXSum.find_x_sum nums k x2 = ok r2 ∧
        r1.val.length = outLen nums k ∧
        r2.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → getI r1.val i ≤ getI r2.val i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k x1 x2 : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx1_pos : 1 ≤ x1.val) (hx12 : x1.val ≤ x2.val) (hx2_le : x2.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000), ∃ r1 r2 : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x1 = ok r1 ∧
        Aegis.FindXSum.find_x_sum nums k x2 = ok r2 ∧
        r1.val.length = outLen nums k ∧
        r2.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → getI r1.val i ≤ getI r2.val i) := by
  sorry

/-- Let r = find_x_sum(nums, k, x), let nums2 be the slice with nums2[j] = c * nums[j] for every j, and let r2 = find_x_sum(nums2, k, x). Both calls return results, len(r2) = len(r) = n - k + 1, and for every i with 0 <= i < n - k + 1, r2[i] = c * r[i] (as mathematical integers).
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting k and x as mathematical integers, 1 <= k <= n and 1 <= x <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. Let c be a positive integer such that 1 <= c * nums[j] <= 1000000000 for every j with 0 <= j < n. -/
theorem spec_11 (nums nums2 : Slice I64) (k x : I64) (c : ℕ)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000)
    (hc_pos : 0 < c)
    (hlen2 : nums2.length = nums.length)
    (hmap : entries nums2 = (entries nums).map (fun v => (c : ℤ) * v))
    (hbounds2 : ∀ v ∈ entries nums, 1 ≤ (c : ℤ) * v ∧ (c : ℤ) * v ≤ 1000000000) :
    ∃ r r2 : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        Aegis.FindXSum.find_x_sum nums2 k x = ok r2 ∧
        r2.val.length = outLen nums2 k ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → getI r2.val i = (c : ℤ) * getI r.val i := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums2 : Slice I64) (k x : I64) (c : ℕ)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000)
    (hc_pos : 0 < c)
    (hlen2 : nums2.length = nums.length)
    (hmap : entries nums2 = (entries nums).map (fun v => (c : ℤ) * v))
    (hbounds2 : ∀ v ∈ entries nums, 1 ≤ (c : ℤ) * v ∧ (c : ℤ) * v ≤ 1000000000), ∃ r r2 : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        Aegis.FindXSum.find_x_sum nums2 k x = ok r2 ∧
        r2.val.length = outLen nums2 k ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k → getI r2.val i = (c : ℤ) * getI r.val i) := by
  sorry

/-- Let r = find_x_sum(nums, k, x) and r2 = find_x_sum(nums2, k, x). Both calls return results, and for every i with 0 <= i < n - k + 1, if the multiset of entries nums[i..i+k-1] equals the multiset of entries nums2[i..i+k-1], then r[i] = r2[i].
  Preconditions: Let n = len(nums). 1 <= n <= 100000. Interpreting k and x as mathematical integers, 1 <= k <= n and 1 <= x <= k. For every j with 0 <= j < n, 1 <= nums[j] <= 1000000000. Let nums2 be another slice with len(nums2) = n and 1 <= nums2[j] <= 1000000000 for every j with 0 <= j < n. -/
theorem spec_12 (nums nums2 : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000)
    (hlen2 : nums2.length = nums.length)
    (hbounds2 : ∀ v ∈ entries nums2, 1 ≤ v ∧ v ≤ 1000000000) :
    ∃ r r2 : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        Aegis.FindXSum.find_x_sum nums2 k x = ok r2 ∧
        r.val.length = outLen nums k ∧
        r2.val.length = outLen nums2 k ∧
        ∀ i, i < outLen nums k →
          win nums k.val.toNat i = win nums2 k.val.toNat i → getI r.val i = getI r2.val i := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums2 : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000)
    (hlen2 : nums2.length = nums.length)
    (hbounds2 : ∀ v ∈ entries nums2, 1 ≤ v ∧ v ≤ 1000000000), ∃ r r2 : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        Aegis.FindXSum.find_x_sum nums2 k x = ok r2 ∧
        r.val.length = outLen nums k ∧
        r2.val.length = outLen nums2 k ∧
        ∀ i, i < outLen nums k →
          win nums k.val.toNat i = win nums2 k.val.toNat i → getI r.val i = getI r2.val i) := by
  sorry

/-- Let r = find_x_sum(nums,k,x) and r2 = find_x_sum(nums2,k,x). Both return results with len r = len r2 = n-k+1, and for every i with 0 <= i < n-k+1, r2[i] = r[n-k-i] (reversing the input reverses the answer).
  Preconditions: Let n=len(nums). 1 <= n <= 100000, 1 <= k <= n, 1 <= x <= k, 1 <= nums[j] <= 1000000000 for all j; let nums2 be defined by nums2[j] = nums[n-1-j] for 0 <= j < n (so nums2 is also a valid input). -/
theorem spec_13 (nums nums2 : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000)
    (hlen2 : nums2.length = nums.length)
    (hrev : entries nums2 = (entries nums).reverse) :
    ∃ r r2 : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        Aegis.FindXSum.find_x_sum nums2 k x = ok r2 ∧
        r.val.length = outLen nums k ∧
        r2.val.length = outLen nums2 k ∧
        ∀ i, i < outLen nums k → getI r2.val i = getI r.val (nums.length - k.val.toNat - i) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums2 : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000)
    (hlen2 : nums2.length = nums.length)
    (hrev : entries nums2 = (entries nums).reverse), ∃ r r2 : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        Aegis.FindXSum.find_x_sum nums2 k x = ok r2 ∧
        r.val.length = outLen nums k ∧
        r2.val.length = outLen nums2 k ∧
        ∀ i, i < outLen nums k → getI r2.val i = getI r.val (nums.length - k.val.toNat - i)) := by
  sorry

/-- The function returns a result r and, for every i with 0 <= i < n-k+1, r[i] = sum_{j=i}^{i+k-1} nums[j] if AND ONLY IF the number of distinct values occurring in nums[i..i+k-1] is at most x. (S11 only states the 'if' direction; the converse—when more than x distinct values occur at least one positive value is dropped, so the sum is strictly smaller—is the missing part.)
  Preconditions: Let n=len(nums). 1 <= n <= 100000, 1 <= k <= n, 1 <= x <= k, and 1 <= nums[j] <= 1000000000 for all j. -/
theorem spec_14 (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k →
          (getI r.val i = (winList nums k.val.toNat i).sum ↔
            (distinctVals nums k.val.toNat i).card ≤ x.val.toNat) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000), ∃ r : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        r.val.length = outLen nums k ∧
        ∀ i, i < outLen nums k →
          (getI r.val i = (winList nums k.val.toNat i).sum ↔
            (distinctVals nums k.val.toNat i).card ≤ x.val.toNat)) := by
  sorry

/-- Let K_i(x) be the set of distinct values kept from nums[i..i+k-1] when the parameter is x. For every i with 0 <= i < n-k+1, K_i(x1) is a subset of K_i(x2) (the kept-value sets are nested in x); consequently r1[i] <= r2[i] (this strict set-nesting strengthens the sum-monotonicity of spec_10).
  Preconditions: Let n=len(nums). 1 <= n <= 100000, 1 <= k <= n, and 1 <= x1 <= x2 <= k; 1 <= nums[j] <= 1000000000 for all j. -/
theorem spec_15 (nums : Slice I64) (k x1 x2 : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx1_pos : 1 ≤ x1.val) (hx12 : x1.val ≤ x2.val) (hx2_le : x2.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000) :
    ∃ r1 r2 : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x1 = ok r1 ∧
        Aegis.FindXSum.find_x_sum nums k x2 = ok r2 ∧
        r1.val.length = outLen nums k ∧
        r2.val.length = outLen nums k ∧
        (∀ i, i < outLen nums k →
          keptValues (win nums k.val.toNat i) x1.val.toNat ⊆
            keptValues (win nums k.val.toNat i) x2.val.toNat) ∧
        ∀ i, i < outLen nums k → getI r1.val i ≤ getI r2.val i := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice I64) (k x1 x2 : I64)
    (hpos : 1 ≤ nums.length) (hn : nums.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.length : ℤ))
    (hx1_pos : 1 ≤ x1.val) (hx12 : x1.val ≤ x2.val) (hx2_le : x2.val ≤ k.val)
    (hbounds : ∀ v ∈ entries nums, 1 ≤ v ∧ v ≤ 1000000000), ∃ r1 r2 : alloc.vec.Vec I64,
      Aegis.FindXSum.find_x_sum nums k x1 = ok r1 ∧
        Aegis.FindXSum.find_x_sum nums k x2 = ok r2 ∧
        r1.val.length = outLen nums k ∧
        r2.val.length = outLen nums k ∧
        (∀ i, i < outLen nums k →
          keptValues (win nums k.val.toNat i) x1.val.toNat ⊆
            keptValues (win nums k.val.toNat i) x2.val.toNat) ∧
        ∀ i, i < outLen nums k → getI r1.val i ≤ getI r2.val i) := by
  sorry

end AegisSpec.FindXSum
