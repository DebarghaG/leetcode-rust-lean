import Aegis.GetSubarrayBeauty.Code.Funs

/-!
# Specifications of `Aegis.GetSubarrayBeauty.get_subarray_beauty`

LeetCode problem `sliding-subarray-beauty`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetSubarrayBeauty

def sliceVals (nums : Slice I64) : List ℤ := nums.val.map (fun v => v.val)

def vecVals (r : alloc.vec.Vec I64) : List ℤ := r.val.map (fun v => v.val)

def negWindow (l : List ℤ) (s k : ℕ) : List ℤ :=
  ((l.drop s).take k).filter (fun v => v < 0)

def sortedNegWindow (l : List ℤ) (s k : ℕ) : List ℤ :=
  (negWindow l s k).mergeSort

def negCount (l : List ℤ) (s k : ℕ) : ℕ :=
  (negWindow l s k).length

def negCountLt (l : List ℤ) (s k : ℕ) (v : ℤ) : ℕ :=
  (negWindow l s k).countP (fun u => u < v)

def negCountLe (l : List ℤ) (s k : ℕ) (v : ℤ) : ℕ :=
  (negWindow l s k).countP (fun u => u ≤ v)

def beauty (l : List ℤ) (s k x : ℕ) : ℤ :=
  if (negWindow l s k).length < x then 0
  else (sortedNegWindow l s k)[x - 1]?.getD 0

def negMultisetEq (l l' : List ℤ) (s t k : ℕ) : Prop :=
  (negWindow l s k).Perm (negWindow l' t k)

/-- Whenever the function returns a result r, len(r) = n - k + 1 and, for every s with 0 <= s <= n-k, r[s] = beauty(s), where for a start s we let W_s be the multiset {nums[i] | s <= i < s+k}, let N_s be the sub-multiset of negative elements of W_s, and let beauty(s) be 0 if |N_s| < x, and otherwise the x-th element of N_s sorted nondecreasingly (1-indexed, with equal values counted with multiplicity).
  Preconditions: Let n = len(nums). The slice nums is nonempty: 1 <= n <= 100000. For every i with 0 <= i < n, -50 <= nums[i] <= 50. The i64 arguments k and x, regarded as mathematical integers, satisfy 1 <= k <= n and 1 <= x <= k. -/
theorem spec_1 (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val) :
    ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        (vecVals r).length = nums.val.length - k.val.toNat + 1 ∧
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          (vecVals r)[s]? = some (beauty (sliceVals nums) s k.val.toNat x.val.toNat) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val), ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        (vecVals r).length = nums.val.length - k.val.toNat + 1 ∧
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          (vecVals r)[s]? = some (beauty (sliceVals nums) s k.val.toNat x.val.toNat)) := by
  sorry

/-- Under these preconditions, the function returns a result r (it does not fail).
  Preconditions: Let n = len(nums). The slice nums is nonempty: 1 <= n <= 100000. For every i with 0 <= i < n, -50 <= nums[i] <= 50. The i64 arguments k and x, regarded as mathematical integers, satisfy 1 <= k <= n and 1 <= x <= k. -/
theorem spec_2 (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val), ∃ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = n - k + 1.
  Preconditions: Let n = len(nums). The slice nums is nonempty: 1 <= n <= 100000. For every i with 0 <= i < n, -50 <= nums[i] <= 50. The i64 arguments k and x, regarded as mathematical integers, satisfy 1 <= k <= n and 1 <= x <= k. -/
theorem spec_3 (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val) :
    ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        (vecVals r).length = nums.val.length - k.val.toNat + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val), ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        (vecVals r).length = nums.val.length - k.val.toNat + 1) := by
  sorry

/-- Whenever the function returns a result r, for every s with 0 <= s <= n-k, -50 <= r[s] <= 0.
  Preconditions: Let n = len(nums). The slice nums is nonempty: 1 <= n <= 100000. For every i with 0 <= i < n, -50 <= nums[i] <= 50. The i64 arguments k and x, regarded as mathematical integers, satisfy 1 <= k <= n and 1 <= x <= k. -/
theorem spec_4 (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val) :
    ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          ∀ (v : ℤ), (vecVals r)[s]? = some v → -50 ≤ v ∧ v ≤ 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val), ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          ∀ (v : ℤ), (vecVals r)[s]? = some v → -50 ≤ v ∧ v ≤ 0) := by
  sorry

/-- Whenever the function returns a result r, for every s with 0 <= s <= n-k, if r[s] < 0 then there exists an index i with s <= i < s+k such that nums[i] = r[s].
  Preconditions: Let n = len(nums). The slice nums is nonempty: 1 <= n <= 100000. For every i with 0 <= i < n, -50 <= nums[i] <= 50. The i64 arguments k and x, regarded as mathematical integers, satisfy 1 <= k <= n and 1 <= x <= k. -/
theorem spec_5 (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val) :
    ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          ∀ (v : ℤ), (vecVals r)[s]? = some v → v < 0 →
            ∃ (i : ℕ), s ≤ i ∧ i < s + k.val.toNat ∧ (sliceVals nums)[i]? = some v := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val), ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          ∀ (v : ℤ), (vecVals r)[s]? = some v → v < 0 →
            ∃ (i : ℕ), s ≤ i ∧ i < s + k.val.toNat ∧ (sliceVals nums)[i]? = some v) := by
  sorry

/-- Whenever the function returns a result r, for every s with 0 <= s <= n-k, r[s] = 0 if and only if the number of indices i with s <= i < s+k and nums[i] < 0 is less than x.
  Preconditions: Let n = len(nums). The slice nums is nonempty: 1 <= n <= 100000. For every i with 0 <= i < n, -50 <= nums[i] <= 50. The i64 arguments k and x, regarded as mathematical integers, satisfy 1 <= k <= n and 1 <= x <= k. -/
theorem spec_6 (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val) :
    ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          ∀ (v : ℤ), (vecVals r)[s]? = some v →
            (v = 0 ↔ negCount (sliceVals nums) s k.val.toNat < x.val.toNat) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val), ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          ∀ (v : ℤ), (vecVals r)[s]? = some v →
            (v = 0 ↔ negCount (sliceVals nums) s k.val.toNat < x.val.toNat)) := by
  sorry

/-- Whenever the function returns a result r, for every s with 0 <= s <= n-k, if r[s] < 0 then setting v = r[s], both of the following hold: the number of indices i with s <= i < s+k and nums[i] < 0 and nums[i] < v is less than x; and the number of indices i with s <= i < s+k and nums[i] < 0 and nums[i] <= v is at least x.
  Preconditions: Let n = len(nums). The slice nums is nonempty: 1 <= n <= 100000. For every i with 0 <= i < n, -50 <= nums[i] <= 50. The i64 arguments k and x, regarded as mathematical integers, satisfy 1 <= k <= n and 1 <= x <= k. -/
theorem spec_7 (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val) :
    ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          ∀ (v : ℤ), (vecVals r)[s]? = some v → v < 0 →
            negCountLt (sliceVals nums) s k.val.toNat v < x.val.toNat ∧
            x.val.toNat ≤ negCountLe (sliceVals nums) s k.val.toNat v := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val), ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          ∀ (v : ℤ), (vecVals r)[s]? = some v → v < 0 →
            negCountLt (sliceVals nums) s k.val.toNat v < x.val.toNat ∧
            x.val.toNat ≤ negCountLe (sliceVals nums) s k.val.toNat v) := by
  sorry

/-- Whenever the function returns a result r, for any two starts s and t with 0 <= s,t <= n-k, if the multiset {nums[i] | s <= i < s+k and nums[i] < 0} equals the multiset {nums[i] | t <= i < t+k and nums[i] < 0} including multiplicities, then r[s] = r[t].
  Preconditions: Let n = len(nums). The slice nums is nonempty: 1 <= n <= 100000. For every i with 0 <= i < n, -50 <= nums[i] <= 50. The i64 arguments k and x, regarded as mathematical integers, satisfy 1 <= k <= n and 1 <= x <= k. -/
theorem spec_8 (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val) :
    ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        ∀ (s t : ℕ), s + k.val.toNat ≤ nums.val.length → t + k.val.toNat ≤ nums.val.length →
          negMultisetEq (sliceVals nums) (sliceVals nums) s t k.val.toNat →
            ∀ (vs vt : ℤ), (vecVals r)[s]? = some vs → (vecVals r)[t]? = some vt →
              vs = vt := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val), ∀ r : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        ∀ (s t : ℕ), s + k.val.toNat ≤ nums.val.length → t + k.val.toNat ≤ nums.val.length →
          negMultisetEq (sliceVals nums) (sliceVals nums) s t k.val.toNat →
            ∀ (vs vt : ℤ), (vecVals r)[s]? = some vs → (vecVals r)[t]? = some vt →
              vs = vt) := by
  sorry

/-- For any x1 and x2 with 1 <= x1 < x2 <= k, whenever get_subarray_beauty(nums,k,x1) returns r1 and get_subarray_beauty(nums,k,x2) returns r2, for every s with 0 <= s <= n-k, if the window nums[s..s+k) contains at least x2 negative entries, then r1[s] <= r2[s].
  Preconditions: Let n = len(nums). The slice nums is nonempty: 1 <= n <= 100000. For every i with 0 <= i < n, -50 <= nums[i] <= 50. The values k, x1, x2, regarded as mathematical integers, satisfy 1 <= k <= n and 1 <= x1 < x2 <= k. The statement compares the result r1 of the call with x = x1 and the result r2 of the call with x = x2. -/
theorem spec_9 (nums : Slice I64) (k x1 x2 : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x1.val) (hx12 : x1.val < x2.val) (hx2 : x2.val ≤ k.val) :
    ∀ r1 r2 : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x1 = ok r1 →
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x2 = ok r2 →
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          x2.val.toNat ≤ negCount (sliceVals nums) s k.val.toNat →
            ∀ (v1 v2 : ℤ), (vecVals r1)[s]? = some v1 → (vecVals r2)[s]? = some v2 →
              v1 ≤ v2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k x1 x2 : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x1.val) (hx12 : x1.val < x2.val) (hx2 : x2.val ≤ k.val), ∀ r1 r2 : alloc.vec.Vec I64,
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x1 = ok r1 →
      Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x2 = ok r2 →
        ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
          x2.val.toNat ≤ negCount (sliceVals nums) s k.val.toNat →
            ∀ (v1 v2 : ℤ), (vecVals r1)[s]? = some v1 → (vecVals r2)[s]? = some v2 →
              v1 ≤ v2) := by
  sorry

/-- For any two such slices nums and nums', if for every s with 0 <= s <= n-k the multiset of negative values in nums[s..s+k) equals the multiset of negative values in nums'[s..s+k) including multiplicities, then whenever get_subarray_beauty(nums,k,x) returns r and get_subarray_beauty(nums',k,x) returns r', it holds that for every s with 0 <= s <= n-k, r[s] = r'[s].
  Preconditions: Let n = len(nums) = len(nums'). Both slices are nonempty: 1 <= n <= 100000. For every i with 0 <= i < n, -50 <= nums[i] <= 50 and -50 <= nums'[i] <= 50. The i64 arguments k and x, regarded as mathematical integers, satisfy 1 <= k <= n and 1 <= x <= k. -/
theorem spec_10 (nums nums' : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hne' : 1 ≤ nums'.val.length) (hmax' : nums'.val.length ≤ 100000)
    (hbound' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      -50 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 50)
    (hlen : nums.val.length = nums'.val.length)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val) :
    (∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
      negMultisetEq (sliceVals nums) (sliceVals nums') s s k.val.toNat) →
      ∀ r r' : alloc.vec.Vec I64,
        Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        Aegis.GetSubarrayBeauty.get_subarray_beauty nums' k x = ok r' →
          ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
            ∀ (v v' : ℤ), (vecVals r)[s]? = some v → (vecVals r')[s]? = some v' →
              v = v' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice I64) (k x : I64)
    (hne : 1 ≤ nums.val.length) (hmax : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -50 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hne' : 1 ≤ nums'.val.length) (hmax' : nums'.val.length ≤ 100000)
    (hbound' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      -50 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 50)
    (hlen : nums.val.length = nums'.val.length)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ k.val), (∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
      negMultisetEq (sliceVals nums) (sliceVals nums') s s k.val.toNat) →
      ∀ r r' : alloc.vec.Vec I64,
        Aegis.GetSubarrayBeauty.get_subarray_beauty nums k x = ok r →
        Aegis.GetSubarrayBeauty.get_subarray_beauty nums' k x = ok r' →
          ∀ (s : ℕ), s + k.val.toNat ≤ nums.val.length →
            ∀ (v v' : ℤ), (vecVals r)[s]? = some v → (vecVals r')[s]? = some v' →
              v = v') := by
  sorry

end AegisSpec.GetSubarrayBeauty
