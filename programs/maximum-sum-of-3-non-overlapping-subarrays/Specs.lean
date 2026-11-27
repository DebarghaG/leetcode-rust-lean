import Aegis.MaxSumOfThreeSubarrays.Code.Funs

/-!
# Specifications of `Aegis.MaxSumOfThreeSubarrays.max_sum_of_three_subarrays`

LeetCode problem `maximum-sum-of-3-non-overlapping-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxSumOfThreeSubarrays

  namespace AegisSpec.MaxSumOfThreeSubarrays

  def resIdx (r : alloc.vec.Vec I64) (t : Nat) : Int := (r.val[t]!).val

  def windowSum (nums : Slice I64) (k : I64) (i : Int) : Int :=
    ((List.range k.val.toNat).map (fun j => (nums.val[i.toNat + j]!).val)).sum

  def arraySum (nums : Slice I64) : Int := (nums.val.map (fun x => x.val)).sum

  def ValidTriple (n k a b c : Int) : Prop :=
    0 ≤ a ∧ a + k ≤ b ∧ b + k ≤ c ∧ c + k ≤ n

  /-- Let W(i) = sum_{j=0}^{k-1} nums[i+j] for 0 <= i <= n-k. The function returns a result r; writing r = (r0,r1,r2), it holds that: (1) len(r)=3; (2) 0 <= r0, r0+k <= r1, r1+k <= r2, and r2+k <= n; (3) for every valid triple (a,b,c), meaning 0 <= a, a+k <= b, b+k <= c, c+k <= n, we have W(r0)+W(r1)+W(r2) >= W(a)+W(b)+W(c); (4) for every valid triple (a,b,c) with W(a)+W(b)+W(c) = W(r0)+W(r1)+W(r2), the returned triple is lexicographically no larger than (a,b,c), i.e. r0 < a, or r0 = a and r1 < b, or r0 = a and r1 = b and r2 <= c.
    Preconditions: Let n = len(nums). n <= 20000; 1 <= k; 3*k <= n; and for every i with 0 <= i < n, 1 <= nums[i] <= 65535. -/
  theorem spec_1 (nums : Slice I64) (k : I64)
      (hn : nums.val.length ≤ 20000)
      (hk : 1 ≤ k.val)
      (hk3 : 3 * k.val ≤ (nums.val.length : Int))
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535) :
      ∃ r : alloc.vec.Vec I64,
        max_sum_of_three_subarrays nums k = ok r ∧
        r.val.length = 3 ∧
        0 ≤ resIdx r 0 ∧
        resIdx r 0 + k.val ≤ resIdx r 1 ∧
        resIdx r 1 + k.val ≤ resIdx r 2 ∧
        resIdx r 2 + k.val ≤ (nums.val.length : Int) ∧
        (∀ a b c : Int,
          ValidTriple (nums.val.length : Int) k.val a b c →
            windowSum nums k (resIdx r 0) + windowSum nums k (resIdx r 1) + windowSum nums k (resIdx r 2) ≥
              windowSum nums k a + windowSum nums k b + windowSum nums k c) ∧
        (∀ a b c : Int,
          ValidTriple (nums.val.length : Int) k.val a b c →
            windowSum nums k a + windowSum nums k b + windowSum nums k c =
              windowSum nums k (resIdx r 0) + windowSum nums k (resIdx r 1) + windowSum nums k (resIdx r 2) →
            resIdx r 0 < a ∨ (resIdx r 0 = a ∧ resIdx r 1 < b) ∨
              (resIdx r 0 = a ∧ resIdx r 1 = b ∧ resIdx r 2 ≤ c)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn : nums.val.length ≤ 20000)
        (hk : 1 ≤ k.val)
        (hk3 : 3 * k.val ≤ (nums.val.length : Int))
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535), ∃ r : alloc.vec.Vec I64,
          max_sum_of_three_subarrays nums k = ok r ∧
          r.val.length = 3 ∧
          0 ≤ resIdx r 0 ∧
          resIdx r 0 + k.val ≤ resIdx r 1 ∧
          resIdx r 1 + k.val ≤ resIdx r 2 ∧
          resIdx r 2 + k.val ≤ (nums.val.length : Int) ∧
          (∀ a b c : Int,
            ValidTriple (nums.val.length : Int) k.val a b c →
              windowSum nums k (resIdx r 0) + windowSum nums k (resIdx r 1) + windowSum nums k (resIdx r 2) ≥
                windowSum nums k a + windowSum nums k b + windowSum nums k c) ∧
          (∀ a b c : Int,
            ValidTriple (nums.val.length : Int) k.val a b c →
              windowSum nums k a + windowSum nums k b + windowSum nums k c =
                windowSum nums k (resIdx r 0) + windowSum nums k (resIdx r 1) + windowSum nums k (resIdx r 2) →
              resIdx r 0 < a ∨ (resIdx r 0 = a ∧ resIdx r 1 < b) ∨
                (resIdx r 0 = a ∧ resIdx r 1 = b ∧ resIdx r 2 ≤ c))) := by
    sorry

  /-- The function returns a result r; it does not fail. In particular, it does not overflow, index out of bounds, or panic on any input satisfying the preconditions.
    Preconditions: Let n = len(nums). n <= 20000; 1 <= k; 3*k <= n; and for every i with 0 <= i < n, 1 <= nums[i] <= 65535. -/
  theorem spec_2 (nums : Slice I64) (k : I64)
      (hn : nums.val.length ≤ 20000)
      (hk : 1 ≤ k.val)
      (hk3 : 3 * k.val ≤ (nums.val.length : Int))
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535) :
      ∃ r : alloc.vec.Vec I64, max_sum_of_three_subarrays nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn : nums.val.length ≤ 20000)
        (hk : 1 ≤ k.val)
        (hk3 : 3 * k.val ≤ (nums.val.length : Int))
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535), ∃ r : alloc.vec.Vec I64, max_sum_of_three_subarrays nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r on an input satisfying the preconditions, len(r)=3. Thus the output has exactly one starting index for each of the three chosen subarrays.
    Preconditions: Let n = len(nums). n <= 20000; 1 <= k; 3*k <= n; and for every i with 0 <= i < n, 1 <= nums[i] <= 65535. -/
  theorem spec_3 (nums : Slice I64) (k : I64)
      (hn : nums.val.length ≤ 20000)
      (hk : 1 ≤ k.val)
      (hk3 : 3 * k.val ≤ (nums.val.length : Int))
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535) :
      ∀ r : alloc.vec.Vec I64,
        max_sum_of_three_subarrays nums k = ok r → r.val.length = 3 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn : nums.val.length ≤ 20000)
        (hk : 1 ≤ k.val)
        (hk3 : 3 * k.val ≤ (nums.val.length : Int))
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535), ∀ r : alloc.vec.Vec I64,
          max_sum_of_three_subarrays nums k = ok r → r.val.length = 3) := by
    sorry

  /-- Whenever the function returns r with len(r)=3, write r=(r0,r1,r2). For every t in {0,1,2}, 0 <= r_t and r_t + k <= n. Equivalently, each r_t is a valid starting index of a length-k subarray of nums.
    Preconditions: Let n = len(nums). n <= 20000; 1 <= k; 3*k <= n; and for every i with 0 <= i < n, 1 <= nums[i] <= 65535. -/
  theorem spec_4 (nums : Slice I64) (k : I64)
      (hn : nums.val.length ≤ 20000)
      (hk : 1 ≤ k.val)
      (hk3 : 3 * k.val ≤ (nums.val.length : Int))
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
      (r : alloc.vec.Vec I64)
      (hres : max_sum_of_three_subarrays nums k = ok r)
      (hlen : r.val.length = 3) :
      ∀ t : Nat, t < 3 →
        0 ≤ resIdx r t ∧ resIdx r t + k.val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn : nums.val.length ≤ 20000)
        (hk : 1 ≤ k.val)
        (hk3 : 3 * k.val ≤ (nums.val.length : Int))
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
        (r : alloc.vec.Vec I64)
        (hres : max_sum_of_three_subarrays nums k = ok r)
        (hlen : r.val.length = 3), ∀ t : Nat, t < 3 →
          0 ≤ resIdx r t ∧ resIdx r t + k.val ≤ (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns r with len(r)=3, write r=(r0,r1,r2). Then r0 + k <= r1 and r1 + k <= r2. Since k >= 1, the three windows [r0, r0+k-1], [r1, r1+k-1], [r2, r2+k-1] are pairwise disjoint and their starts are strictly increasing.
    Preconditions: Let n = len(nums). n <= 20000; 1 <= k; 3*k <= n; and for every i with 0 <= i < n, 1 <= nums[i] <= 65535. -/
  theorem spec_5 (nums : Slice I64) (k : I64)
      (hn : nums.val.length ≤ 20000)
      (hk : 1 ≤ k.val)
      (hk3 : 3 * k.val ≤ (nums.val.length : Int))
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
      (r : alloc.vec.Vec I64)
      (hres : max_sum_of_three_subarrays nums k = ok r)
      (hlen : r.val.length = 3) :
      resIdx r 0 + k.val ≤ resIdx r 1 ∧ resIdx r 1 + k.val ≤ resIdx r 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn : nums.val.length ≤ 20000)
        (hk : 1 ≤ k.val)
        (hk3 : 3 * k.val ≤ (nums.val.length : Int))
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
        (r : alloc.vec.Vec I64)
        (hres : max_sum_of_three_subarrays nums k = ok r)
        (hlen : r.val.length = 3), resIdx r 0 + k.val ≤ resIdx r 1 ∧ resIdx r 1 + k.val ≤ resIdx r 2) := by
    sorry

  /-- Let W(i) = sum_{j=0}^{k-1} nums[i+j]. Whenever the function returns r with len(r)=3 and r is a valid triple, meaning 0 <= r0, r0+k <= r1, r1+k <= r2, r2+k <= n, then for every valid triple (a,b,c) with 0 <= a, a+k <= b, b+k <= c, c+k <= n, we have W(r0)+W(r1)+W(r2) >= W(a)+W(b)+W(c).
    Preconditions: Let n = len(nums). n <= 20000; 1 <= k; 3*k <= n; and for every i with 0 <= i < n, 1 <= nums[i] <= 65535. -/
  theorem spec_6 (nums : Slice I64) (k : I64)
      (hn : nums.val.length ≤ 20000)
      (hk : 1 ≤ k.val)
      (hk3 : 3 * k.val ≤ (nums.val.length : Int))
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
      (r : alloc.vec.Vec I64)
      (hres : max_sum_of_three_subarrays nums k = ok r)
      (hlen : r.val.length = 3)
      (hvalid : ValidTriple (nums.val.length : Int) k.val (resIdx r 0) (resIdx r 1) (resIdx r 2)) :
      ∀ a b c : Int,
        ValidTriple (nums.val.length : Int) k.val a b c →
          windowSum nums k (resIdx r 0) + windowSum nums k (resIdx r 1) + windowSum nums k (resIdx r 2) ≥
            windowSum nums k a + windowSum nums k b + windowSum nums k c := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn : nums.val.length ≤ 20000)
        (hk : 1 ≤ k.val)
        (hk3 : 3 * k.val ≤ (nums.val.length : Int))
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
        (r : alloc.vec.Vec I64)
        (hres : max_sum_of_three_subarrays nums k = ok r)
        (hlen : r.val.length = 3)
        (hvalid : ValidTriple (nums.val.length : Int) k.val (resIdx r 0) (resIdx r 1) (resIdx r 2)), ∀ a b c : Int,
          ValidTriple (nums.val.length : Int) k.val a b c →
            windowSum nums k (resIdx r 0) + windowSum nums k (resIdx r 1) + windowSum nums k (resIdx r 2) ≥
              windowSum nums k a + windowSum nums k b + windowSum nums k c) := by
    sorry

  /-- Let W(i) = sum_{j=0}^{k-1} nums[i+j]. Whenever the function returns r with len(r)=3 and r is a valid triple, then for every valid triple (a,b,c) with W(a)+W(b)+W(c) = W(r0)+W(r1)+W(r2), the returned triple is lexicographically no larger than (a,b,c): r0 < a, or r0 = a and r1 < b, or r0 = a and r1 = b and r2 <= c.
    Preconditions: Let n = len(nums). n <= 20000; 1 <= k; 3*k <= n; and for every i with 0 <= i < n, 1 <= nums[i] <= 65535. -/
  theorem spec_7 (nums : Slice I64) (k : I64)
      (hn : nums.val.length ≤ 20000)
      (hk : 1 ≤ k.val)
      (hk3 : 3 * k.val ≤ (nums.val.length : Int))
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
      (r : alloc.vec.Vec I64)
      (hres : max_sum_of_three_subarrays nums k = ok r)
      (hlen : r.val.length = 3)
      (hvalid : ValidTriple (nums.val.length : Int) k.val (resIdx r 0) (resIdx r 1) (resIdx r 2)) :
      ∀ a b c : Int,
        ValidTriple (nums.val.length : Int) k.val a b c →
          windowSum nums k a + windowSum nums k b + windowSum nums k c =
            windowSum nums k (resIdx r 0) + windowSum nums k (resIdx r 1) + windowSum nums k (resIdx r 2) →
          resIdx r 0 < a ∨ (resIdx r 0 = a ∧ resIdx r 1 < b) ∨
            (resIdx r 0 = a ∧ resIdx r 1 = b ∧ resIdx r 2 ≤ c) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn : nums.val.length ≤ 20000)
        (hk : 1 ≤ k.val)
        (hk3 : 3 * k.val ≤ (nums.val.length : Int))
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
        (r : alloc.vec.Vec I64)
        (hres : max_sum_of_three_subarrays nums k = ok r)
        (hlen : r.val.length = 3)
        (hvalid : ValidTriple (nums.val.length : Int) k.val (resIdx r 0) (resIdx r 1) (resIdx r 2)), ∀ a b c : Int,
          ValidTriple (nums.val.length : Int) k.val a b c →
            windowSum nums k a + windowSum nums k b + windowSum nums k c =
              windowSum nums k (resIdx r 0) + windowSum nums k (resIdx r 1) + windowSum nums k (resIdx r 2) →
            resIdx r 0 < a ∨ (resIdx r 0 = a ∧ resIdx r 1 < b) ∨
              (resIdx r 0 = a ∧ resIdx r 1 = b ∧ resIdx r 2 ≤ c)) := by
    sorry

  /-- If the function returns r on nums, then max_sum_of_three_subarrays(nums2, k) returns the same vector r.
    Preconditions: Let n = len(nums). n <= 20000; 1 <= k; 3*k <= n; for every i with 0 <= i < n, 1 <= nums[i] <= 65535. Let nums2 be any slice of length n such that for every i with 0 <= i < n, 1 <= nums2[i] <= 65535, and for every i with 0 <= i <= n-k, sum_{j=0}^{k-1} nums2[i+j] = sum_{j=0}^{k-1} nums[i+j]. -/
  theorem spec_8 (nums nums2 : Slice I64) (k : I64)
      (hn : nums.val.length ≤ 20000)
      (hk : 1 ≤ k.val)
      (hk3 : 3 * k.val ≤ (nums.val.length : Int))
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
      (hlen2 : nums2.val.length = nums.val.length)
      (hbound2 : ∀ i : Nat, i < nums2.val.length → 1 ≤ (nums2.val[i]!).val ∧ (nums2.val[i]!).val ≤ 65535)
      (hW : ∀ i : Int, 0 ≤ i → i ≤ (nums.val.length : Int) - k.val → windowSum nums2 k i = windowSum nums k i) :
      ∀ r : alloc.vec.Vec I64,
        max_sum_of_three_subarrays nums k = ok r → max_sum_of_three_subarrays nums2 k = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums2 : Slice I64) (k : I64)
        (hn : nums.val.length ≤ 20000)
        (hk : 1 ≤ k.val)
        (hk3 : 3 * k.val ≤ (nums.val.length : Int))
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
        (hlen2 : nums2.val.length = nums.val.length)
        (hbound2 : ∀ i : Nat, i < nums2.val.length → 1 ≤ (nums2.val[i]!).val ∧ (nums2.val[i]!).val ≤ 65535)
        (hW : ∀ i : Int, 0 ≤ i → i ≤ (nums.val.length : Int) - k.val → windowSum nums2 k i = windowSum nums k i), ∀ r : alloc.vec.Vec I64,
          max_sum_of_three_subarrays nums k = ok r → max_sum_of_three_subarrays nums2 k = ok r) := by
    sorry

  /-- Let W(i) = sum_{j=0}^{k-1} nums[i+j]. Whenever the function returns r with len(r)=3 and r is a valid triple, W(r0)+W(r1)+W(r2) <= sum_{i=0}^{n-1} nums[i].
    Preconditions: Let n = len(nums). n <= 20000; 1 <= k; 3*k <= n; and for every i with 0 <= i < n, 1 <= nums[i] <= 65535. -/
  theorem spec_9 (nums : Slice I64) (k : I64)
      (hn : nums.val.length ≤ 20000)
      (hk : 1 ≤ k.val)
      (hk3 : 3 * k.val ≤ (nums.val.length : Int))
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
      (r : alloc.vec.Vec I64)
      (hres : max_sum_of_three_subarrays nums k = ok r)
      (hlen : r.val.length = 3)
      (hvalid : ValidTriple (nums.val.length : Int) k.val (resIdx r 0) (resIdx r 1) (resIdx r 2)) :
      windowSum nums k (resIdx r 0) + windowSum nums k (resIdx r 1) + windowSum nums k (resIdx r 2) ≤
        arraySum nums := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn : nums.val.length ≤ 20000)
        (hk : 1 ≤ k.val)
        (hk3 : 3 * k.val ≤ (nums.val.length : Int))
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535)
        (r : alloc.vec.Vec I64)
        (hres : max_sum_of_three_subarrays nums k = ok r)
        (hlen : r.val.length = 3)
        (hvalid : ValidTriple (nums.val.length : Int) k.val (resIdx r 0) (resIdx r 1) (resIdx r 2)), windowSum nums k (resIdx r 0) + windowSum nums k (resIdx r 1) + windowSum nums k (resIdx r 2) ≤
          arraySum nums) := by
    sorry

  /-- The function returns a result r and len(r)=0.
    Preconditions: Let n = len(nums). n <= 20000; 1 <= k <= n; 3*k > n; and for every i with 0 <= i < n, 1 <= nums[i] <= 65535. -/
  theorem spec_10 (nums : Slice I64) (k : I64)
      (hn : nums.val.length ≤ 20000)
      (hk : 1 ≤ k.val)
      (hkn : k.val ≤ (nums.val.length : Int))
      (hk3 : (nums.val.length : Int) < 3 * k.val)
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535) :
      ∃ r : alloc.vec.Vec I64,
        max_sum_of_three_subarrays nums k = ok r ∧ r.val.length = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn : nums.val.length ≤ 20000)
        (hk : 1 ≤ k.val)
        (hkn : k.val ≤ (nums.val.length : Int))
        (hk3 : (nums.val.length : Int) < 3 * k.val)
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535), ∃ r : alloc.vec.Vec I64,
          max_sum_of_three_subarrays nums k = ok r ∧ r.val.length = 0) := by
    sorry

  /-- The function returns a result r with len(r)=0.
    Preconditions: Let n = len(nums). 1 <= n <= 20000; 1 <= k <= 20000; n < k; and for every i with 0 <= i < n, 1 <= nums[i] <= 65535. -/
  theorem spec_11 (nums : Slice I64) (k : I64)
      (hn1 : 1 ≤ nums.val.length)
      (hn : nums.val.length ≤ 20000)
      (hk : 1 ≤ k.val)
      (hk2 : k.val ≤ 20000)
      (hnk : (nums.val.length : Int) < k.val)
      (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535) :
      ∃ r : alloc.vec.Vec I64,
        max_sum_of_three_subarrays nums k = ok r ∧ r.val.length = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn1 : 1 ≤ nums.val.length)
        (hn : nums.val.length ≤ 20000)
        (hk : 1 ≤ k.val)
        (hk2 : k.val ≤ 20000)
        (hnk : (nums.val.length : Int) < k.val)
        (hbound : ∀ i : Nat, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 65535), ∃ r : alloc.vec.Vec I64,
          max_sum_of_three_subarrays nums k = ok r ∧ r.val.length = 0) := by
    sorry

  end AegisSpec.MaxSumOfThreeSubarrays
