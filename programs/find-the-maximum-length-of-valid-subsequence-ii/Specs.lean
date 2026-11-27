import Aegis.MaximumLength.Code.Funs

/-!
# Specifications of `Aegis.MaximumLength.maximum_length`

LeetCode problem `find-the-maximum-length-of-valid-subsequence-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumLength

namespace AegisSpec.MaximumLength

def valueAt (xs : List I64) (i : Nat) : Int :=
  match xs[i]? with
  | some x => x.val
  | none => 0

def StrictInc (l : List Nat) : Prop := l.Pairwise (· < ·)

def ValidIdxSeq (nums : Slice I64) (k : I64) (l : List Nat) : Prop :=
  StrictInc l ∧
  (∀ i ∈ l, i < nums.val.length) ∧
  (∀ j : Nat, j + 1 < l.length →
    (valueAt nums.val (l.getD j 0) + valueAt nums.val (l.getD (j + 1) 0)) % k.val
      = (valueAt nums.val (l.getD 0 0) + valueAt nums.val (l.getD 1 0)) % k.val)

def PairSumsAgree (nums : Slice I64) (k : I64) : Prop :=
  ∀ j₁ j₂ : Nat, j₁ + 1 < nums.val.length → j₂ + 1 < nums.val.length →
    (valueAt nums.val j₁ + valueAt nums.val (j₁ + 1)) % k.val
      = (valueAt nums.val j₂ + valueAt nums.val (j₂ + 1)) % k.val

def IsSubseqOf (sub nums : List I64) : Prop :=
  ∃ js : List Nat,
    js.length = sub.length ∧
      StrictInc js ∧
      (∀ j ∈ js, j < nums.length) ∧
      (∀ t : Nat, t < sub.length → valueAt sub t = valueAt nums (js.getD t 0))

def cnt (nums : Slice I64) (k : I64) (a : Int) : Nat :=
  (List.range nums.val.length).countP (fun i => decide (valueAt nums.val i % k.val = a))

def counts (nums : Slice I64) (k : I64) : List Nat :=
  (List.range k.val.toNat).map (fun a => cnt nums k (a : Int))

def topTwo : List Nat → Nat × Nat
  | [] => (0, 0)
  | x :: t =>
    let p := topTwo t
    if x ≥ p.1 then (x, p.1) else if x ≥ p.2 then (p.1, x) else p

def maxCount (nums : Slice I64) (k : I64) : Nat := (topTwo (counts nums k)).1

def secondCount (nums : Slice I64) (k : I64) : Nat := (topTwo (counts nums k)).2

/-- Whenever the function returns a result r for input (nums, k), r is the maximum value of x over all x for which a valid index sequence of length x exists, where an increasing index sequence (i_0, i_1, ..., i_{x-1}) with 0 <= i_0 < i_1 < ... < i_{x-1} < len(nums) is called valid iff x <= 1 or, for every j with 0 <= j <= x-2, (nums[i_j] + nums[i_{j+1}]) mod k = (nums[i_0] + nums[i_1]) mod k. Equivalently, r is the length of a longest valid subsequence of nums.
  Preconditions: len(nums) >= 2, len(nums) <= 1000, and 1 <= k <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^7. Here a mod k denotes the least non-negative remainder of a modulo k, so 0 <= a mod k < k. -/
theorem spec_1 (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r) :
    (∃ l : List Nat, ValidIdxSeq nums k l ∧ (l.length : Int) = r.val) ∧
      (∀ l : List Nat, ValidIdxSeq nums k l → (l.length : Int) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r), (∃ l : List Nat, ValidIdxSeq nums k l ∧ (l.length : Int) = r.val) ∧
      (∀ l : List Nat, ValidIdxSeq nums k l → (l.length : Int) ≤ r.val)) := by
  sorry

/-- On every input satisfying the preconditions the function returns a result; it does not fail (no 64-bit overflow, no out-of-bounds indexing, no panic).
  Preconditions: len(nums) >= 2, len(nums) <= 1000, and 1 <= k <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^7. -/
theorem spec_2 (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000) :
    ∃ r : I64, maximum_length nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000), ∃ r : I64, maximum_length nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 2 <= r <= len(nums).
  Preconditions: len(nums) >= 2, len(nums) <= 1000, and 1 <= k <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^7. -/
theorem spec_3 (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r) :
    2 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r), 2 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exists a valid index sequence of length r: indices 0 <= i_0 < i_1 < ... < i_{r-1} < len(nums) such that for every j with 0 <= j <= r-2, (nums[i_j] + nums[i_{j+1}]) mod k equals (nums[i_0] + nums[i_1]) mod k.
  Preconditions: len(nums) >= 2, len(nums) <= 1000, and 1 <= k <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^7. -/
theorem spec_4 (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r) :
    ∃ l : List Nat, ValidIdxSeq nums k l ∧ (l.length : Int) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r), ∃ l : List Nat, ValidIdxSeq nums k l ∧ (l.length : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, every valid index sequence has length at most r: for every increasing index sequence 0 <= i_0 < i_1 < ... < i_{x-1} < len(nums) whose consecutive pair sums (nums[i_j] + nums[i_{j+1}]) mod k are all equal, we have x <= r.
  Preconditions: len(nums) >= 2, len(nums) <= 1000, and 1 <= k <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^7. -/
theorem spec_5 (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r) :
    ∀ l : List Nat, ValidIdxSeq nums k l → (l.length : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r), ∀ l : List Nat, ValidIdxSeq nums k l → (l.length : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if the whole index sequence (0, 1, ..., len(nums)-1) is valid — that is, all the values (nums[j] + nums[j+1]) mod k for 0 <= j <= len(nums)-2 are equal to each other — then r = len(nums).
  Preconditions: len(nums) >= 2, len(nums) <= 1000, and 1 <= k <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^7. -/
theorem spec_6 (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r)
    (h_agree : PairSumsAgree nums k) :
    r.val = (nums.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r)
    (h_agree : PairSumsAgree nums k), r.val = (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns r on (nums, k) and r2 on (nums2, k), if nums[i] mod k = nums2[i] mod k for every i with 0 <= i < len(nums), then r = r2.
  Preconditions: nums and nums2 each satisfy: len >= 2, len <= 1000, and all entries in [1, 10^7]; 1 <= k <= 1000; len(nums) = len(nums2). -/
theorem spec_7 (nums nums2 : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (h_len2_ge : 2 ≤ nums2.val.length) (h_len2_le : nums2.val.length ≤ 1000)
    (h_entries2 : ∀ i : Nat, i < nums2.val.length →
      1 ≤ valueAt nums2.val i ∧ valueAt nums2.val i ≤ 10000000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_len_eq : nums.val.length = nums2.val.length)
    (h_congr : ∀ i : Nat, i < nums.val.length →
      valueAt nums.val i % k.val = valueAt nums2.val i % k.val)
    (r r2 : I64) (h_ret : maximum_length nums k = ok r)
    (h_ret2 : maximum_length nums2 k = ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums2 : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (h_len2_ge : 2 ≤ nums2.val.length) (h_len2_le : nums2.val.length ≤ 1000)
    (h_entries2 : ∀ i : Nat, i < nums2.val.length →
      1 ≤ valueAt nums2.val i ∧ valueAt nums2.val i ≤ 10000000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_len_eq : nums.val.length = nums2.val.length)
    (h_congr : ∀ i : Nat, i < nums.val.length →
      valueAt nums.val i % k.val = valueAt nums2.val i % k.val)
    (r r2 : I64) (h_ret : maximum_length nums k = ok r)
    (h_ret2 : maximum_length nums2 k = ok r2), r.val = r2.val) := by
  sorry

/-- Whenever the function returns r on (nums, k) and r2 on (sub, k), we have r2 <= r.
  Preconditions: nums satisfies len(nums) >= 2, len(nums) <= 1000, entries in [1, 10^7]; k in [1, 1000]; sub satisfies len(sub) >= 2, entries in [1, 10^7]; and sub is a subsequence of nums: there are indices 0 <= j_0 < j_1 < ... < j_{m-1} < len(nums) with m = len(sub) and sub[t] = nums[j_t] for all 0 <= t < m. -/
theorem spec_8 (nums sub : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_sub_ge : 2 ≤ sub.val.length)
    (h_sub_entries : ∀ i : Nat, i < sub.val.length →
      1 ≤ valueAt sub.val i ∧ valueAt sub.val i ≤ 10000000)
    (h_subseq : IsSubseqOf sub.val nums.val)
    (r r2 : I64) (h_ret : maximum_length nums k = ok r)
    (h_ret2 : maximum_length sub k = ok r2) :
    r2.val ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums sub : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_sub_ge : 2 ≤ sub.val.length)
    (h_sub_entries : ∀ i : Nat, i < sub.val.length →
      1 ≤ valueAt sub.val i ∧ valueAt sub.val i ≤ 10000000)
    (h_subseq : IsSubseqOf sub.val nums.val)
    (r r2 : I64) (h_ret : maximum_length nums k = ok r)
    (h_ret2 : maximum_length sub k = ok r2), r2.val ≤ r.val) := by
  sorry

/-- Whenever the function returns r on (nums, k) and r2 on (nums2, k), we have r <= r2 <= r + 1.
  Preconditions: nums satisfies len(nums) >= 2, len(nums) <= 999, entries in [1, 10^7]; k in [1, 1000]; v in [1, 10^7]; and nums2 is nums with v appended at the end (len(nums2) = len(nums)+1, nums2[i] = nums[i] for 0 <= i < len(nums), and nums2[len(nums)] = v). -/
theorem spec_9 (nums nums2 : Slice I64) (k v : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 999)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_v_ge : 1 ≤ v.val) (h_v_le : v.val ≤ 10000000)
    (h_len2 : nums2.val.length = nums.val.length + 1)
    (h_prefix : ∀ i : Nat, i < nums.val.length → valueAt nums2.val i = valueAt nums.val i)
    (h_last : valueAt nums2.val nums.val.length = v.val)
    (r r2 : I64) (h_ret : maximum_length nums k = ok r)
    (h_ret2 : maximum_length nums2 k = ok r2) :
    r.val ≤ r2.val ∧ r2.val ≤ r.val + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums2 : Slice I64) (k v : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 999)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_v_ge : 1 ≤ v.val) (h_v_le : v.val ≤ 10000000)
    (h_len2 : nums2.val.length = nums.val.length + 1)
    (h_prefix : ∀ i : Nat, i < nums.val.length → valueAt nums2.val i = valueAt nums.val i)
    (h_last : valueAt nums2.val nums.val.length = v.val)
    (r r2 : I64) (h_ret : maximum_length nums k = ok r)
    (h_ret2 : maximum_length nums2 k = ok r2), r.val ≤ r2.val ∧ r2.val ≤ r.val + 1) := by
  sorry

/-- Whenever the function returns a result r, r >= max over a with 0 <= a < k of cnt(a), where cnt(a) is the number of indices i with 0 <= i < len(nums) and nums[i] mod k = a.
  Preconditions: len(nums) >= 2, len(nums) <= 1000, and 1 <= k <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^7. -/
theorem spec_10 (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r) :
    ∀ a : Int, 0 ≤ a → a < k.val → (cnt nums k a : Int) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r), ∀ a : Int, 0 ≤ a → a < k.val → (cnt nums k a : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= M1 + M2, where cnt(a) for 0 <= a < k is the number of indices i with 0 <= i < len(nums) and nums[i] mod k = a, and M1 >= M2 are the two largest values among the counts cnt(0), cnt(1), ..., cnt(k-1) (when k = 1, take M2 = 0).
  Preconditions: len(nums) >= 2, len(nums) <= 1000, and 1 <= k <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^7. -/
theorem spec_11 (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r) :
    r.val ≤ (maxCount nums k : Int) + (secondCount nums k : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
    (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 1000)
    (h_entries : ∀ i : Nat, i < nums.val.length →
      1 ≤ valueAt nums.val i ∧ valueAt nums.val i ≤ 10000000)
    (r : I64) (h_ret : maximum_length nums k = ok r), r.val ≤ (maxCount nums k : Int) + (secondCount nums k : Int)) := by
  sorry

end AegisSpec.MaximumLength
