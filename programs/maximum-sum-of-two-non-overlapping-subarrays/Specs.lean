import Aegis.MaxSumTwoNoOverlap.Code.Funs

/-!
# Specifications of `Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap`

LeetCode problem `maximum-sum-of-two-non-overlapping-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSumTwoNoOverlap

def getZ (s : Slice Std.I64) (i : ℕ) : ℤ :=
  match s.list.toList[i]? with
  | some x => x.val
  | none => 0

def winSum (s : Slice Std.I64) (start len : ℤ) : ℤ :=
  ((List.range len.toNat).map (fun t => getZ s (start.toNat + t))).sum

def maxWin (s : Slice Std.I64) (len : ℤ) : ℤ :=
  (((List.range (s.leng + 1 - len.toNat)).map (fun i => winSum s (i : ℤ) len)).max?).getD 0

def admissible (s : Slice Std.I64) (L M i j : ℤ) : Prop :=
  0 ≤ i ∧ i + L ≤ (s.leng : ℤ) ∧ 0 ≤ j ∧ j + M ≤ (s.leng : ℤ) ∧
    (i + L ≤ j ∨ j + M ≤ i)

/-- The function returns a result r, and r is the largest integer s for which there exist integers i and j with 0 <= i <= n-L, 0 <= j <= n-M, either i+L <= j or j+M <= i, and s = sum_{t=0}^{L-1} nums[i+t] + sum_{t=0}^{M-1} nums[j+t].
  Preconditions: Let n = len(nums), L = firstLen, M = secondLen. Assume 1 <= L <= 1000, 1 <= M <= 1000, L + M <= n <= 1000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000. -/
theorem spec_1 (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r ∧
        (∃ i j : ℤ, admissible nums L.val M.val i j ∧
          r.val = winSum nums i L.val + winSum nums j M.val) ∧
        (∀ s : ℤ, (∃ i j : ℤ, admissible nums L.val M.val i j ∧
          s = winSum nums i L.val + winSum nums j M.val) → s ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000), ∃ r : Std.I64,
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r ∧
        (∃ i j : ℤ, admissible nums L.val M.val i j ∧
          r.val = winSum nums i L.val + winSum nums j M.val) ∧
        (∀ s : ℤ, (∃ i j : ℤ, admissible nums L.val M.val i j ∧
          s = winSum nums i L.val + winSum nums j M.val) → s ≤ r.val)) := by
  sorry

/-- The function returns a result r; in particular, it does not panic, access an out-of-bounds index, or overflow.
  Preconditions: Let n = len(nums), L = firstLen, M = secondLen. Assume 1 <= L <= 1000, 1 <= M <= 1000, L + M <= n <= 1000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000. -/
theorem spec_2 (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000) :
    ∃ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000), ∃ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, 0 <= r.
  Preconditions: Let n = len(nums), L = firstLen, M = secondLen. Assume 1 <= L <= 1000, 1 <= M <= 1000, L + M <= n <= 1000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000. -/
theorem spec_3 (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000) :
    ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000), ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, r <= sum_{t=0}^{n-1} nums[t].
  Preconditions: Let n = len(nums), L = firstLen, M = secondLen. Assume 1 <= L <= 1000, 1 <= M <= 1000, L + M <= n <= 1000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000. -/
theorem spec_4 (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000) :
    ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      r.val ≤ winSum nums 0 (nums.leng : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000), ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      r.val ≤ winSum nums 0 (nums.leng : ℤ)) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, r <= 1000 * (L + M).
  Preconditions: Let n = len(nums), L = firstLen, M = secondLen. Assume 1 <= L <= 1000, 1 <= M <= 1000, L + M <= n <= 1000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000. -/
theorem spec_5 (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000) :
    ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      r.val ≤ 1000 * (L.val + M.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000), ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      r.val ≤ 1000 * (L.val + M.val)) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, there exist integers i and j with 0 <= i <= n-L, 0 <= j <= n-M, either i+L <= j or j+M <= i, and r = sum_{t=0}^{L-1} nums[i+t] + sum_{t=0}^{M-1} nums[j+t].
  Preconditions: Let n = len(nums), L = firstLen, M = secondLen. Assume 1 <= L <= 1000, 1 <= M <= 1000, L + M <= n <= 1000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000. -/
theorem spec_6 (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000) :
    ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      ∃ i j : ℤ, admissible nums L.val M.val i j ∧
        r.val = winSum nums i L.val + winSum nums j M.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000), ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      ∃ i j : ℤ, admissible nums L.val M.val i j ∧
        r.val = winSum nums i L.val + winSum nums j M.val) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every pair of integers i and j with 0 <= i <= n-L, 0 <= j <= n-M, and either i+L <= j or j+M <= i, we have sum_{t=0}^{L-1} nums[i+t] + sum_{t=0}^{M-1} nums[j+t] <= r.
  Preconditions: Let n = len(nums), L = firstLen, M = secondLen. Assume 1 <= L <= 1000, 1 <= M <= 1000, L + M <= n <= 1000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000. -/
theorem spec_7 (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000) :
    ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      ∀ i j : ℤ, admissible nums L.val M.val i j →
        winSum nums i L.val + winSum nums j M.val ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000), ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      ∀ i j : ℤ, admissible nums L.val M.val i j →
        winSum nums i L.val + winSum nums j M.val ≤ r.val) := by
  sorry

/-- For the same nums, L, and M, whenever the function returns a result r on input (nums, L, M) and a result s on input (nums, M, L), we have r = s.
  Preconditions: Let n = len(nums), L = firstLen, M = secondLen. Assume 1 <= L <= 1000, 1 <= M <= 1000, L + M <= n <= 1000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000. -/
theorem spec_8 (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000) :
    ∀ r s : Std.I64,
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums M L = ok s → r = s := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000), ∀ r s : Std.I64,
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums M L = ok s → r = s) := by
  sorry

/-- If for every i with 0 <= i < n we have nums[i] <= nums'[i], then whenever the function returns r on (nums, L, M) and r' on (nums', L, M), we have r <= r'.
  Preconditions: Let nums and nums' be slices of the same length n, and let L and M satisfy the preconditions with respect to both slices (so in particular both slices have entries in [0,1000] and L + M <= n). -/
theorem spec_9 (nums nums' : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hn : nums.leng ≤ 1000) (hn' : nums'.leng ≤ 1000)
    (hlen : nums'.leng = nums.leng)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ))
    (hLM' : L.val + M.val ≤ (nums'.leng : ℤ))
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000)
    (hb' : ∀ i : ℕ, i < nums'.leng → 0 ≤ getZ nums' i ∧ getZ nums' i ≤ 1000)
    (hmono : ∀ i : ℕ, i < nums.leng → getZ nums i ≤ getZ nums' i) :
    ∀ r r' : Std.I64,
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums' L M = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hn : nums.leng ≤ 1000) (hn' : nums'.leng ≤ 1000)
    (hlen : nums'.leng = nums.leng)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ))
    (hLM' : L.val + M.val ≤ (nums'.leng : ℤ))
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000)
    (hb' : ∀ i : ℕ, i < nums'.leng → 0 ≤ getZ nums' i ∧ getZ nums' i ≤ 1000)
    (hmono : ∀ i : ℕ, i < nums.leng → getZ nums i ≤ getZ nums' i), ∀ r r' : Std.I64,
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums' L M = ok r' → r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns r on (nums, L, M) and r' on (nums', L, M), we have r' = r + c * (L + M).
  Preconditions: Let n = len(nums), L = firstLen, M = secondLen. Assume 1 <= L <= 1000, 1 <= M <= 1000, L + M <= n <= 1000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000. Let c be an integer with 0 <= c <= 1000, and let nums' be a slice of length n such that for every i with 0 <= i < n, nums'[i] = nums[i] + c and 0 <= nums'[i] <= 1000. -/
theorem spec_10 (nums nums' : Slice Std.I64) (L M : Std.I64) (c : ℤ)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hn : nums.leng ≤ 1000) (hn' : nums'.leng ≤ 1000)
    (hlen : nums'.leng = nums.leng)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ))
    (hLM' : L.val + M.val ≤ (nums'.leng : ℤ))
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1000)
    (hshift : ∀ i : ℕ, i < nums'.leng → getZ nums' i = getZ nums i + c)
    (hb' : ∀ i : ℕ, i < nums'.leng → 0 ≤ getZ nums' i ∧ getZ nums' i ≤ 1000) :
    ∀ r r' : Std.I64,
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums' L M = ok r' →
      r'.val = r.val + c * (L.val + M.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (L M : Std.I64) (c : ℤ)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hn : nums.leng ≤ 1000) (hn' : nums'.leng ≤ 1000)
    (hlen : nums'.leng = nums.leng)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ))
    (hLM' : L.val + M.val ≤ (nums'.leng : ℤ))
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1000)
    (hshift : ∀ i : ℕ, i < nums'.leng → getZ nums' i = getZ nums i + c)
    (hb' : ∀ i : ℕ, i < nums'.leng → 0 ≤ getZ nums' i ∧ getZ nums' i ≤ 1000), ∀ r r' : Std.I64,
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums' L M = ok r' →
      r'.val = r.val + c * (L.val + M.val)) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, r <= (max_{0 <= i <= n-L} sum_{t=0}^{L-1} nums[i+t]) + (max_{0 <= j <= n-M} sum_{t=0}^{M-1} nums[j+t]).
  Preconditions: Let n = len(nums), L = firstLen, M = secondLen. Assume 1 <= L <= 1000, 1 <= M <= 1000, L + M <= n <= 1000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000. -/
theorem spec_11 (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000) :
    ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      r.val ≤ maxWin nums L.val + maxWin nums M.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (L M : Std.I64)
    (hL1 : 1 ≤ L.val) (hL2 : L.val ≤ 1000)
    (hM1 : 1 ≤ M.val) (hM2 : M.val ≤ 1000)
    (hLM : L.val + M.val ≤ (nums.leng : ℤ)) (hn : nums.leng ≤ 1000)
    (hb : ∀ i : ℕ, i < nums.leng → 0 ≤ getZ nums i ∧ getZ nums i ≤ 1000), ∀ r : Std.I64, Aegis.MaxSumTwoNoOverlap.max_sum_two_no_overlap nums L M = ok r →
      r.val ≤ maxWin nums L.val + maxWin nums M.val) := by
  sorry

end AegisSpec.MaxSumTwoNoOverlap
