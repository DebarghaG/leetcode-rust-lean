import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `maximum-array-hopping-score-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
  open Aeneas.Std.Result

  namespace AegisSpec.MaxScore

  def numLen (nums : Slice Std.I64) : Nat := nums.val.length

  def entry (nums : Slice Std.I64) (i : Nat) : Int :=
    ((nums.val[i]?).map (fun x => x.val)).getD 0

  def IsHop (n : Nat) (p : List Nat) : Prop :=
    2 ≤ p.length ∧ p.head? = some 0 ∧ p.getLast? = some (n - 1) ∧ p.Pairwise (· < ·)

  def score (nums : Slice Std.I64) (p : List Nat) : Int :=
    ((p.zip (p.drop 1)).map
      (fun q => ((q.2 : Int) - (q.1 : Int)) * entry nums q.2)).sum

  def sumFrom1 (n : Nat) (f : Nat → Int) : Int :=
    ((List.range (n - 1)).map (fun k => f (k + 1))).sum

  def tailSum (nums : Slice Std.I64) : Int :=
    sumFrom1 (numLen nums) (entry nums)

  def rangeMax (nums : Slice Std.I64) (lo hi : Nat) : Int :=
    ((nums.val.drop lo).take (hi - lo)).foldr (fun x acc => max x.val acc) 0

  /-- Whenever max_score(nums) returns a result r, r is the maximum, over all valid hopping sequences p = (p_0, p_1, ..., p_m) with m >= 1, p_0 = 0, p_m = n - 1, and p_{k-1} < p_k for every k with 1 <= k <= m, of the score Σ_{k=1}^m (p_k - p_{k-1}) * nums[p_k].
    Preconditions: Let n = len(nums). The slice nums satisfies 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∀ r, Aegis.MaxScore.max_score nums = ok r →
        (∀ p, IsHop (numLen nums) p → score nums p ≤ r.val) ∧
          ∃ p, IsHop (numLen nums) p ∧ score nums p = r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000), ∀ r, Aegis.MaxScore.max_score nums = ok r →
          (∀ p, IsHop (numLen nums) p → score nums p ≤ r.val) ∧
            ∃ p, IsHop (numLen nums) p ∧ score nums p = r.val) := by
    sorry

  /-- For every nums satisfying the preconditions, max_score(nums) returns Ok(r) for some i64 value r; it does not return an error, panic, overflow, or index out of bounds.
    Preconditions: Let n = len(nums). The slice nums satisfies 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∃ r, Aegis.MaxScore.max_score nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000), ∃ r, Aegis.MaxScore.max_score nums = ok r) := by
    sorry

  /-- Whenever max_score(nums) returns r, there exists at least one valid hopping sequence p = (p_0, ..., p_m) with m >= 1, p_0 = 0, p_m = n - 1, and p_{k-1} < p_k for every 1 <= k <= m, such that Σ_{k=1}^m (p_k - p_{k-1}) * nums[p_k] = r.
    Preconditions: Let n = len(nums). The slice nums satisfies 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∀ r, Aegis.MaxScore.max_score nums = ok r →
        ∃ p, IsHop (numLen nums) p ∧ score nums p = r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000), ∀ r, Aegis.MaxScore.max_score nums = ok r →
          ∃ p, IsHop (numLen nums) p ∧ score nums p = r.val) := by
    sorry

  /-- Whenever max_score(nums) returns r, r <= (n - 1) * max{ nums[i] | 1 <= i < n }.
    Preconditions: Let n = len(nums). The slice nums satisfies 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∀ r, Aegis.MaxScore.max_score nums = ok r →
        r.val ≤ ((numLen nums : Int) - 1) * rangeMax nums 1 (numLen nums) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000), ∀ r, Aegis.MaxScore.max_score nums = ok r →
          r.val ≤ ((numLen nums : Int) - 1) * rangeMax nums 1 (numLen nums)) := by
    sorry

  /-- Whenever max_score(nums) returns r, r >= Σ_{i=1}^{n-1} nums[i].
    Preconditions: Let n = len(nums). The slice nums satisfies 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∀ r, Aegis.MaxScore.max_score nums = ok r → tailSum nums ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000), ∀ r, Aegis.MaxScore.max_score nums = ok r → tailSum nums ≤ r.val) := by
    sorry

  /-- Whenever max_score(nums) returns r, for every i with 0 <= i < n, r >= i * nums[i] + (n - 1 - i) * nums[n - 1].
    Preconditions: Let n = len(nums). The slice nums satisfies 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∀ r, Aegis.MaxScore.max_score nums = ok r → ∀ i, i < numLen nums →
        (i : Int) * entry nums i +
            ((numLen nums - 1 - i : Nat) : Int) * entry nums (numLen nums - 1) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000), ∀ r, Aegis.MaxScore.max_score nums = ok r → ∀ i, i < numLen nums →
          (i : Int) * entry nums i +
              ((numLen nums - 1 - i : Nat) : Int) * entry nums (numLen nums - 1) ≤ r.val) := by
    sorry

  /-- Whenever max_score(nums) returns r and max_score(nums') returns r', we have r = r'.
    Preconditions: Let n = len(nums) = len(nums'). Both slices satisfy 2 <= n <= 100000 and all their entries lie in [1,100000]. They agree at every index i with 1 <= i < n; the values nums[0] and nums'[0] may differ. -/
  theorem spec_7 (nums nums' : Slice Std.I64)
      (h_len : numLen nums' = numLen nums)
      (h_len_bounds : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
      (h_bounds' : ∀ i, i < numLen nums' → 1 ≤ entry nums' i ∧ entry nums' i ≤ 100000)
      (h_agree : ∀ i, 1 ≤ i → i < numLen nums → entry nums' i = entry nums i) :
      ∀ r r', Aegis.MaxScore.max_score nums = ok r →
        Aegis.MaxScore.max_score nums' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (h_len : numLen nums' = numLen nums)
        (h_len_bounds : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
        (h_bounds' : ∀ i, i < numLen nums' → 1 ≤ entry nums' i ∧ entry nums' i ≤ 100000)
        (h_agree : ∀ i, 1 ≤ i → i < numLen nums → entry nums' i = entry nums i), ∀ r r', Aegis.MaxScore.max_score nums = ok r →
          Aegis.MaxScore.max_score nums' = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever max_score(nums) returns r and max_score(nums') returns r', we have r' >= r.
    Preconditions: Let n = len(nums) = len(nums'). Both slices satisfy 2 <= n <= 100000 and all their entries lie in [1,100000]. There is an index j with 1 <= j < n such that nums'[j] >= nums[j], and nums'[i] = nums[i] for every i with 0 <= i < n and i ≠ j. -/
  theorem spec_8 (nums nums' : Slice Std.I64)
      (h_len : numLen nums' = numLen nums)
      (h_len_bounds : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
      (h_bounds' : ∀ i, i < numLen nums' → 1 ≤ entry nums' i ∧ entry nums' i ≤ 100000)
      (h_diff : ∃ j, 1 ≤ j ∧ j < numLen nums ∧ entry nums j ≤ entry nums' j ∧
        ∀ i, i < numLen nums → i ≠ j → entry nums' i = entry nums i) :
      ∀ r r', Aegis.MaxScore.max_score nums = ok r →
        Aegis.MaxScore.max_score nums' = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (h_len : numLen nums' = numLen nums)
        (h_len_bounds : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
        (h_bounds' : ∀ i, i < numLen nums' → 1 ≤ entry nums' i ∧ entry nums' i ≤ 100000)
        (h_diff : ∃ j, 1 ≤ j ∧ j < numLen nums ∧ entry nums j ≤ entry nums' j ∧
          ∀ i, i < numLen nums → i ≠ j → entry nums' i = entry nums i), ∀ r r', Aegis.MaxScore.max_score nums = ok r →
          Aegis.MaxScore.max_score nums' = ok r' → r.val ≤ r'.val) := by
    sorry

  /-- Whenever max_score(nums) returns r and max_score(nums') returns r', we have r' = r + (n - 1) * c.
    Preconditions: Let n = len(nums) = len(nums'). Both slices satisfy 2 <= n <= 100000 and all their entries lie in [1,100000]. There is an integer c such that nums'[i] = nums[i] + c for every i with 1 <= i < n, and nums'[0] = nums[0]. -/
  theorem spec_9 (nums nums' : Slice Std.I64)
      (c : Int)
      (h_len : numLen nums' = numLen nums)
      (h_len_bounds : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
      (h_bounds' : ∀ i, i < numLen nums' → 1 ≤ entry nums' i ∧ entry nums' i ≤ 100000)
      (h_shift : ∀ i, 1 ≤ i → i < numLen nums → entry nums' i = entry nums i + c)
      (h_zero : entry nums' 0 = entry nums 0) :
      ∀ r r', Aegis.MaxScore.max_score nums = ok r →
        Aegis.MaxScore.max_score nums' = ok r' →
          r'.val = r.val + ((numLen nums : Int) - 1) * c := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (c : Int)
        (h_len : numLen nums' = numLen nums)
        (h_len_bounds : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
        (h_bounds' : ∀ i, i < numLen nums' → 1 ≤ entry nums' i ∧ entry nums' i ≤ 100000)
        (h_shift : ∀ i, 1 ≤ i → i < numLen nums → entry nums' i = entry nums i + c)
        (h_zero : entry nums' 0 = entry nums 0), ∀ r r', Aegis.MaxScore.max_score nums = ok r →
          Aegis.MaxScore.max_score nums' = ok r' →
            r'.val = r.val + ((numLen nums : Int) - 1) * c) := by
    sorry

  /-- Whenever max_score(nums) returns r and max_score(nums') returns r', we have r' = c * r.
    Preconditions: Let n = len(nums) = len(nums'). Both slices satisfy 2 <= n <= 100000 and all their entries lie in [1,100000]. There is an integer c >= 1 such that nums'[i] = c * nums[i] for every i with 1 <= i < n, and nums'[0] = nums[0]. -/
  theorem spec_10 (nums nums' : Slice Std.I64)
      (c : Int)
      (h_len : numLen nums' = numLen nums)
      (h_len_bounds : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
      (h_bounds' : ∀ i, i < numLen nums' → 1 ≤ entry nums' i ∧ entry nums' i ≤ 100000)
      (h_pos : 1 ≤ c)
      (h_scale : ∀ i, 1 ≤ i → i < numLen nums → entry nums' i = c * entry nums i)
      (h_zero : entry nums' 0 = entry nums 0) :
      ∀ r r', Aegis.MaxScore.max_score nums = ok r →
        Aegis.MaxScore.max_score nums' = ok r' → r'.val = c * r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (c : Int)
        (h_len : numLen nums' = numLen nums)
        (h_len_bounds : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
        (h_bounds' : ∀ i, i < numLen nums' → 1 ≤ entry nums' i ∧ entry nums' i ≤ 100000)
        (h_pos : 1 ≤ c)
        (h_scale : ∀ i, 1 ≤ i → i < numLen nums → entry nums' i = c * entry nums i)
        (h_zero : entry nums' 0 = entry nums 0), ∀ r r', Aegis.MaxScore.max_score nums = ok r →
          Aegis.MaxScore.max_score nums' = ok r' → r'.val = c * r.val) := by
    sorry

  /-- Whenever max_score(nums) returns r, r = Σ_{i=1}^{n-1} nums[i].
    Preconditions: Let n = len(nums). The slice satisfies 2 <= n <= 100000 and all entries lie in [1,100000]. For every i with 1 <= i < n - 1, nums[i] >= nums[i + 1]. -/
  theorem spec_11 (nums : Slice Std.I64)
      (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
      (h_nonincreasing : ∀ i, 1 ≤ i → i < numLen nums - 1 → entry nums (i + 1) ≤ entry nums i) :
      ∀ r, Aegis.MaxScore.max_score nums = ok r → r.val = tailSum nums := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
        (h_nonincreasing : ∀ i, 1 ≤ i → i < numLen nums - 1 → entry nums (i + 1) ≤ entry nums i), ∀ r, Aegis.MaxScore.max_score nums = ok r → r.val = tailSum nums) := by
    sorry

  /-- Whenever max_score(nums) returns r, r = (n - 1) * nums[n - 1].
    Preconditions: Let n = len(nums). The slice satisfies 2 <= n <= 100000 and all entries lie in [1,100000]. For every i with 1 <= i < n, nums[i] <= nums[n - 1]. -/
  theorem spec_12 (nums : Slice Std.I64)
      (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
      (h_last_max : ∀ i, 1 ≤ i → i < numLen nums → entry nums i ≤ entry nums (numLen nums - 1)) :
      ∀ r, Aegis.MaxScore.max_score nums = ok r →
        r.val = ((numLen nums : Int) - 1) * entry nums (numLen nums - 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
        (h_last_max : ∀ i, 1 ≤ i → i < numLen nums → entry nums i ≤ entry nums (numLen nums - 1)), ∀ r, Aegis.MaxScore.max_score nums = ok r →
          r.val = ((numLen nums : Int) - 1) * entry nums (numLen nums - 1)) := by
    sorry

  /-- Whenever max_score(nums) returns Ok(r), r = sum_{i=1}^{n-1} max{ nums[j] | i <= j < n }.
    Preconditions: Let n = len(nums). The slice nums satisfies 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_13 (nums : Slice Std.I64)
      (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
      (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∀ r, Aegis.MaxScore.max_score nums = ok r →
        r.val = sumFrom1 (numLen nums) (fun i => rangeMax nums i (numLen nums)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 2 ≤ numLen nums ∧ numLen nums ≤ 100000)
        (h_bounds : ∀ i, i < numLen nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000), ∀ r, Aegis.MaxScore.max_score nums = ok r →
          r.val = sumFrom1 (numLen nums) (fun i => rangeMax nums i (numLen nums))) := by
    sorry

  end AegisSpec.MaxScore
