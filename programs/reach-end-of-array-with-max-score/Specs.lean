import Aegis.FindMaximumScore.Code.Funs

/-!
# Specifications of `Aegis.FindMaximumScore.find_maximum_score`

LeetCode problem `reach-end-of-array-with-max-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindMaximumScore

  namespace AegisSpec.FindMaximumScore

  def contents (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def entry (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

  def jumps (s : List ℕ) : List (ℕ × ℕ) := s.zip s.tail

  def jumpScore (l : List ℤ) (s : List ℕ) : ℤ :=
    (jumps s).foldr (fun p acc => ((p.2 : ℤ) - (p.1 : ℤ)) * entry l p.1 + acc) 0

  def IsIncreasing (s : List ℕ) : Prop := ∀ p ∈ jumps s, p.1 < p.2

  def increasingB (s : List ℕ) : Bool := (jumps s).all fun p => decide (p.1 < p.2)

  def IsJumpPath (n : ℕ) (s : List ℕ) : Prop :=
    s.head? = some 0 ∧ s.getLast? = some (n - 1) ∧ IsIncreasing s

  def isJumpPathB (n : ℕ) (s : List ℕ) : Bool :=
    (s.head? == some 0) && (s.getLast? == some (n - 1)) && increasingB s

  theorem isJumpPathB_iff (n : ℕ) (s : List ℕ) : IsJumpPath n s ↔ isJumpPathB n s = true := by
    simp [IsJumpPath, isJumpPathB, IsIncreasing, increasingB, List.all_eq_true]

  def listMax : List ℤ → Option ℤ
    | [] => none
    | x :: xs => some (xs.foldr max x)

  def maxScoreOf (l : List ℤ) : ℤ :=
    (listMax (((List.range l.length).sublists.filter (isJumpPathB l.length)).map
      (jumpScore l))).getD 0

  def maxScore (nums : Slice Std.I64) : ℤ := maxScoreOf (contents nums)

  def prefixMax (l : List ℤ) (i : ℕ) : ℤ :=
    match l.take (i + 1) with
    | [] => 0
    | x :: xs => xs.foldr max x

  def prefixMaxSum (l : List ℤ) (m : ℕ) : ℤ := ((List.range m).map (prefixMax l)).sum

  def prefixMaxTotal (l : List ℤ) : ℤ :=
    if l.length = 1 then 0 else prefixMaxSum l (l.length - 1)

  def maxEntry (l : List ℤ) : ℤ :=
    match l with
    | [] => 0
    | x :: xs => xs.foldr max x

  def sumFirst (l : List ℤ) (m : ℕ) : ℤ := ((List.range m).map (entry l)).sum

  /-- The function returns a result r (it does not fail), and r equals the maximum possible total score over all valid jump sequences from index 0 to index n-1. A valid jump sequence is a finite sequence of indices i_0, i_1, ..., i_m such that i_0 = 0, i_m = n-1, m >= 0, and i_t < i_{t+1} for every 0 <= t < m; its total score is sum_{t=0}^{m-1} (i_{t+1} - i_t) * nums[i_t]. For n = 1 the only sequence is [0] and its total score is 0.
    Preconditions: Let n = len(nums). Assume n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64) (n : ℕ)
      (hlen : n = Slice.length nums)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000) :
      ∃ r : Std.I64, find_maximum_score nums = ok r ∧ r.val = maxScore nums := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : n = Slice.length nums)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000), ∃ r : Std.I64, find_maximum_score nums = ok r ∧ r.val = maxScore nums) := by
    sorry

  /-- Whenever the function returns a result r, r = S, where S is defined by: if n = 1 then S = 0, and if n >= 2 then S = sum_{i=0}^{n-2} P(i) with P(i) = max({nums[k] | 0 <= k <= i}).
    Preconditions: Let n = len(nums). Assume n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64) (n : ℕ)
      (hlen : n = Slice.length nums)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000) :
      ∀ r : Std.I64, find_maximum_score nums = ok r → r.val = prefixMaxTotal (contents nums) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : n = Slice.length nums)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000), ∀ r : Std.I64, find_maximum_score nums = ok r → r.val = prefixMaxTotal (contents nums)) := by
    sorry

  /-- The function returns a result r for every nums satisfying the preconditions; it does not fail due to panic, out-of-bounds indexing, or arithmetic overflow.
    Preconditions: Let n = len(nums). Assume n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64) (n : ℕ)
      (hlen : n = Slice.length nums)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000) :
      ∃ r : Std.I64, find_maximum_score nums = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : n = Slice.length nums)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000), ∃ r : Std.I64, find_maximum_score nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= (n - 1) * M, where M = max({nums[i] | 0 <= i < n}).
    Preconditions: Let n = len(nums). Assume n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64) (n : ℕ)
      (hlen : n = Slice.length nums)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000) :
      ∀ r : Std.I64, find_maximum_score nums = ok r →
        r.val ≤ ((n : ℤ) - 1) * maxEntry (contents nums) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : n = Slice.length nums)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000), ∀ r : Std.I64, find_maximum_score nums = ok r →
          r.val ≤ ((n : ℤ) - 1) * maxEntry (contents nums)) := by
    sorry

  /-- Whenever the function returns a result r, r >= sum_{i=0}^{n-2} nums[i], with the sum empty and equal to 0 when n = 1.
    Preconditions: Let n = len(nums). Assume n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64) (n : ℕ)
      (hlen : n = Slice.length nums)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000) :
      ∀ r : Std.I64, find_maximum_score nums = ok r →
        sumFirst (contents nums) (n - 1) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : n = Slice.length nums)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000), ∀ r : Std.I64, find_maximum_score nums = ok r →
          sumFirst (contents nums) (n - 1) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= (n - 1) * nums[0].
    Preconditions: Let n = len(nums). Assume n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64) (n : ℕ)
      (hlen : n = Slice.length nums)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000) :
      ∀ r : Std.I64, find_maximum_score nums = ok r →
        ((n : ℤ) - 1) * entry (contents nums) 0 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : n = Slice.length nums)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000), ∀ r : Std.I64, find_maximum_score nums = ok r →
          ((n : ℤ) - 1) * entry (contents nums) 0 ≤ r.val) := by
    sorry

  /-- Both calls find_maximum_score(nums) and find_maximum_score(nums') return results r and r', and r = r'.
    Preconditions: Let n = len(nums). Assume n >= 1, n <= 100000, and 1 <= nums[i] <= 100000 for all 0 <= i < n. Let v be an integer with 1 <= v <= 100000, and let nums' be the array of length n that agrees with nums at every index except nums'[n-1] = v. -/
  theorem spec_7 (nums nums' : Slice Std.I64) (n : ℕ) (v : ℤ)
      (hlen : n = Slice.length nums)
      (hlen' : Slice.length nums' = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000)
      (hv_pos : 1 ≤ v) (hv_le : v ≤ 100000)
      (hagree : ∀ i, i < n → i ≠ n - 1 → entry (contents nums') i = entry (contents nums) i)
      (hlast : entry (contents nums') (n - 1) = v) :
      ∃ r r' : Std.I64, find_maximum_score nums = ok r ∧ find_maximum_score nums' = ok r' ∧
        r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (n : ℕ) (v : ℤ)
        (hlen : n = Slice.length nums)
        (hlen' : Slice.length nums' = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000)
        (hv_pos : 1 ≤ v) (hv_le : v ≤ 100000)
        (hagree : ∀ i, i < n → i ≠ n - 1 → entry (contents nums') i = entry (contents nums) i)
        (hlast : entry (contents nums') (n - 1) = v), ∃ r r' : Std.I64, find_maximum_score nums = ok r ∧ find_maximum_score nums' = ok r' ∧
          r.val = r'.val) := by
    sorry

  /-- Both calls find_maximum_score(nums) and find_maximum_score(nums') return results r and r', and r <= r'.
    Preconditions: Let n >= 1 with n <= 100000. Let nums and nums' be arrays of length n satisfying 1 <= nums[i] <= 100000 and 1 <= nums'[i] <= 100000 for every 0 <= i < n, and assume nums[i] <= nums'[i] for every 0 <= i < n. -/
  theorem spec_8 (nums nums' : Slice Std.I64) (n : ℕ)
      (hlen : n = Slice.length nums)
      (hlen' : Slice.length nums' = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000)
      (hvals' : ∀ i, i < n → 1 ≤ entry (contents nums') i ∧ entry (contents nums') i ≤ 100000)
      (hle : ∀ i, i < n → entry (contents nums) i ≤ entry (contents nums') i) :
      ∃ r r' : Std.I64, find_maximum_score nums = ok r ∧ find_maximum_score nums' = ok r' ∧
        r.val ≤ r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (n : ℕ)
        (hlen : n = Slice.length nums)
        (hlen' : Slice.length nums' = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000)
        (hvals' : ∀ i, i < n → 1 ≤ entry (contents nums') i ∧ entry (contents nums') i ≤ 100000)
        (hle : ∀ i, i < n → entry (contents nums) i ≤ entry (contents nums') i), ∃ r r' : Std.I64, find_maximum_score nums = ok r ∧ find_maximum_score nums' = ok r' ∧
          r.val ≤ r'.val) := by
    sorry

  /-- Both calls find_maximum_score(nums) and find_maximum_score(nums') return results r and r', and r' = c * r.
    Preconditions: Let n >= 1 with n <= 100000 and nums be an array of length n with 1 <= nums[i] <= 100000 for every 0 <= i < n. Let c be an integer with c >= 1 and c * nums[i] <= 100000 for every 0 <= i < n. Let nums' be the array of length n with nums'[i] = c * nums[i]. -/
  theorem spec_9 (nums nums' : Slice Std.I64) (n : ℕ) (c : ℤ)
      (hlen : n = Slice.length nums)
      (hlen' : Slice.length nums' = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000)
      (hc_pos : 1 ≤ c)
      (hc_bound : ∀ i, i < n → c * entry (contents nums) i ≤ 100000)
      (hscale : ∀ i, i < n → entry (contents nums') i = c * entry (contents nums) i) :
      ∃ r r' : Std.I64, find_maximum_score nums = ok r ∧ find_maximum_score nums' = ok r' ∧
        r'.val = c * r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (n : ℕ) (c : ℤ)
        (hlen : n = Slice.length nums)
        (hlen' : Slice.length nums' = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000)
        (hc_pos : 1 ≤ c)
        (hc_bound : ∀ i, i < n → c * entry (contents nums) i ≤ 100000)
        (hscale : ∀ i, i < n → entry (contents nums') i = c * entry (contents nums) i), ∃ r r' : Std.I64, find_maximum_score nums = ok r ∧ find_maximum_score nums' = ok r' ∧
          r'.val = c * r.val) := by
    sorry

  /-- Both calls find_maximum_score(nums) and find_maximum_score(nums') return results r and r', and r' = r + (n - 1) * c.
    Preconditions: Let n >= 1 with n <= 100000 and nums be an array of length n with 1 <= nums[i] <= 100000 for every 0 <= i < n. Let c be an integer with c >= 0 and nums[i] + c <= 100000 for every 0 <= i < n. Let nums' be the array of length n with nums'[i] = nums[i] + c. -/
  theorem spec_10 (nums nums' : Slice Std.I64) (n : ℕ) (c : ℤ)
      (hlen : n = Slice.length nums)
      (hlen' : Slice.length nums' = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000)
      (hc_nonneg : 0 ≤ c)
      (hc_bound : ∀ i, i < n → entry (contents nums) i + c ≤ 100000)
      (hshift : ∀ i, i < n → entry (contents nums') i = entry (contents nums) i + c) :
      ∃ r r' : Std.I64, find_maximum_score nums = ok r ∧ find_maximum_score nums' = ok r' ∧
        r'.val = r.val + ((n : ℤ) - 1) * c := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (n : ℕ) (c : ℤ)
        (hlen : n = Slice.length nums)
        (hlen' : Slice.length nums' = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000)
        (hc_nonneg : 0 ≤ c)
        (hc_bound : ∀ i, i < n → entry (contents nums) i + c ≤ 100000)
        (hshift : ∀ i, i < n → entry (contents nums') i = entry (contents nums) i + c), ∃ r r' : Std.I64, find_maximum_score nums = ok r ∧ find_maximum_score nums' = ok r' ∧
          r'.val = r.val + ((n : ℤ) - 1) * c) := by
    sorry

  /-- Whenever the function returns a result r, there exists a valid jump sequence from index 0 to index n-1 whose total score is exactly r. A valid jump sequence is a finite sequence i_0, i_1, ..., i_m with i_0 = 0, i_m = n-1, m >= 0, and i_t < i_{t+1} for every 0 <= t < m; its total score is sum_{t=0}^{m-1} (i_{t+1} - i_t) * nums[i_t].
    Preconditions: Let n = len(nums). Assume n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_11 (nums : Slice Std.I64) (n : ℕ)
      (hlen : n = Slice.length nums)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000) :
      ∀ r : Std.I64, find_maximum_score nums = ok r →
        ∃ s : List ℕ, IsJumpPath n s ∧ jumpScore (contents nums) s = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : n = Slice.length nums)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000), ∀ r : Std.I64, find_maximum_score nums = ok r →
          ∃ s : List ℕ, IsJumpPath n s ∧ jumpScore (contents nums) s = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every valid jump sequence from index 0 to index n-1, its total score is at most r. A valid jump sequence is a finite sequence i_0, i_1, ..., i_m with i_0 = 0, i_m = n-1, m >= 0, and i_t < i_{t+1} for every 0 <= t < m; its total score is sum_{t=0}^{m-1} (i_{t+1} - i_t) * nums[i_t].
    Preconditions: Let n = len(nums). Assume n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_12 (nums : Slice Std.I64) (n : ℕ)
      (hlen : n = Slice.length nums)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000) :
      ∀ r : Std.I64, find_maximum_score nums = ok r →
        ∀ s : List ℕ, IsJumpPath n s → jumpScore (contents nums) s ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : n = Slice.length nums)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hvals : ∀ i, i < n → 1 ≤ entry (contents nums) i ∧ entry (contents nums) i ≤ 100000), ∀ r : Std.I64, find_maximum_score nums = ok r →
          ∀ s : List ℕ, IsJumpPath n s → jumpScore (contents nums) s ≤ r.val) := by
    sorry

  end AegisSpec.FindMaximumScore
