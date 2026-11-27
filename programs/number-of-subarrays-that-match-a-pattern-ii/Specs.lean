import Aegis.CountMatchingSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountMatchingSubarrays.count_matching_subarrays`

LeetCode problem `number-of-subarrays-that-match-a-pattern-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountMatchingSubarrays

  def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  @[simp] theorem vals_length (s : Slice Std.I64) : (vals s).length = s.length := by
    simp [vals, Aeneas.Std.Slice.val, Aeneas.Std.Slice.length]

  def nth (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

  def sgn (a b : ℤ) : ℤ := if b > a then 1 else if b = a then 0 else -1

  def diffs (l : List ℤ) : List ℤ :=
    (List.range (l.length - 1)).map (fun t => sgn (nth l t) (nth l (t + 1)))

  def StepOK (p a b : ℤ) : Prop :=
    (p = 1 → b > a) ∧ (p = 0 → b = a) ∧ (p = -1 → b < a)

  def StepKO (p a b : ℤ) : Prop :=
    (p = 1 ∧ b ≤ a) ∨ (p = 0 ∧ b ≠ a) ∨ (p = -1 ∧ b ≥ a)

  def MatchAt (l p : List ℤ) (m i : ℕ) : Prop :=
    ∀ k, k < m → StepOK (nth p k) (nth l (i + k)) (nth l (i + k + 1))

  def FailAt (l p : List ℤ) (m i : ℕ) : Prop :=
    ∃ k, k < m ∧ StepKO (nth p k) (nth l (i + k)) (nth l (i + k + 1))

  noncomputable def countMatches (l p : List ℤ) (m : ℕ) : ℕ := by
    classical
    exact ((Finset.Ico (0 : ℕ) (l.length - m)).filter (fun i => MatchAt l p m i)).card

  noncomputable def countDiffMatches (l p : List ℤ) (m : ℕ) : ℕ := by
    classical
    exact ((Finset.Ico (0 : ℕ) (l.length - m)).filter
      (fun i => ∀ k, k < m → nth p k = nth (diffs l) (i + k))).card

  /-- The function returns a result r and, interpreting r as a mathematical integer, r equals the number of integers i such that 0 <= i < n - m and for every k with 0 <= k < m: pattern[k] = 1 implies nums[i+k+1] > nums[i+k]; pattern[k] = 0 implies nums[i+k+1] = nums[i+k]; and pattern[k] = -1 implies nums[i+k+1] < nums[i+k].
    Preconditions: Let n = len(nums) and m = len(pattern). The input satisfies 2 <= n <= 10^6, 1 <= m < n, every nums[j] is an integer in [1, 10^9], and every pattern[k] is in {-1, 0, 1}. -/
  theorem spec_1 (nums pattern : Slice Std.I64)
      (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
      (hm_ge : 1 ≤ (vals pattern).length)
      (hm_lt_n : (vals pattern).length < (vals nums).length)
      (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1) :
      ∃ r : Std.I64,
        Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r ∧
        r.val = (countMatches (vals nums) (vals pattern) (vals pattern).length : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums pattern : Slice Std.I64)
        (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
        (hm_ge : 1 ≤ (vals pattern).length)
        (hm_lt_n : (vals pattern).length < (vals nums).length)
        (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1), ∃ r : Std.I64,
          Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r ∧
          r.val = (countMatches (vals nums) (vals pattern) (vals pattern).length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, interpreting r as a mathematical integer, 0 <= r <= n - m.
    Preconditions: Let n = len(nums) and m = len(pattern). The input satisfies 2 <= n <= 10^6, 1 <= m < n, every nums[j] is an integer in [1, 10^9], and every pattern[k] is in {-1, 0, 1}. -/
  theorem spec_2 (nums pattern : Slice Std.I64)
      (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
      (hm_ge : 1 ≤ (vals pattern).length)
      (hm_lt_n : (vals pattern).length < (vals nums).length)
      (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1) :
      ∀ r : Std.I64,
        Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
        0 ≤ r.val ∧ r.val ≤ ((vals nums).length : ℤ) - ((vals pattern).length : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums pattern : Slice Std.I64)
        (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
        (hm_ge : 1 ≤ (vals pattern).length)
        (hm_lt_n : (vals pattern).length < (vals nums).length)
        (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1), ∀ r : Std.I64,
          Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
          0 ≤ r.val ∧ r.val ≤ ((vals nums).length : ℤ) - ((vals pattern).length : ℤ)) := by
    sorry

  /-- Define an array c of length n-1 by c[t] = 1 if nums[t+1] > nums[t], c[t] = 0 if nums[t+1] = nums[t], and c[t] = -1 if nums[t+1] < nums[t]. Whenever the function returns a result r, interpreting r as a mathematical integer, r equals the number of integers i such that 0 <= i < n - m and pattern[k] = c[i+k] for every k with 0 <= k < m.
    Preconditions: Let n = len(nums) and m = len(pattern). The input satisfies 2 <= n <= 10^6, 1 <= m < n, every nums[j] is an integer in [1, 10^9], and every pattern[k] is in {-1, 0, 1}. -/
  theorem spec_3 (nums pattern : Slice Std.I64)
      (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
      (hm_ge : 1 ≤ (vals pattern).length)
      (hm_lt_n : (vals pattern).length < (vals nums).length)
      (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1) :
      ∀ r : Std.I64,
        Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
        r.val =
          (countDiffMatches (vals nums) (vals pattern) (vals pattern).length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums pattern : Slice Std.I64)
        (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
        (hm_ge : 1 ≤ (vals pattern).length)
        (hm_lt_n : (vals pattern).length < (vals nums).length)
        (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1), ∀ r : Std.I64,
          Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
          r.val =
            (countDiffMatches (vals nums) (vals pattern) (vals pattern).length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, interpreting r as a mathematical integer, r > 0 if and only if there exists an integer i with 0 <= i < n - m such that for every k with 0 <= k < m, the required comparison holds: nums[i+k+1] > nums[i+k] when pattern[k] = 1, nums[i+k+1] = nums[i+k] when pattern[k] = 0, and nums[i+k+1] < nums[i+k] when pattern[k] = -1.
    Preconditions: Let n = len(nums) and m = len(pattern). The input satisfies 2 <= n <= 10^6, 1 <= m < n, every nums[j] is an integer in [1, 10^9], and every pattern[k] is in {-1, 0, 1}. -/
  theorem spec_4 (nums pattern : Slice Std.I64)
      (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
      (hm_ge : 1 ≤ (vals pattern).length)
      (hm_lt_n : (vals pattern).length < (vals nums).length)
      (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1) :
      ∀ r : Std.I64,
        Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
        (r.val > 0 ↔
          ∃ i, i < (vals nums).length - (vals pattern).length ∧
            MatchAt (vals nums) (vals pattern) (vals pattern).length i) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums pattern : Slice Std.I64)
        (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
        (hm_ge : 1 ≤ (vals pattern).length)
        (hm_lt_n : (vals pattern).length < (vals nums).length)
        (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1), ∀ r : Std.I64,
          Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
          (r.val > 0 ↔
            ∃ i, i < (vals nums).length - (vals pattern).length ∧
              MatchAt (vals nums) (vals pattern) (vals pattern).length i)) := by
    sorry

  /-- Whenever the function returns a result r, interpreting r as a mathematical integer, r = 0 if and only if for every integer i with 0 <= i < n - m there exists an integer k with 0 <= k < m such that the comparison between nums[i+k+1] and nums[i+k] is not the one required by pattern[k]; explicitly, at least one of the following holds: pattern[k] = 1 and nums[i+k+1] <= nums[i+k], or pattern[k] = 0 and nums[i+k+1] != nums[i+k], or pattern[k] = -1 and nums[i+k+1] >= nums[i+k].
    Preconditions: Let n = len(nums) and m = len(pattern). The input satisfies 2 <= n <= 10^6, 1 <= m < n, every nums[j] is an integer in [1, 10^9], and every pattern[k] is in {-1, 0, 1}. -/
  theorem spec_5 (nums pattern : Slice Std.I64)
      (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
      (hm_ge : 1 ≤ (vals pattern).length)
      (hm_lt_n : (vals pattern).length < (vals nums).length)
      (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1) :
      ∀ r : Std.I64,
        Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
        (r.val = 0 ↔
          ∀ i, i < (vals nums).length - (vals pattern).length →
            FailAt (vals nums) (vals pattern) (vals pattern).length i) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums pattern : Slice Std.I64)
        (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
        (hm_ge : 1 ≤ (vals pattern).length)
        (hm_lt_n : (vals pattern).length < (vals nums).length)
        (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1), ∀ r : Std.I64,
          Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
          (r.val = 0 ↔
            ∀ i, i < (vals nums).length - (vals pattern).length →
              FailAt (vals nums) (vals pattern) (vals pattern).length i)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(nums) and m = len(pattern). The input satisfies 2 <= n <= 10^6, 1 <= m < n, every nums[j] is an integer in [1, 10^9], and every pattern[k] is in {-1, 0, 1}. -/
  theorem spec_6 (nums pattern : Slice Std.I64)
      (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
      (hm_ge : 1 ≤ (vals pattern).length)
      (hm_lt_n : (vals pattern).length < (vals nums).length)
      (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1) :
      ∃ r : Std.I64,
        Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums pattern : Slice Std.I64)
        (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
        (hm_ge : 1 ≤ (vals pattern).length)
        (hm_lt_n : (vals pattern).length < (vals nums).length)
        (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1), ∃ r : Std.I64,
          Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r) := by
    sorry

  /-- Whenever the function returns r on (nums, pattern) and returns r' on (nums', pattern), interpreting both as mathematical integers, r = r'.
    Preconditions: Let n = len(nums) and m = len(pattern). The input satisfies 2 <= n <= 10^6, 1 <= m < n, every nums[j] is an integer in [1, 10^9], and every pattern[k] is in {-1, 0, 1}. Let c be an integer and let nums' be the array with nums'[j] = nums[j] + c for every j with 0 <= j < n. Assume nums' also satisfies 2 <= len(nums') <= 10^6 and every nums'[j] is in [1, 10^9]. -/
  theorem spec_7 (nums nums' pattern : Slice Std.I64) (c : ℤ)
      (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
      (hm_ge : 1 ≤ (vals pattern).length)
      (hm_lt_n : (vals pattern).length < (vals nums).length)
      (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1)
      (hshift : vals nums' = (vals nums).map (fun x => x + c))
      (hn'_ge : 2 ≤ (vals nums').length) (hn'_le : (vals nums').length ≤ 10 ^ 6)
      (hnums'_bounds : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9) :
      ∀ r r' : Std.I64,
        Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
        Aegis.CountMatchingSubarrays.count_matching_subarrays nums' pattern = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' pattern : Slice Std.I64) (c : ℤ)
        (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
        (hm_ge : 1 ≤ (vals pattern).length)
        (hm_lt_n : (vals pattern).length < (vals nums).length)
        (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1)
        (hshift : vals nums' = (vals nums).map (fun x => x + c))
        (hn'_ge : 2 ≤ (vals nums').length) (hn'_le : (vals nums').length ≤ 10 ^ 6)
        (hnums'_bounds : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9), ∀ r r' : Std.I64,
          Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
          Aegis.CountMatchingSubarrays.count_matching_subarrays nums' pattern = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Let revnums be the array of length n with revnums[j] = nums[n-1-j] for 0 <= j < n, and let revpattern be the array of length m with revpattern[k] = -pattern[m-1-k] for 0 <= k < m. Whenever the function returns r on (nums, pattern) and returns r' on (revnums, revpattern), interpreting both as mathematical integers, r = r'.
    Preconditions: Let n = len(nums) and m = len(pattern). The input satisfies 2 <= n <= 10^6, 1 <= m < n, every nums[j] is an integer in [1, 10^9], and every pattern[k] is in {-1, 0, 1}. -/
  theorem spec_8 (nums pattern revnums revpattern : Slice Std.I64)
      (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
      (hm_ge : 1 ≤ (vals pattern).length)
      (hm_lt_n : (vals pattern).length < (vals nums).length)
      (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1)
      (hrevnums : vals revnums = (vals nums).reverse)
      (hrevpattern : vals revpattern = (vals pattern).reverse.map (fun x => -x)) :
      ∀ r r' : Std.I64,
        Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
        Aegis.CountMatchingSubarrays.count_matching_subarrays revnums revpattern = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums pattern revnums revpattern : Slice Std.I64)
        (hn_ge : 2 ≤ (vals nums).length) (hn_le : (vals nums).length ≤ 10 ^ 6)
        (hm_ge : 1 ≤ (vals pattern).length)
        (hm_lt_n : (vals pattern).length < (vals nums).length)
        (hnums_bounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hpattern_bounds : ∀ x ∈ pattern.val, x.val = -1 ∨ x.val = 0 ∨ x.val = 1)
        (hrevnums : vals revnums = (vals nums).reverse)
        (hrevpattern : vals revpattern = (vals pattern).reverse.map (fun x => -x)), ∀ r r' : Std.I64,
          Aegis.CountMatchingSubarrays.count_matching_subarrays nums pattern = ok r →
          Aegis.CountMatchingSubarrays.count_matching_subarrays revnums revpattern = ok r' →
          r.val = r'.val) := by
    sorry

  end AegisSpec.CountMatchingSubarrays
