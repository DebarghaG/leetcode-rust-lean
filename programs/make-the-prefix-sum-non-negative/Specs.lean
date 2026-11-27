import Aegis.MakePrefSumNonNegative.Code.Funs

/-!
# Specifications of `Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative`

LeetCode problem `make-the-prefix-sum-non-negative`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MakePrefSumNonNegative

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def PrefixesNonneg (a : List ℤ) : Prop := ∀ i, i < a.length → 0 ≤ (a.take (i + 1)).sum

  def MoveStep (cur nxt : List ℤ) : Prop :=
    ∃ p, ∃ (h : p < cur.length),
      nxt = cur.take p ++ cur.drop (p + 1) ++ [cur.get ⟨p, h⟩]

  inductive ReachesIn : ℕ → List ℤ → List ℤ → Prop where
    | refl (s : List ℤ) : ReachesIn 0 s s
    | step {k : ℕ} {s u t : List ℤ} :
        ReachesIn k s u → MoveStep u t → ReachesIn (k + 1) s t

  def MinMoves (s : List ℤ) (k : ℕ) : Prop :=
    (∃ a, ReachesIn k s a ∧ a.length = s.length ∧ PrefixesNonneg a) ∧
      ∀ j, j < k → ¬ ∃ a, ReachesIn j s a ∧ a.length = s.length ∧ PrefixesNonneg a

  def MaxGoodSubseqLen (s : List ℤ) (L : ℕ) : Prop :=
    (∃ t, t.Sublist s ∧ PrefixesNonneg t ∧ t.length = L) ∧
      ∀ t, t.Sublist s → PrefixesNonneg t → t.length ≤ L

  def RemainingPrefixSum (s : List ℤ) (M : Finset ℕ) (i : ℕ) : ℤ :=
    ((Finset.range (i + 1)).filter (fun j => j ∉ M)).sum (fun j => s.getD j 0)

  def ValidRemovalSet (s : List ℤ) (M : Finset ℕ) : Prop :=
    (∀ i ∈ M, i < s.length ∧ s.getD i 0 < 0) ∧
      ∀ i, i < s.length → 0 ≤ RemainingPrefixSum s M i

  /-- Whenever the function returns a result r, r is the least nonnegative integer k for which there exists a sequence of exactly k operations, starting from nums, that produces an array a with len(a)=len(nums) and with all prefix sums nonnegative: for every i with 0 <= i < len(nums), sum_{j=0}^{i} a[j] >= 0. An operation chooses any current index p with 0 <= p < len(current), removes the element current[p], and appends that same value to the end of the array. The case k=0 is allowed, so if nums already has all prefix sums nonnegative then r=0. The quantification is over all operation sequences and all resulting arrays; no particular final ordering of moved elements is required.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; and sum_{i=0}^{len(nums)-1} nums[i] >= 0 (the problem's promise that the array can be made prefix-sum non-negative). All indices are 0-based. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
      (hsum : 0 ≤ (vals nums).sum) :
      ∀ r : Std.I64,
        Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
          ∃ k : ℕ, MinMoves (vals nums) k ∧ r.val = (k : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
        (hsum : 0 ≤ (vals nums).sum), ∀ r : Std.I64,
          Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
            ∃ k : ℕ, MinMoves (vals nums) k ∧ r.val = (k : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail by panic, out-of-bounds access, or arithmetic overflow on any input satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; and sum_{i=0}^{len(nums)-1} nums[i] >= 0. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
      (hsum : 0 ≤ (vals nums).sum) :
      ∃ r : Std.I64,
        Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
        (hsum : 0 ≤ (vals nums).sum), ∃ r : Std.I64,
          Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= (the number of indices i with 0 <= i < len(nums) and nums[i] < 0).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; and sum_{i=0}^{len(nums)-1} nums[i] >= 0. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
      (hsum : 0 ≤ (vals nums).sum) :
      ∀ r : Std.I64,
        Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
          r.val ≤ (((vals nums).filter (fun x => x < 0)).length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
        (hsum : 0 ≤ (vals nums).sum), ∀ r : Std.I64,
          Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
            r.val ≤ (((vals nums).filter (fun x => x < 0)).length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, let L be the maximum length of a subsequence of nums (indices i_1 < i_2 < ... < i_L, not necessarily contiguous, with 0 <= L <= len(nums)) such that for every t with 1 <= t <= L, sum_{s=1}^{t} nums[i_s] >= 0. The empty subsequence is allowed and has all prefix sums nonnegative vacuously. Then r = len(nums) - L.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; and sum_{i=0}^{len(nums)-1} nums[i] >= 0. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
      (hsum : 0 ≤ (vals nums).sum) :
      ∀ r : Std.I64,
        Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
          ∃ L : ℕ, MaxGoodSubseqLen (vals nums) L ∧
            r.val = ((vals nums).length : ℤ) - (L : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
        (hsum : 0 ≤ (vals nums).sum), ∀ r : Std.I64,
          Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
            ∃ L : ℕ, MaxGoodSubseqLen (vals nums) L ∧
              r.val = ((vals nums).length : ℤ) - (L : ℤ)) := by
    sorry

  /-- Let nums' be the array of length len(nums)+1 with nums'[i]=nums[i] for 0 <= i < len(nums) and nums'[len(nums)]=x. Whenever the function returns r for nums and r' for nums', r' = r.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; sum_{i=0}^{len(nums)-1} nums[i] >= 0; len(nums) < 100000; x is an integer with -10^9 <= x <= 10^9 and sum_{i=0}^{len(nums)-1} nums[i] + x >= 0. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
      (hlen_lt : nums.val.length < 100000)
      (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
      (hsum : 0 ≤ (vals nums).sum)
      (x : Std.I64) (hx_lo : -(10 ^ 9 : ℤ) ≤ x.val) (hx_hi : x.val ≤ 10 ^ 9)
      (hsum_x : 0 ≤ (vals nums).sum + x.val) :
      ∀ nums' : Slice Std.I64, nums'.val = nums.val ++ [x] →
        ∀ r r' : Std.I64,
          Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
            Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums' = ok r' →
              r'.val = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
        (hlen_lt : nums.val.length < 100000)
        (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
        (hsum : 0 ≤ (vals nums).sum)
        (x : Std.I64) (hx_lo : -(10 ^ 9 : ℤ) ≤ x.val) (hx_hi : x.val ≤ 10 ^ 9)
        (hsum_x : 0 ≤ (vals nums).sum + x.val), ∀ nums' : Slice Std.I64, nums'.val = nums.val ++ [x] →
          ∀ r r' : Std.I64,
            Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
              Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums' = ok r' →
                r'.val = r.val) := by
    sorry

  /-- Let nums' be the array with nums'[i]=y and nums'[j]=nums[j] for every j != i. Whenever the function returns r for nums and r' for nums', r' <= r.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; sum_{i=0}^{len(nums)-1} nums[i] >= 0; i is an index with 0 <= i < len(nums); y is an integer with nums[i] <= y <= 10^9. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
      (hsum : 0 ≤ (vals nums).sum)
      (i : ℕ) (hi : i < nums.val.length) (y : Std.I64)
      (hy_lo : (nums.val.get ⟨i, hi⟩).val ≤ y.val) (hy_hi : y.val ≤ 10 ^ 9) :
      ∀ nums' : Slice Std.I64, nums'.val = nums.val.set i y →
        ∀ r r' : Std.I64,
          Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
            Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums' = ok r' →
              r'.val ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
        (hsum : 0 ≤ (vals nums).sum)
        (i : ℕ) (hi : i < nums.val.length) (y : Std.I64)
        (hy_lo : (nums.val.get ⟨i, hi⟩).val ≤ y.val) (hy_hi : y.val ≤ 10 ^ 9), ∀ nums' : Slice Std.I64, nums'.val = nums.val.set i y →
          ∀ r r' : Std.I64,
            Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
              Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums' = ok r' →
                r'.val ≤ r.val) := by
    sorry

  /-- Let nums' be the array of length len(nums)+1 with nums'[0]=x and nums'[i+1]=nums[i] for 0 <= i < len(nums). Whenever the function returns r for nums and r' for nums', r' <= r.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; sum_{i=0}^{len(nums)-1} nums[i] >= 0; len(nums) < 100000; x is an integer with 0 <= x <= 10^9. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
      (hlen_lt : nums.val.length < 100000)
      (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
      (hsum : 0 ≤ (vals nums).sum)
      (x : Std.I64) (hx_lo : 0 ≤ x.val) (hx_hi : x.val ≤ 10 ^ 9) :
      ∀ nums' : Slice Std.I64, nums'.val = x :: nums.val →
        ∀ r r' : Std.I64,
          Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
            Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums' = ok r' →
              r'.val ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
        (hlen_lt : nums.val.length < 100000)
        (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
        (hsum : 0 ≤ (vals nums).sum)
        (x : Std.I64) (hx_lo : 0 ≤ x.val) (hx_hi : x.val ≤ 10 ^ 9), ∀ nums' : Slice Std.I64, nums'.val = x :: nums.val →
          ∀ r r' : Std.I64,
            Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
              Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums' = ok r' →
                r'.val ≤ r.val) := by
    sorry

  /-- Let nums' be the array with nums'[i] = c * nums[i] for every i with 0 <= i < len(nums). Whenever the function returns r for nums and r' for nums', r' = r.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; sum_{i=0}^{len(nums)-1} nums[i] >= 0; c is a positive integer and for every i with 0 <= i < len(nums), -10^9 <= c * nums[i] <= 10^9. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
      (hsum : 0 ≤ (vals nums).sum)
      (c : ℕ) (hc : 0 < c)
      (hscaled : ∀ j : ℕ, ∀ (hj : j < nums.val.length),
        -(10 ^ 9 : ℤ) ≤ (c : ℤ) * (nums.val.get ⟨j, hj⟩).val ∧
          (c : ℤ) * (nums.val.get ⟨j, hj⟩).val ≤ 10 ^ 9) :
      ∀ nums' : Slice Std.I64,
        vals nums' = (vals nums).map (fun v => (c : ℤ) * v) →
          ∀ r r' : Std.I64,
            Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
              Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums' = ok r' →
                r'.val = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
        (hsum : 0 ≤ (vals nums).sum)
        (c : ℕ) (hc : 0 < c)
        (hscaled : ∀ j : ℕ, ∀ (hj : j < nums.val.length),
          -(10 ^ 9 : ℤ) ≤ (c : ℤ) * (nums.val.get ⟨j, hj⟩).val ∧
            (c : ℤ) * (nums.val.get ⟨j, hj⟩).val ≤ 10 ^ 9), ∀ nums' : Slice Std.I64,
          vals nums' = (vals nums).map (fun v => (c : ℤ) * v) →
            ∀ r r' : Std.I64,
              Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
                Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums' = ok r' →
                  r'.val = r.val) := by
    sorry

  /-- Whenever the function returns a result r, r is the smallest cardinality of a set M of indices with M subset of {0,1,...,len(nums)-1} such that: (a) for every i in M, nums[i] < 0; and (b) for every i with 0 <= i < len(nums), the sum of nums[j] over all j with 0 <= j <= i and j not in M is >= 0 (an empty sum is 0). Equivalently, if one deletes (or moves to the end) exactly the negative elements indexed by M, the remaining elements in their original order have all their prefix sums nonnegative, and r is the minimum number of negative elements for which this holds.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; and sum_{i=0}^{len(nums)-1} nums[i] >= 0. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
      (hsum : 0 ≤ (vals nums).sum) :
      ∀ r : Std.I64,
        Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
          ∃ M : Finset ℕ, ValidRemovalSet (vals nums) M ∧ r.val = (M.card : ℤ) ∧
            ∀ M' : Finset ℕ, ValidRemovalSet (vals nums) M' → M.card ≤ M'.card := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -(10 ^ 9 : ℤ) ≤ x ∧ x ≤ 10 ^ 9)
        (hsum : 0 ≤ (vals nums).sum), ∀ r : Std.I64,
          Aegis.MakePrefSumNonNegative.make_pref_sum_non_negative nums = ok r →
            ∃ M : Finset ℕ, ValidRemovalSet (vals nums) M ∧ r.val = (M.card : ℤ) ∧
              ∀ M' : Finset ℕ, ValidRemovalSet (vals nums) M' → M.card ≤ M'.card) := by
    sorry

  end AegisSpec.MakePrefSumNonNegative
