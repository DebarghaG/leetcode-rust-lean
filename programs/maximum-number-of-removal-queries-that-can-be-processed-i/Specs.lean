import Aegis.MaximumProcessableQueries.Code.Funs

/-!
# Specifications of `Aegis.MaximumProcessableQueries.maximum_processable_queries`

LeetCode problem `maximum-number-of-removal-queries-that-can-be-processed-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumProcessableQueries

  open Aegis.MaximumProcessableQueries

  def EntriesInRange (l : List I64) : Prop := ∀ v ∈ l, 1 ≤ v.val ∧ v.val ≤ 1000000000

  def IsSubsequence (s t : List I64) : Prop := List.Sublist s t

  def Processes (S qs : List I64) : ℕ → ℕ → ℕ → ℕ → Prop
    | 0, _, _, _ => True
    | (t + 1), k, i, r =>
        i + r < S.length ∧
          ∃ q : I64, qs[k]? = some q ∧
            ((∃ a : I64, S[i]? = some a ∧ q.val ≤ a.val ∧
                Processes S qs t (k + 1) (i + 1) r) ∨
             (∃ a : I64, S[S.length - 1 - r]? = some a ∧ q.val ≤ a.val ∧
                Processes S qs t (k + 1) i (r + 1)))

  def Processable (nums qs : List I64) (t : ℕ) : Prop :=
    ∃ S : List I64, IsSubsequence S nums ∧ Processes S qs t 0 0 0

  def IsMaxProcessable (nums qs : List I64) (m : ℕ) : Prop :=
    Processable nums qs m ∧ ∀ t : ℕ, Processable nums qs t → t ≤ m

  def headVal (l : List I64) : ℤ := ((l.head?).map (fun v => v.val)).getD 0

  def firstExceeding (l : List I64) (c : ℤ) : ℕ := (l.takeWhile (fun q => decide (q.val ≤ c))).length

  def IsReversed (revnums nums : Slice I64) : Prop := revnums.val = nums.val.reverse

  /-- Let a preprocessing choice be any subsequence S of nums, obtained by deleting zero or more entries while preserving order; S may be empty. For an integer t with 0 <= t <= len(queries), call t processable if there is a preprocessing choice S and, for each s = 0,1,...,t-1, a choice of either the first or the last element of the current sequence such that: initially the current sequence is S; at step s the current sequence is nonempty, the chosen side's element is at least queries[s], and that element is removed. The function returns r and r is the largest processable t. It does not fail.
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= 1000, len(queries) <= 1000, and for every i with 0 <= i < len(nums), nums[i] is an integer with 1 <= nums[i] <= 10^9, and for every j with 0 <= j < len(queries), queries[j] is an integer with 1 <= queries[j] <= 10^9. -/
  theorem spec_1 (nums queries : Slice I64)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val) :
      ∃ r : I64, maximum_processable_queries nums queries = ok r ∧ 0 ≤ r.val ∧
        IsMaxProcessable nums.val queries.val r.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums queries : Slice I64)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val), ∃ r : I64, maximum_processable_queries nums queries = ok r ∧ 0 ≤ r.val ∧
          IsMaxProcessable nums.val queries.val r.val.toNat) := by
    sorry

  /-- The function returns a result r; it does not fail.
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= 1000, len(queries) <= 1000, and all nums[i] and queries[j] are in [1, 10^9]. -/
  theorem spec_2 (nums queries : Slice I64)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val) :
      ∃ r : I64, maximum_processable_queries nums queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums queries : Slice I64)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val), ∃ r : I64, maximum_processable_queries nums queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have 0 <= r <= min(len(nums), len(queries)).
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= 1000, len(queries) <= 1000, and all nums[i] and queries[j] are in [1, 10^9]. -/
  theorem spec_3 (nums queries : Slice I64)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val) :
      ∀ r : I64, maximum_processable_queries nums queries = ok r →
        0 ≤ r.val ∧ r.val ≤ min (nums.val.length : ℤ) (queries.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums queries : Slice I64)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val), ∀ r : I64, maximum_processable_queries nums queries = ok r →
          0 ≤ r.val ∧ r.val ≤ min (nums.val.length : ℤ) (queries.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(nums), nums[i] < queries[0].
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= 1000, len(queries) <= 1000, and all nums[i] and queries[j] are in [1, 10^9]. -/
  theorem spec_4 (nums queries : Slice I64)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val) :
      ∀ r : I64, maximum_processable_queries nums queries = ok r →
        (r.val = 0 ↔ ∀ v ∈ nums.val, v.val < headVal queries.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums queries : Slice I64)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val), ∀ r : I64, maximum_processable_queries nums queries = ok r →
          (r.val = 0 ↔ ∀ v ∈ nums.val, v.val < headVal queries.val)) := by
    sorry

  /-- Let c = nums[0]. The function returns r = 1 if c >= queries[0], and r = 0 otherwise.
    Preconditions: len(nums) = 1, len(queries) >= 1, len(queries) <= 1000, nums[0] is in [1, 10^9], and all queries[j] are in [1, 10^9]. -/
  theorem spec_5 (nums queries : Slice I64)
      (hNlen : nums.val.length = 1)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val) :
      ∀ r : I64, maximum_processable_queries nums queries = ok r →
        r.val = if headVal queries.val ≤ headVal nums.val then 1 else 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums queries : Slice I64)
        (hNlen : nums.val.length = 1)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val), ∀ r : I64, maximum_processable_queries nums queries = ok r →
          r.val = if headVal queries.val ≤ headVal nums.val then 1 else 0) := by
    sorry

  /-- The function returns r = min(len(nums), len(queries)).
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= 1000, len(queries) <= 1000, all nums[i] and queries[j] are in [1, 10^9], and for every i with 0 <= i < len(nums) and every j with 0 <= j < len(queries), nums[i] >= queries[j]. -/
  theorem spec_6 (nums queries : Slice I64)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val)
      (hge : ∀ v ∈ nums.val, ∀ q ∈ queries.val, q.val ≤ v.val) :
      ∀ r : I64, maximum_processable_queries nums queries = ok r →
        r.val = min (nums.val.length : ℤ) (queries.val.length : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums queries : Slice I64)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val)
        (hge : ∀ v ∈ nums.val, ∀ q ∈ queries.val, q.val ≤ v.val), ∀ r : I64, maximum_processable_queries nums queries = ok r →
          r.val = min (nums.val.length : ℤ) (queries.val.length : ℤ)) := by
    sorry

  /-- Let p be the least integer with 0 <= p <= len(queries) such that either p = len(queries) or queries[p] > c. Then the function returns r = min(len(nums), p).
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= 1000, len(queries) <= 1000, all nums[i] and queries[j] are in [1, 10^9], and there is an integer c such that nums[i] = c for every i with 0 <= i < len(nums). -/
  theorem spec_7 (nums queries : Slice I64) (c : ℤ)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val)
      (hconst : ∀ v ∈ nums.val, v.val = c) :
      ∀ r : I64, maximum_processable_queries nums queries = ok r →
        r.val = min (nums.val.length : ℤ) (firstExceeding queries.val c : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums queries : Slice I64) (c : ℤ)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val)
        (hconst : ∀ v ∈ nums.val, v.val = c), ∀ r : I64, maximum_processable_queries nums queries = ok r →
          r.val = min (nums.val.length : ℤ) (firstExceeding queries.val c : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums) if and only if the first len(nums) queries can be processed starting from the full original slice nums itself with no initial replacement; that is, there exists a sequence of choices of the current first or last element for len(nums) steps such that each chosen element is at least the corresponding query and is removed. Consequently r < len(nums) otherwise.
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= len(queries), len(nums) <= 1000, len(queries) <= 1000, and all nums[i] and queries[j] are in [1, 10^9]. -/
  theorem spec_8 (nums queries : Slice I64)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNM : nums.val.length ≤ queries.val.length)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val) :
      ∀ r : I64, maximum_processable_queries nums queries = ok r →
        ((r.val = (nums.val.length : ℤ) ↔
            Processes nums.val queries.val nums.val.length 0 0 0) ∧
         (r.val < (nums.val.length : ℤ) ↔
            ¬ Processes nums.val queries.val nums.val.length 0 0 0)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums queries : Slice I64)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNM : nums.val.length ≤ queries.val.length)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val), ∀ r : I64, maximum_processable_queries nums queries = ok r →
          ((r.val = (nums.val.length : ℤ) ↔
              Processes nums.val queries.val nums.val.length 0 0 0) ∧
           (r.val < (nums.val.length : ℤ) ↔
              ¬ Processes nums.val queries.val nums.val.length 0 0 0))) := by
    sorry

  /-- Whenever the function returns a result r, for every t with 0 <= t <= r, there exists a preprocessing subsequence S of nums and a sequence of side choices that processes the first t queries.
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= 1000, len(queries) <= 1000, and all nums[i] and queries[j] are in [1, 10^9]. -/
  theorem spec_9 (nums queries : Slice I64)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val) :
      ∀ r : I64, maximum_processable_queries nums queries = ok r →
        ∀ t : ℕ, t ≤ r.val.toNat → Processable nums.val queries.val t := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums queries : Slice I64)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val), ∀ r : I64, maximum_processable_queries nums queries = ok r →
          ∀ t : ℕ, t ≤ r.val.toNat → Processable nums.val queries.val t) := by
    sorry

  /-- Whenever the function returns a result r, there exists a preprocessing subsequence S of nums and a sequence of side choices that processes exactly the first r queries.
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= 1000, len(queries) <= 1000, and all nums[i] and queries[j] are in [1, 10^9]. -/
  theorem spec_10 (nums queries : Slice I64)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val) :
      ∀ r : I64, maximum_processable_queries nums queries = ok r →
        Processable nums.val queries.val r.val.toNat := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums queries : Slice I64)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val), ∀ r : I64, maximum_processable_queries nums queries = ok r →
          Processable nums.val queries.val r.val.toNat) := by
    sorry

  /-- Let revnums be the slice of length len(nums) with revnums[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). If maximum_processable_queries(nums, queries) returns r and maximum_processable_queries(revnums, queries) returns r', then r = r'.
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= 1000, len(queries) <= 1000, and all nums[i] and queries[j] are in [1, 10^9]. -/
  theorem spec_11 (nums queries revnums : Slice I64)
      (hrev : IsReversed revnums nums)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val) :
      ∀ r r' : I64, maximum_processable_queries nums queries = ok r →
        maximum_processable_queries revnums queries = ok r' → r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums queries revnums : Slice I64)
        (hrev : IsReversed revnums nums)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val), ∀ r r' : I64, maximum_processable_queries nums queries = ok r →
          maximum_processable_queries revnums queries = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever maximum_processable_queries(nums, queries) returns r and maximum_processable_queries(nums2, queries) returns r2, we have r <= r2.
    Preconditions: nums and nums2 are slices of lengths at least 1 and at most 1000, len(queries) >= 1 and at most 1000, all entries are in [1, 10^9], and nums is a subsequence of nums2: there exist indices 0 <= j0 < j1 < ... < j(len(nums)-1) < len(nums2) with nums[i] = nums2[ji] for every i. -/
  theorem spec_12 (nums nums2 queries : Slice I64)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hN21 : 1 ≤ nums2.val.length) (hN22 : nums2.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hN2r : EntriesInRange nums2.val)
      (hMr : EntriesInRange queries.val)
      (hsub : IsSubsequence nums.val nums2.val) :
      ∀ r r2 : I64, maximum_processable_queries nums queries = ok r →
        maximum_processable_queries nums2 queries = ok r2 → r.val ≤ r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums2 queries : Slice I64)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hN21 : 1 ≤ nums2.val.length) (hN22 : nums2.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hN2r : EntriesInRange nums2.val)
        (hMr : EntriesInRange queries.val)
        (hsub : IsSubsequence nums.val nums2.val), ∀ r r2 : I64, maximum_processable_queries nums queries = ok r →
          maximum_processable_queries nums2 queries = ok r2 → r.val ≤ r2.val) := by
    sorry

  /-- Whenever maximum_processable_queries(nums, queries) returns r and maximum_processable_queries(nums, queries2) returns r2, we have r >= r2.
    Preconditions: len(nums) >= 1, len(queries) = len(queries2) >= 1, len(nums) <= 1000, len(queries) <= 1000, all entries are in [1, 10^9], and queries[j] <= queries2[j] for every j with 0 <= j < len(queries). -/
  theorem spec_13 (nums queries queries2 : Slice I64)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hlen : queries.val.length = queries2.val.length)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val)
      (hMr2 : EntriesInRange queries2.val)
      (hle : List.Forall₂ (fun q q2 => q.val ≤ q2.val) queries.val queries2.val) :
      ∀ r r2 : I64, maximum_processable_queries nums queries = ok r →
        maximum_processable_queries nums queries2 = ok r2 → r2.val ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums queries queries2 : Slice I64)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hlen : queries.val.length = queries2.val.length)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val)
        (hMr2 : EntriesInRange queries2.val)
        (hle : List.Forall₂ (fun q q2 => q.val ≤ q2.val) queries.val queries2.val), ∀ r r2 : I64, maximum_processable_queries nums queries = ok r →
          maximum_processable_queries nums queries2 = ok r2 → r2.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < r and queries[i] > v is at most the number of indices j with 0 <= j < len(nums) and nums[j] > v.
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= 1000, len(queries) <= 1000, and all nums[i] and queries[j] are in [1, 10^9]. -/
  theorem spec_14 (nums queries : Slice I64)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val) :
      ∀ r : I64, maximum_processable_queries nums queries = ok r →
        ∀ v : ℤ,
          (queries.val.take r.val.toNat).countP (fun q => decide (v < q.val)) ≤
            nums.val.countP (fun q => decide (v < q.val)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums queries : Slice I64)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val), ∀ r : I64, maximum_processable_queries nums queries = ok r →
          ∀ v : ℤ,
            (queries.val.take r.val.toNat).countP (fun q => decide (v < q.val)) ≤
              nums.val.countP (fun q => decide (v < q.val))) := by
    sorry

  /-- If maximum_processable_queries(nums, queries) returns r and maximum_processable_queries(nums, Qm) returns rm, then rm = min(r, m).
    Preconditions: len(nums) >= 1, len(queries) >= 1, len(nums) <= 1000, len(queries) <= 1000, all entries are in [1, 10^9], and 1 <= m <= len(queries). Let Qm be the slice of length m with Qm[j] = queries[j] for 0 <= j < m. -/
  theorem spec_15 (nums queries Qm : Slice I64) (m : ℕ)
      (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
      (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
      (hm1 : 1 ≤ m) (hm2 : m ≤ queries.val.length)
      (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val)
      (hQm : Qm.val = queries.val.take m) :
      ∀ r rm : I64, maximum_processable_queries nums queries = ok r →
        maximum_processable_queries nums Qm = ok rm → rm.val = min r.val (m : ℤ) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums queries Qm : Slice I64) (m : ℕ)
        (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 1000)
        (hM1 : 1 ≤ queries.val.length) (hM2 : queries.val.length ≤ 1000)
        (hm1 : 1 ≤ m) (hm2 : m ≤ queries.val.length)
        (hNr : EntriesInRange nums.val) (hMr : EntriesInRange queries.val)
        (hQm : Qm.val = queries.val.take m), ∀ r rm : I64, maximum_processable_queries nums queries = ok r →
          maximum_processable_queries nums Qm = ok rm → rm.val = min r.val (m : ℤ)) := by
    sorry

  end AegisSpec.MaximumProcessableQueries
