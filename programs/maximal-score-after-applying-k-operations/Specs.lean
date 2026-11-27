import Aegis.MaxKelements.Code.Funs

/-!
# Specifications of `Aegis.MaxKelements.max_kelements`

LeetCode problem `maximal-score-after-applying-k-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxKelements (max_kelements)

  namespace AegisSpec.MaxKelements

  def sliceVals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

  def ceilDiv3 (x : ℤ) : ℤ := (x + 2) / 3

  def listMax : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldl max x

  def countOcc (M : ℤ) : List ℤ → ℕ
    | [] => 0
    | x :: xs => (if x = M then 1 else 0) + countOcc M xs

  def validIndices (n : ℕ) (is : List ℕ) : Prop := ∀ i ∈ is, i < n

  def totalScore : List ℤ → List ℕ → ℤ
    | _, [] => 0
    | vals, i :: is =>
        vals.getD i 0 + totalScore (vals.set i (ceilDiv3 (vals.getD i 0))) is

  def IsMaxTotalScore (vals : List ℤ) (k : ℕ) (r : ℤ) : Prop :=
    (∃ is : List ℕ,
      is.length = k ∧ validIndices vals.length is ∧ totalScore vals is = r) ∧
    (∀ is : List ℕ,
      is.length = k → validIndices vals.length is → totalScore vals is ≤ r)

  def insertDesc (x : ℤ) : List ℤ → List ℤ
    | [] => [x]
    | y :: ys => if x ≥ y then x :: y :: ys else y :: insertDesc x ys

  def sortDesc : List ℤ → List ℤ
    | [] => []
    | x :: xs => insertDesc x (sortDesc xs)

  def sumLargest (k : ℕ) (l : List ℤ) : ℤ := ((sortDesc l).take k).sum

  def trajQ (x : ℤ) : ℕ → ℤ
    | 0 => x
    | t + 1 => ceilDiv3 (trajQ x t)

  def trajSum (x : ℤ) (k : ℕ) : ℤ := ((List.range k).map (fun t => trajQ x t)).sum

  def trajMultiset (vals : List ℤ) (k : ℕ) : List ℤ :=
    vals.flatMap (fun x => (List.range k).map (fun t => trajQ x t))

  /-- The function returns a result r and r is the maximum possible total score over all sequences (i_0, ..., i_{k-1}) of indices with 0 <= i_t < len(nums) for every t. For such a sequence define current values c[0][j] = nums[j]; for t = 0, ..., k-1, the t-th operation gains c[t][i_t] and sets c[t+1][i_t] = ceil(c[t][i_t]/3), while c[t+1][j] = c[t][j] for j != i_t. The total score of the sequence is sum_{t=0}^{k-1} c[t][i_t], where ceil(x/3) is the least integer >= x/3. Indices may repeat.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums); k is a 64-bit integer with 1 <= k <= 100000. -/
  theorem spec_1 (nums : Slice I64) (k : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : I64, max_kelements nums k = ok r ∧
        IsMaxTotalScore (sliceVals nums) k.val.toNat r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : I64, max_kelements nums k = ok r ∧
          IsMaxTotalScore (sliceVals nums) k.val.toNat r.val) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow on these inputs.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums); k is a 64-bit integer with 1 <= k <= 100000. -/
  theorem spec_2 (nums : Slice I64) (k : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : I64, max_kelements nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : I64, max_kelements nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= k * M, where M = max_{0 <= i < len(nums)} nums[i].
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums); k is a 64-bit integer with 1 <= k <= 100000. -/
  theorem spec_3 (nums : Slice I64) (k : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : I64, max_kelements nums k = ok r →
        r.val ≤ k.val * listMax (sliceVals nums) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : I64, max_kelements nums k = ok r →
          r.val ≤ k.val * listMax (sliceVals nums)) := by
    sorry

  /-- Whenever the function returns a result r, r >= M + k - 1, where M = max_{0 <= i < len(nums)} nums[i].
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums); k is a 64-bit integer with 1 <= k <= 100000. -/
  theorem spec_4 (nums : Slice I64) (k : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : I64, max_kelements nums k = ok r →
        listMax (sliceVals nums) + k.val - 1 ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : I64, max_kelements nums k = ok r →
          listMax (sliceVals nums) + k.val - 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = k * M.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums); k is a 64-bit integer with 1 <= k <= 100000. Let M = max_{0 <= i < len(nums)} nums[i], and assume the number of indices i with nums[i] = M is at least k. -/
  theorem spec_5 (nums : Slice I64) (k : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hcount : k.val ≤ (countOcc (listMax (sliceVals nums)) (sliceVals nums) : ℤ)) :
      ∃ r : I64, max_kelements nums k = ok r ∧
        r.val = k.val * listMax (sliceVals nums) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hcount : k.val ≤ (countOcc (listMax (sliceVals nums)) (sliceVals nums) : ℤ)), ∃ r : I64, max_kelements nums k = ok r ∧
          r.val = k.val * listMax (sliceVals nums)) := by
    sorry

  /-- The function returns a result r and r = sum_{t=0}^{k-1} q_t, where q_0 = nums[0] and q_{t+1} = ceil(q_t/3) for every t >= 0.
    Preconditions: nums is a slice of 64-bit integers with len(nums) = 1, 1 <= nums[0] <= 1000000000; k is a 64-bit integer with 1 <= k <= 100000. -/
  theorem spec_6 (nums : Slice I64) (k : I64)
      (hlen : (sliceVals nums).length = 1)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : I64, max_kelements nums k = ok r ∧
        r.val = trajSum ((sliceVals nums).getD 0 0) k.val.toNat := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen : (sliceVals nums).length = 1)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : I64, max_kelements nums k = ok r ∧
          r.val = trajSum ((sliceVals nums).getD 0 0) k.val.toNat) := by
    sorry

  /-- The function returns a result r and r = k.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and nums[i] = 1 for every 0 <= i < len(nums); k is a 64-bit integer with 1 <= k <= 100000. -/
  theorem spec_7 (nums : Slice I64) (k : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hones : ∀ i (h : i < (sliceVals nums).length), (sliceVals nums)[i] = 1)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : I64, max_kelements nums k = ok r ∧ r.val = k.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hones : ∀ i (h : i < (sliceVals nums).length), (sliceVals nums)[i] = 1)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : I64, max_kelements nums k = ok r ∧ r.val = k.val) := by
    sorry

  /-- If r = max_kelements(nums,k) and r' = max_kelements(nums',k) are returned results, then r = r'.
    Preconditions: nums and nums' are slices of 64-bit integers with 1 <= len(nums) = len(nums') <= 100000, 1 <= nums[i] <= 1000000000 and 1 <= nums'[i] <= 1000000000 for all valid i, and the multiset of entries of nums' is the same as the multiset of entries of nums; k is a 64-bit integer with 1 <= k <= 100000. -/
  theorem spec_8 (nums nums' : Slice I64) (k : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen_eq : (sliceVals nums).length = (sliceVals nums').length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
      (hbounds' : ∀ i (h : i < (sliceVals nums').length),
        1 ≤ (sliceVals nums')[i] ∧ (sliceVals nums')[i] ≤ 1000000000)
      (hperm : (sliceVals nums).Perm (sliceVals nums'))
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r r' : I64, max_kelements nums k = ok r → max_kelements nums' k = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice I64) (k : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen_eq : (sliceVals nums).length = (sliceVals nums').length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
        (hbounds' : ∀ i (h : i < (sliceVals nums').length),
          1 ≤ (sliceVals nums')[i] ∧ (sliceVals nums')[i] ≤ 1000000000)
        (hperm : (sliceVals nums).Perm (sliceVals nums'))
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r r' : I64, max_kelements nums k = ok r → max_kelements nums' k = ok r' →
          r.val = r'.val) := by
    sorry

  /-- If r1 = max_kelements(nums,k1) and r2 = max_kelements(nums,k2) are returned results, then r2 >= r1 + (k2 - k1).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums); k1 and k2 are 64-bit integers with 1 <= k1 <= k2 <= 100000. -/
  theorem spec_9 (nums : Slice I64) (k1 k2 : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
      (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 100000) :
      ∀ r1 r2 : I64, max_kelements nums k1 = ok r1 → max_kelements nums k2 = ok r2 →
        r2.val ≥ r1.val + (k2.val - k1.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64) (k1 k2 : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
        (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 100000), ∀ r1 r2 : I64, max_kelements nums k1 = ok r1 → max_kelements nums k2 = ok r2 →
          r2.val ≥ r1.val + (k2.val - k1.val)) := by
    sorry

  /-- If r = max_kelements(nums,k) and r' = max_kelements(nums',k) are returned results, then r' >= r.
    Preconditions: nums and nums' are slices of 64-bit integers with 1 <= len(nums) = len(nums') <= 100000, 1 <= nums[i] <= nums'[i] <= 1000000000 for every 0 <= i < len(nums); k is a 64-bit integer with 1 <= k <= 100000. -/
  theorem spec_10 (nums nums' : Slice I64) (k : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen_eq : (sliceVals nums).length = (sliceVals nums').length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ (sliceVals nums')[i] ∧
          (sliceVals nums')[i] ≤ 1000000000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r r' : I64, max_kelements nums k = ok r → max_kelements nums' k = ok r' →
        r'.val ≥ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice I64) (k : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen_eq : (sliceVals nums).length = (sliceVals nums').length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ (sliceVals nums')[i] ∧
            (sliceVals nums')[i] ≤ 1000000000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r r' : I64, max_kelements nums k = ok r → max_kelements nums' k = ok r' →
          r'.val ≥ r.val) := by
    sorry

  /-- The function returns a result r and there exists a sequence (i_0, ..., i_{k-1}) of indices with 0 <= i_t < len(nums) for every t such that the total score of this sequence equals r. The total score is computed by starting with current values nums, for each t = 0, ..., k-1 gaining the current value at index i_t, then replacing that current value by ceil(current/3).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums); k is a 64-bit integer with 1 <= k <= 100000. -/
  theorem spec_11 (nums : Slice I64) (k : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : I64, max_kelements nums k = ok r ∧
        ∃ is : List ℕ, is.length = k.val.toNat ∧
          validIndices (sliceVals nums).length is ∧
          totalScore (sliceVals nums) is = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : I64, max_kelements nums k = ok r ∧
          ∃ is : List ℕ, is.length = k.val.toNat ∧
            validIndices (sliceVals nums).length is ∧
            totalScore (sliceVals nums) is = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every sequence (i_0, ..., i_{k-1}) of indices with 0 <= i_t < len(nums) for every t, the total score obtained by applying these k operations is at most r. The total score is the sum of the k gained current values, where an operation gains the current value at the chosen index and then replaces it by ceil(current/3).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums); k is a 64-bit integer with 1 <= k <= 100000. -/
  theorem spec_12 (nums : Slice I64) (k : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : I64, max_kelements nums k = ok r →
        ∀ is : List ℕ, is.length = k.val.toNat →
          validIndices (sliceVals nums).length is →
          totalScore (sliceVals nums) is ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : I64, max_kelements nums k = ok r →
          ∀ is : List ℕ, is.length = k.val.toNat →
            validIndices (sliceVals nums).length is →
            totalScore (sliceVals nums) is ≤ r.val) := by
    sorry

  /-- The function returns a result r and r equals the sum of the k largest elements, with multiplicity, of the multiset Q = { q_{i,t} | 0 <= i < len(nums) and 0 <= t < k }, where q_{i,0} = nums[i] and q_{i,t+1} = ceil(q_{i,t}/3).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums); k is a 64-bit integer with 1 <= k <= 100000. -/
  theorem spec_13 (nums : Slice I64) (k : I64)
      (hlen1 : 1 ≤ (sliceVals nums).length)
      (hlen2 : (sliceVals nums).length ≤ 100000)
      (hbounds : ∀ i (h : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : I64, max_kelements nums k = ok r ∧
        r.val = sumLargest k.val.toNat (trajMultiset (sliceVals nums) k.val.toNat) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen1 : 1 ≤ (sliceVals nums).length)
        (hlen2 : (sliceVals nums).length ≤ 100000)
        (hbounds : ∀ i (h : i < (sliceVals nums).length),
          1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 1000000000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : I64, max_kelements nums k = ok r ∧
          r.val = sumLargest k.val.toNat (trajMultiset (sliceVals nums) k.val.toNat)) := by
    sorry

  end AegisSpec.MaxKelements
