import Aegis.MaxFrequency.Code.Funs

/-!
# Specifications of `Aegis.MaxFrequency.max_frequency`

LeetCode problem `maximum-frequency-after-subarray-operation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxFrequency

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def valueSet (nums : Slice Std.I64) (k : Std.I64) : Finset ℤ :=
    insert k.val (vals nums).toFinset

  def valAt (nums : Slice Std.I64) (p : ℕ) : Option ℤ := (nums.val[p]?).map (fun x => x.val)

  def countList (l : List ℤ) (v : ℤ) : ℕ := (l.filter (fun y => y = v)).length

  def countVal (nums : Slice Std.I64) (v : ℤ) : ℕ := countList (vals nums) v

  def countIn (nums : Slice Std.I64) (v : ℤ) (i j : ℕ) : ℕ :=
    ((List.range nums.val.length).filter
      (fun p => i ≤ p ∧ p ≤ j ∧ valAt nums p = some v)).length

  def countOut (nums : Slice Std.I64) (v : ℤ) (i j : ℕ) : ℕ :=
    ((List.range nums.val.length).filter
      (fun p => (p < i ∨ j < p) ∧ valAt nums p = some v)).length

  def bestScore (nums : Slice Std.I64) (k : Std.I64) : ℕ :=
    (((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
        (fun q : ℕ × ℕ => q.1 ≤ q.2)).sup
      (fun q => (valueSet nums k).sup
        (fun v => countOut nums k.val q.1 q.2 + countIn nums v q.1 q.2))

  def maxOtherCount (nums : Slice Std.I64) (k : Std.I64) : ℕ :=
    ((valueSet nums k).filter (fun v => v ≠ k.val)).sup (fun v => countVal nums v)

  def maxCount (nums : Slice Std.I64) : ℕ := (vals nums).toFinset.sup (fun v => countVal nums v)

  def shifted (l : List ℤ) (i j : ℕ) (x : ℤ) : List ℤ :=
    l.zipIdx.map (fun q : ℤ × ℕ => if i ≤ q.2 ∧ q.2 ≤ j then q.1 + x else q.1)

  /-- The function returns a result r and does not fail. Let out_k(i,j) be the number of indices p with 0 <= p < n, (p < i or p > j), and nums[p] = k. For an integer v, let in_v(i,j) be the number of indices p with i <= p <= j and nums[p] = v. Then r = max { out_k(i,j) + in_v(i,j) : 0 <= i <= j < n and v is an integer }.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1 and n <= 100000. For every p with 0 <= p < n, 1 <= nums[p] <= 50. Also 1 <= k <= 50. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
      ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
        r.val = (bestScore nums k : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
          r.val = (bestScore nums k : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: Let n = len(nums). The slice satisfies n >= 1 and n <= 100000. For every p with 0 <= p < n, 1 <= nums[p] <= 50. Also 1 <= k <= 50. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
      ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r) := by
    sorry

  /-- The function returns a result r and r <= len(nums).
    Preconditions: Let n = len(nums). The slice satisfies n >= 1 and n <= 100000. For every p with 0 <= p < n, 1 <= nums[p] <= 50. Also 1 <= k <= 50. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
      ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
        r.val ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
          r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- Let totalK be the number of indices p with 0 <= p < len(nums) and nums[p] = k. The function returns a result r and r >= totalK.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1 and n <= 100000. For every p with 0 <= p < n, 1 <= nums[p] <= 50. Also 1 <= k <= 50. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
      ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
        (countVal nums k.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
          (countVal nums k.val : ℤ) ≤ r.val) := by
    sorry

  /-- Let totalK be the number of indices p with 0 <= p < len(nums) and nums[p] = k. If totalK < len(nums), then the function returns a result r and r >= totalK + 1.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1 and n <= 100000. For every p with 0 <= p < n, 1 <= nums[p] <= 50. Also 1 <= k <= 50. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50)
      (hlt : countVal nums k.val < nums.val.length) :
      ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
        (countVal nums k.val : ℤ) + 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50)
        (hlt : countVal nums k.val < nums.val.length), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
          (countVal nums k.val : ℤ) + 1 ≤ r.val) := by
    sorry

  /-- Let totalK be the number of indices p with 0 <= p < len(nums) and nums[p] = k. Let M be the maximum of 0 and all numbers #{p | 0 <= p < len(nums) and nums[p] = v} for integers v with v != k. The function returns a result r and r <= totalK + M.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1 and n <= 100000. For every p with 0 <= p < n, 1 <= nums[p] <= 50. Also 1 <= k <= 50. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
      ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
        r.val ≤ (countVal nums k.val : ℤ) + (maxOtherCount nums k : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
          r.val ≤ (countVal nums k.val : ℤ) + (maxOtherCount nums k : ℤ)) := by
    sorry

  /-- The function returns a result r and r = len(nums).
    Preconditions: Let n = len(nums). The slice satisfies n >= 1 and n <= 100000. For every p with 0 <= p < n, 1 <= nums[p] <= 50. Also 1 <= k <= 50. Let totalK be the number of indices p with 0 <= p < n and nums[p] = k, and assume totalK >= n - 1. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50)
      (hge : nums.val.length - 1 ≤ countVal nums k.val) :
      ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
        r.val = (nums.val.length : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50)
        (hge : nums.val.length - 1 ≤ countVal nums k.val), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
          r.val = (nums.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r and r = max { #{p | 0 <= p < n and nums[p] = v} : v is an integer }.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1 and n <= 100000. For every p with 0 <= p < n, 1 <= nums[p] <= 50. Also 1 <= k <= 50. Let totalK be the number of indices p with 0 <= p < n and nums[p] = k, and assume totalK = 0. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50)
      (hzero : countVal nums k.val = 0) :
      ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
        r.val = (maxCount nums : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50)
        (hzero : countVal nums k.val = 0), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
          r.val = (maxCount nums : ℤ)) := by
    sorry

  /-- The function returns a result r and there exist indices i,j with 0 <= i <= j < len(nums) and an integer x with -49 <= x <= 49 such that, after adding x to every element of nums[i..j], the number of indices p with resulting value equal to k is exactly r.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1 and n <= 100000. For every p with 0 <= p < n, 1 <= nums[p] <= 50. Also 1 <= k <= 50. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
      ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
        ∃ (i j : ℕ) (x : ℤ), i ≤ j ∧ j < nums.val.length ∧ -49 ≤ x ∧ x ≤ 49 ∧
          (countList (shifted (vals nums) i j x) k.val : ℤ) = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
          ∃ (i j : ℕ) (x : ℤ), i ≤ j ∧ j < nums.val.length ∧ -49 ≤ x ∧ x ≤ 49 ∧
            (countList (shifted (vals nums) i j x) k.val : ℤ) = r.val) := by
    sorry

  /-- The function returns a result r and, for every nonempty subarray nums[i..j] with 0 <= i <= j < len(nums) and every integer x, if new_nums is obtained by adding x to every element of nums[i..j] and leaving all other elements unchanged, then the number of indices p with new_nums[p] = k is at most r.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1 and n <= 100000. For every p with 0 <= p < n, 1 <= nums[p] <= 50. Also 1 <= k <= 50. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
      ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
        ∀ (i j : ℕ) (x : ℤ) (newNums : List ℤ),
          i ≤ j → j < nums.val.length → newNums = shifted (vals nums) i j x →
            (countList newNums k.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
          ∀ (i j : ℕ) (x : ℤ) (newNums : List ℤ),
            i ≤ j → j < nums.val.length → newNums = shifted (vals nums) i j x →
              (countList newNums k.val : ℤ) ≤ r.val) := by
    sorry

  /-- Let count(v) be the number of indices p with 0 <= p < n and nums[p] = v. The function returns a result r and r >= max { count(v) : v is an integer }.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1 and n <= 100000. For every p with 0 <= p < n, 1 <= nums[p] <= 50. Also 1 <= k <= 50. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
      ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
        (maxCount nums : ℤ) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hrange : ∀ (p : ℕ) (x : Std.I64), nums.val[p]? = some x → 1 ≤ x.val ∧ x.val ≤ 50)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k = ok r ∧
          (maxCount nums : ℤ) ≤ r.val) := by
    sorry

  end AegisSpec.MaxFrequency
