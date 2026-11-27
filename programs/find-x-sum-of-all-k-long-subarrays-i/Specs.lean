import Aegis.FindXSum.Code.Funs

/-!
# Specifications of `Aegis.FindXSum.find_x_sum`

LeetCode problem `find-x-sum-of-all-k-long-subarrays-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindXSum

  def inVals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun v => v.val)

  def outVals (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun v => v.val)

  def entry (r : alloc.vec.Vec Std.I64) (i : ℕ) : Option ℤ := (outVals r)[i]?

  def window (l : List ℤ) (i k : ℕ) : List ℤ := (l.drop i).take k

  def cnt (l : List ℤ) (v : ℤ) : ℕ := (l.filter (fun w => decide (w = v))).length

  def distinct (l : List ℤ) : Finset ℤ := l.toFinset

  def dcount (l : List ℤ) : ℕ := (distinct l).card

  def lexLt (a b : ℤ × ℤ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

  def keyOf (l : List ℤ) (v : ℤ) : ℤ × ℤ := ((cnt l v : ℤ), v)

  def better (l : List ℤ) (w v : ℤ) : Prop := lexLt (keyOf l v) (keyOf l w)

  instance instDecidableBetter (l : List ℤ) (w v : ℤ) : Decidable (better l w v) := by
    unfold better lexLt keyOf
    infer_instance

  def rank (l : List ℤ) (v : ℤ) : ℕ := ((distinct l).filter (fun w => better l w v)).card

  def selected (l : List ℤ) (x : ℕ) : Finset ℤ := (distinct l).filter (fun v => rank l v < x)

  def xsumOf (l : List ℤ) (x : ℕ) : ℤ := ∑ v ∈ selected l x, v * (cnt l v : ℤ)

  def topSum (l : List ℤ) (y : ℕ) : ℤ :=
    ∑ v ∈ (distinct l).filter (fun v => ((distinct l).filter (fun w => v < w)).card < y), v

  def totalSum (l : List ℤ) : ℤ := l.sum

  def minVal : List ℤ → ℤ
    | [] => 0
    | a :: l => l.foldr min a

  def sameMultiset (l₁ l₂ : List ℤ) : Prop := ∀ v : ℤ, cnt l₁ v = cnt l₂ v

  def nwin (nums : Slice Std.I64) (k : ℕ) : ℕ := nums.val.length - k + 1

  def win (nums : Slice Std.I64) (i k : ℕ) : List ℤ := window (inVals nums) i k

  /-- The function returns a result vector r of length n - k + 1. For every i with 0 <= i <= n - k, let W_i = nums[i..i+k-1] be the contiguous subarray of length k. For each integer v, let c_i(v) be the number of indices j with 0 <= j < k and W_i[j] = v. Let D_i = {v | c_i(v) > 0}. Let t_i = min(x, |D_i|). Let S_i be the set of t_i values from D_i with the t_i largest pairs (c_i(v), v) under lexicographic order; explicitly, if |D_i| <= x then S_i = D_i, and otherwise S_i consists of the x values with largest c_i(v), breaking ties in favor of the largest v. Then r[i] = sum_{v in S_i} v * c_i(v).
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. Interpret k and x as mathematical integers. -/
  theorem spec_1 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r ∧
        (outVals r).length = nwin nums k.val.toNat ∧
        ∀ i : ℕ, i < nwin nums k.val.toNat →
          entry r i = some (xsumOf (win nums i k.val.toNat) x.val.toNat) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r ∧
          (outVals r).length = nwin nums k.val.toNat ∧
          ∀ i : ℕ, i < nwin nums k.val.toNat →
            entry r i = some (xsumOf (win nums i k.val.toNat) x.val.toNat)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums) - k + 1.
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_2 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r →
          (outVals r).length = nwin nums k.val.toNat := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r →
            (outVals r).length = nwin nums k.val.toNat) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_3 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.FindXSum.find_x_sum nums k x = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∃ r : alloc.vec.Vec Std.I64, Aegis.FindXSum.find_x_sum nums k x = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i <= n - k, r[i] <= sum_{j=0}^{k-1} nums[i+j].
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_4 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r →
          ∀ i : ℕ, i < nwin nums k.val.toNat →
            ∀ z : ℤ, entry r i = some z → z ≤ totalSum (win nums i k.val.toNat) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r →
            ∀ i : ℕ, i < nwin nums k.val.toNat →
              ∀ z : ℤ, entry r i = some z → z ≤ totalSum (win nums i k.val.toNat)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i <= n - k, if the number of distinct values in the subarray nums[i..i+k-1] is strictly greater than x, then r[i] < sum_{j=0}^{k-1} nums[i+j].
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_5 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r →
          ∀ i : ℕ, i < nwin nums k.val.toNat →
            x.val.toNat < dcount (win nums i k.val.toNat) →
              ∀ z : ℤ, entry r i = some z →
                z < totalSum (win nums i k.val.toNat) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r →
            ∀ i : ℕ, i < nwin nums k.val.toNat →
              x.val.toNat < dcount (win nums i k.val.toNat) →
                ∀ z : ℤ, entry r i = some z →
                  z < totalSum (win nums i k.val.toNat)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i <= n - k, r[i] >= x * min_{0 <= j < k} nums[i+j].
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_6 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r →
          ∀ i : ℕ, i < nwin nums k.val.toNat →
            ∀ z : ℤ, entry r i = some z →
              (x.val.toNat : ℤ) * minVal (win nums i k.val.toNat) ≤ z := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r →
            ∀ i : ℕ, i < nwin nums k.val.toNat →
              ∀ z : ℤ, entry r i = some z →
                (x.val.toNat : ℤ) * minVal (win nums i k.val.toNat) ≤ z) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i <= n - k, if the subarray nums[i..i+k-1] has at most x distinct values, then r[i] = sum_{j=0}^{k-1} nums[i+j].
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_7 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r →
          ∀ i : ℕ, i < nwin nums k.val.toNat →
            dcount (win nums i k.val.toNat) ≤ x.val.toNat →
              entry r i = some (totalSum (win nums i k.val.toNat)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r →
            ∀ i : ℕ, i < nwin nums k.val.toNat →
              dcount (win nums i k.val.toNat) ≤ x.val.toNat →
                entry r i = some (totalSum (win nums i k.val.toNat))) := by
    sorry

  /-- Whenever the function returns a result r, if x = 1, then for every i with 0 <= i <= n - k, let W_i = nums[i..i+k-1] and for each integer v let c_i(v) be its number of occurrences in W_i. Let v_i be the value with c_i(v_i) > 0 that is lexicographically maximal by the pair (c_i(v_i), v_i). Then r[i] = v_i * c_i(v_i).
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_8 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r →
          x.val = 1 →
            ∀ i : ℕ, i < nwin nums k.val.toNat →
              ∀ v : ℤ, 0 < cnt (win nums i k.val.toNat) v →
                (∀ w : ℤ, 0 < cnt (win nums i k.val.toNat) w →
                  ¬ better (win nums i k.val.toNat) w v) →
                  entry r i = some (v * (cnt (win nums i k.val.toNat) v : ℤ)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r →
            x.val = 1 →
              ∀ i : ℕ, i < nwin nums k.val.toNat →
                ∀ v : ℤ, 0 < cnt (win nums i k.val.toNat) v →
                  (∀ w : ℤ, 0 < cnt (win nums i k.val.toNat) w →
                    ¬ better (win nums i k.val.toNat) w v) →
                    entry r i = some (v * (cnt (win nums i k.val.toNat) v : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i <= n - k, if the k elements of nums[i..i+k-1] are pairwise distinct, then r[i] equals the sum of the x largest values among nums[i..i+k-1].
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_9 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r →
          ∀ i : ℕ, i < nwin nums k.val.toNat →
            (win nums i k.val.toNat).Nodup →
              entry r i = some (topSum (win nums i k.val.toNat) x.val.toNat) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r →
            ∀ i : ℕ, i < nwin nums k.val.toNat →
              (win nums i k.val.toNat).Nodup →
                entry r i = some (topSum (win nums i k.val.toNat) x.val.toNat)) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i <= n - k and 0 <= j <= n - k, if the multisets of values in the subarrays nums[i..i+k-1] and nums[j..j+k-1] are equal (equivalently, every integer occurs the same number of times in both windows), then r[i] = r[j].
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_10 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r →
          ∀ i j : ℕ, i < nwin nums k.val.toNat → j < nwin nums k.val.toNat →
            sameMultiset (win nums i k.val.toNat) (win nums j k.val.toNat) →
              ∀ z₁ z₂ : ℤ, entry r i = some z₁ → entry r j = some z₂ → z₁ = z₂ := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r →
            ∀ i j : ℕ, i < nwin nums k.val.toNat → j < nwin nums k.val.toNat →
              sameMultiset (win nums i k.val.toNat) (win nums j k.val.toNat) →
                ∀ z₁ z₂ : ℤ, entry r i = some z₁ → entry r j = some z₂ → z₁ = z₂) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i <= n - k, there exists a set S_i of distinct values occurring in nums[i..i+k-1] such that |S_i| = min(x, d_i), where d_i is the number of distinct values in that window, and r[i] = sum_{v in S_i} v * c_i(v), where c_i(v) is the number of occurrences of v in the window.
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_11 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r →
          ∀ i : ℕ, i < nwin nums k.val.toNat →
            ∃ S : Finset ℤ,
              S ⊆ distinct (win nums i k.val.toNat) ∧
              S.card = min x.val.toNat (dcount (win nums i k.val.toNat)) ∧
              entry r i = some (∑ v ∈ S, v * (cnt (win nums i k.val.toNat) v : ℤ)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r →
            ∀ i : ℕ, i < nwin nums k.val.toNat →
              ∃ S : Finset ℤ,
                S ⊆ distinct (win nums i k.val.toNat) ∧
                S.card = min x.val.toNat (dcount (win nums i k.val.toNat)) ∧
                entry r i = some (∑ v ∈ S, v * (cnt (win nums i k.val.toNat) v : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i <= n - k, let W_i = nums[i..i+k-1] and for each integer v let c_i(v) be its number of occurrences in W_i. Let v_i be a value with c_i(v_i) > 0 that is lexicographically maximal by the pair (c_i(v_i), v_i). Then r[i] >= v_i * c_i(v_i).
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_12 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r →
          ∀ i : ℕ, i < nwin nums k.val.toNat →
            ∀ v : ℤ, 0 < cnt (win nums i k.val.toNat) v →
              (∀ w : ℤ, 0 < cnt (win nums i k.val.toNat) w →
                ¬ better (win nums i k.val.toNat) w v) →
                ∀ z : ℤ, entry r i = some z →
                  v * (cnt (win nums i k.val.toNat) v : ℤ) ≤ z := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r →
            ∀ i : ℕ, i < nwin nums k.val.toNat →
              ∀ v : ℤ, 0 < cnt (win nums i k.val.toNat) v →
                (∀ w : ℤ, 0 < cnt (win nums i k.val.toNat) w →
                  ¬ better (win nums i k.val.toNat) w v) →
                  ∀ z : ℤ, entry r i = some z →
                    v * (cnt (win nums i k.val.toNat) v : ℤ) ≤ z) := by
    sorry

  /-- Let r1 be the result returned by find_x_sum(nums, k, x1) and r2 the result returned by find_x_sum(nums, k, x2). Whenever both calls return, len(r1) = len(r2) = n - k + 1 and for every i with 0 <= i <= n - k, r1[i] <= r2[i].
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x1 <= x2 <= k <= n. Interpret k, x1, x2 as mathematical integers. -/
  theorem spec_13 (nums : Slice Std.I64) (k x₁ x₂ : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx₁ : 1 ≤ x₁.val) (hx₁₂ : x₁.val ≤ x₂.val) (hx₂k : x₂.val ≤ k.val)
      (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r₁ r₂ : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x₁ = ok r₁ →
        Aegis.FindXSum.find_x_sum nums k x₂ = ok r₂ →
          (outVals r₁).length = nwin nums k.val.toNat ∧
          (outVals r₂).length = nwin nums k.val.toNat ∧
          ∀ i : ℕ, i < nwin nums k.val.toNat →
            ∀ z₁ z₂ : ℤ, entry r₁ i = some z₁ → entry r₂ i = some z₂ → z₁ ≤ z₂ := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x₁ x₂ : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx₁ : 1 ≤ x₁.val) (hx₁₂ : x₁.val ≤ x₂.val) (hx₂k : x₂.val ≤ k.val)
        (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r₁ r₂ : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x₁ = ok r₁ →
          Aegis.FindXSum.find_x_sum nums k x₂ = ok r₂ →
            (outVals r₁).length = nwin nums k.val.toNat ∧
            (outVals r₂).length = nwin nums k.val.toNat ∧
            ∀ i : ℕ, i < nwin nums k.val.toNat →
              ∀ z₁ z₂ : ℤ, entry r₁ i = some z₁ → entry r₂ i = some z₂ → z₁ ≤ z₂) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i <= n - k, let W_i = nums[i..i+k-1]. If all distinct values occurring in W_i have the same positive frequency f, then r[i] = f * (the sum of the min(x, d_i) largest values occurring in W_i), where d_i is the number of distinct values in W_i.
    Preconditions: Let n = len(nums). 1 <= n <= 50; for every j with 0 <= j < n, 1 <= nums[j] <= 50; 1 <= x <= k <= n. -/
  theorem spec_14 (nums : Slice Std.I64) (k x : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
      (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.FindXSum.find_x_sum nums k x = ok r →
          ∀ i : ℕ, i < nwin nums k.val.toNat →
            ∀ f : ℤ, 0 < f →
              (∀ v : ℤ, v ∈ distinct (win nums i k.val.toNat) →
                (cnt (win nums i k.val.toNat) v : ℤ) = f) →
                entry r i =
                  some (f * topSum (win nums i k.val.toNat)
                    (min x.val.toNat (dcount (win nums i k.val.toNat)))) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 50)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 50)
        (hx1 : 1 ≤ x.val) (hxk : x.val ≤ k.val) (hkn : k.val ≤ (nums.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.FindXSum.find_x_sum nums k x = ok r →
            ∀ i : ℕ, i < nwin nums k.val.toNat →
              ∀ f : ℤ, 0 < f →
                (∀ v : ℤ, v ∈ distinct (win nums i k.val.toNat) →
                  (cnt (win nums i k.val.toNat) v : ℤ) = f) →
                  entry r i =
                    some (f * topSum (win nums i k.val.toNat)
                      (min x.val.toNat (dcount (win nums i k.val.toNat))))) := by
    sorry

  end AegisSpec.FindXSum
