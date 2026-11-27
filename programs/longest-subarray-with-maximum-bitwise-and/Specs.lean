import Aegis.LongestSubarray.Code.Funs

/-!
# Specifications of `Aegis.LongestSubarray.longest_subarray`

LeetCode problem `longest-subarray-with-maximum-bitwise-and`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestSubarray

  def elem (nums : Slice Std.I64) (i : Nat) : Int :=
    Option.elim (nums.val[i]?) 0 fun x => x.val

  def band (a b : Int) : Int := ((a.toNat &&& b.toNat : Nat) : Int)

  def andFrom (nums : Slice Std.I64) (l : Nat) : Nat → Int
    | 0 => elem nums l
    | k + 1 => band (andFrom nums l k) (elem nums (l + k + 1))

  def andRange (nums : Slice Std.I64) (l r : Nat) : Int := andFrom nums l (r - l)

  def andLen (nums : Slice Std.I64) (l t : Nat) : Int := andFrom nums l (t - 1)

  def segPairs (m : Nat) : List (Nat × Nat) :=
    (List.range m).flatMap fun l => (List.range (m - l)).map fun k => (l, l + k)

  def maxAnd (nums : Slice Std.I64) : Int :=
    match segPairs nums.val.length with
    | [] => 0
    | p :: ps =>
      ps.foldl (fun acc q => max acc (andRange nums q.1 q.2)) (andRange nums p.1 p.2)

  def lengthsAtMaxAnd (nums : Slice Std.I64) : List Int :=
    List.filterMap
      (fun p =>
        if andRange nums p.1 p.2 = maxAnd nums then some ((p.2 - p.1 + 1 : Nat) : Int)
        else none)
      (segPairs nums.val.length)

  def maxLenAtMaxAnd (nums : Slice Std.I64) : Int := (lengthsAtMaxAnd nums).foldr max 0

  def maxElem (nums : Slice Std.I64) : Int :=
    match nums.val with
    | [] => 0
    | x :: xs => xs.foldl (fun acc y => max acc y.val) x.val

  def countMaxElem (nums : Slice Std.I64) : Nat :=
    (nums.val.filter fun x => x.val = maxElem nums).length

  def toListN {α : Type} : (l : List α) → Aeneas.Data.ListN.ListN α l.length
    | [] => .nil
    | a :: l => .cons a (toListN l)

  def sliceOf (l : List Std.I64) (h : l.length ≤ Usize.max) : Slice Std.I64 where
    leng := l.length
    list := toListN l
    bound := h

  theorem toListN_toList {α : Type} : ∀ l : List α, (toListN l).toList = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [toListN, Aeneas.Data.ListN.ListN.toList, ih]

  theorem toList_length {α : Type} {m : Nat} (l : Aeneas.Data.ListN.ListN α m) :
      l.toList.length = m := by
    induction l with
    | nil => rfl
    | cons a l ih => simp [Aeneas.Data.ListN.ListN.toList, ih]

  def revSlice (nums : Slice Std.I64) : Slice Std.I64 :=
    sliceOf nums.val.reverse (by
      have hlen : nums.val.length = nums.leng := by
        simp [Aeneas.Std.Slice.val, toList_length]
      rw [List.length_reverse, hlen]
      exact nums.bound)

  theorem revSlice_val (nums : Slice Std.I64) : (revSlice nums).val = nums.val.reverse := by
    simp [revSlice, sliceOf, Aeneas.Std.Slice.val, toListN_toList]

  def Pre (nums : Slice Std.I64) (n : Nat) : Prop :=
    n = nums.val.length ∧ 1 ≤ n ∧ n ≤ 100000 ∧
      ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000

  /-- Whenever the function returns a result ans, the following holds. For 0 <= l <= r < n let AND(l,r) be the bitwise AND nums[l] & nums[l+1] & ... & nums[r], and let K = max { AND(l,r) | 0 <= l <= r < n }. Then ans = max { r - l + 1 | 0 <= l <= r < n and AND(l,r) = K }.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_1 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
        ans.val = maxLenAtMaxAnd nums := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
          ans.val = maxLenAtMaxAnd nums) := by
    sorry

  /-- The function returns a result ans; it does not fail, panic, overflow, or access memory out of bounds.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_2 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∃ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∃ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans) := by
    sorry

  /-- Whenever the function returns a result ans, 1 <= ans <= n.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_3 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
        1 ≤ ans.val ∧ ans.val ≤ (n : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
          1 ≤ ans.val ∧ ans.val ≤ (n : Int)) := by
    sorry

  /-- Whenever the function returns a result ans, there exists l such that 0 <= l < n, ans >= 1, l + ans <= n, and AND(l,l+ans-1) = K, where AND(l,r) is the bitwise AND of nums[l],...,nums[r] and K is the maximum of AND(l',r') over all 0 <= l' <= r' < n.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_4 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
        ∃ l, l < n ∧ 1 ≤ ans.val ∧ (l : Int) + ans.val ≤ (n : Int) ∧
          andLen nums l ans.val.toNat = maxAnd nums := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
          ∃ l, l < n ∧ 1 ≤ ans.val ∧ (l : Int) + ans.val ≤ (n : Int) ∧
            andLen nums l ans.val.toNat = maxAnd nums) := by
    sorry

  /-- Whenever the function returns a result ans, for every l and r with 0 <= l <= r < n, if r - l + 1 > ans, then AND(l,r) < K, where K is the maximum of AND(l',r') over all 0 <= l' <= r' < n and AND(l,r) is the bitwise AND of nums[l],...,nums[r].
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_5 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
        ∀ l r, l ≤ r → r < n → (r : Int) - (l : Int) + 1 > ans.val →
          andRange nums l r < maxAnd nums := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
          ∀ l r, l ≤ r → r < n → (r : Int) - (l : Int) + 1 > ans.val →
            andRange nums l r < maxAnd nums) := by
    sorry

  /-- Whenever the function returns a result ans, let M = max_{0 <= i < n} nums[i]. Then there exists l with 0 <= l < n, ans >= 1, and l + ans <= n such that for every i with l <= i < l + ans, nums[i] = M.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_6 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
        ∃ l, l < n ∧ 1 ≤ ans.val ∧ (l : Int) + ans.val ≤ (n : Int) ∧
          ∀ i, l ≤ i → i < l + ans.val.toNat → elem nums i = maxElem nums := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
          ∃ l, l < n ∧ 1 ≤ ans.val ∧ (l : Int) + ans.val ≤ (n : Int) ∧
            ∀ i, l ≤ i → i < l + ans.val.toNat → elem nums i = maxElem nums) := by
    sorry

  /-- Whenever the function returns a result ans, let M = max_{0 <= i < n} nums[i]. Then for every l and t with 0 <= l < n, t >= 1, and l + t <= n, if for every i with l <= i < l + t we have nums[i] = M, then t <= ans.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_7 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
        ∀ (l : Nat) (t : Nat), l < n → 1 ≤ t → (l : Int) + (t : Int) ≤ (n : Int) →
          (∀ i, l ≤ i → i < l + t → elem nums i = maxElem nums) → (t : Int) ≤ ans.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
          ∀ (l : Nat) (t : Nat), l < n → 1 ≤ t → (l : Int) + (t : Int) ≤ (n : Int) →
            (∀ i, l ≤ i → i < l + t → elem nums i = maxElem nums) → (t : Int) ≤ ans.val) := by
    sorry

  /-- Whenever the function returns a result ans, let M = max_{0 <= i < n} nums[i] and let C be the number of indices i with 0 <= i < n and nums[i] = M. Then ans <= C.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_8 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
        ans.val ≤ (countMaxElem nums : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
          ans.val ≤ (countMaxElem nums : Int)) := by
    sorry

  /-- Whenever the function returns a result ans, ans = n if and only if all elements of nums are equal, i.e., nums[i] = nums[j] for every i and j with 0 <= i < n and 0 <= j < n.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_9 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
        (ans.val = (n : Int) ↔ ∀ i j, i < n → j < n → elem nums i = elem nums j) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
          (ans.val = (n : Int) ↔ ∀ i j, i < n → j < n → elem nums i = elem nums j)) := by
    sorry

  /-- Whenever the function returns a result ans, let M = max_{0 <= i < n} nums[i]. If there is exactly one index i with 0 <= i < n and nums[i] = M, then ans = 1.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_10 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
        (∃ i, i < n ∧ elem nums i = maxElem nums ∧
            ∀ j, j < n → elem nums j = maxElem nums → j = i) →
          ans.val = 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
          (∃ i, i < n ∧ elem nums i = maxElem nums ∧
              ∀ j, j < n → elem nums j = maxElem nums → j = i) →
            ans.val = 1) := by
    sorry

  /-- Whenever the function returns a result ans, let M = max_{0 <= i < n} nums[i]. Then ans > 1 if and only if there exists an index i with 0 <= i < n - 1 and nums[i] = nums[i+1] = M.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_11 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
        (ans.val > 1 ↔
          ∃ i, i < n - 1 ∧ elem nums i = maxElem nums ∧ elem nums (i + 1) = maxElem nums) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ ans, Aegis.LongestSubarray.longest_subarray nums = ok ans →
          (ans.val > 1 ↔
            ∃ i, i < n - 1 ∧ elem nums i = maxElem nums ∧ elem nums (i + 1) = maxElem nums)) := by
    sorry

  /-- Let rev(nums) be the slice of length n with rev(nums)[i] = nums[n-1-i] for 0 <= i < n. For every nums satisfying the preconditions, if the function returns ans on nums and ans' on rev(nums), then ans = ans'.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
  theorem spec_12 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
      ∀ ans ans', Aegis.LongestSubarray.longest_subarray nums = ok ans →
        Aegis.LongestSubarray.longest_subarray (revSlice nums) = ok ans' →
          ans.val = ans'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ ans ans', Aegis.LongestSubarray.longest_subarray nums = ok ans →
          Aegis.LongestSubarray.longest_subarray (revSlice nums) = ok ans' →
            ans.val = ans'.val) := by
    sorry

  end AegisSpec.LongestSubarray
