import Aegis.IsPossibleDivide.Code.Funs

/-!
# Specifications of `Aegis.IsPossibleDivide.is_possible_divide`

LeetCode problem `divide-array-in-sets-of-k-consecutive-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsPossibleDivide

  open Aegis.IsPossibleDivide

  def elems (nums : Slice Std.I64) : List ℤ := nums.val.map (fun v => v.val)

  def cnt (nums : Slice Std.I64) (x : ℤ) : ℕ := (elems nums).filter (fun y => y = x) |>.length

  def IsMax (nums : Slice Std.I64) (M : ℤ) : Prop :=
    M ∈ elems nums ∧ ∀ v ∈ elems nums, v ≤ M

  def IsMin (nums : Slice Std.I64) (m : ℤ) : Prop :=
    m ∈ elems nums ∧ ∀ v ∈ elems nums, m ≤ v

  def FiniteSupport (g : ℤ → ℕ) : Prop :=
    ∃ F : Finset ℤ, ∀ s : ℤ, s ∉ F → g s = 0

  def IsBlockDecomp (nums : Slice Std.I64) (k : ℕ) (g : ℤ → ℕ) : Prop :=
    FiniteSupport g ∧
      ∀ x : ℤ, cnt nums x = Finset.sum (Finset.range k) (fun j => g (x - (j : ℤ)))

  /-- The function returns a result r and r = true if and only if there exists a function g from the integers to the nonnegative integers such that g(s) = 0 for all but finitely many integers s and, for every integer x, cnt(x) = sum_{j=0}^{k-1} g(x - j), where cnt(x) is the number of indices i with 0 <= i < len(nums) and nums[i] = x. Here g(s) represents the number of k-consecutive blocks {s, s+1, ..., s+k-1} used in the division.
    Preconditions: k is a positive integer, 1 <= k <= len(nums) <= 100000, and every entry nums[i] with 0 <= i < len(nums) satisfies 1 <= nums[i] <= 10^9. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9) :
      ∃ r : Bool, is_possible_divide nums k = .ok r ∧
        (r = true ↔ ∃ g : ℤ → ℕ, IsBlockDecomp nums k.val.toNat g) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9), ∃ r : Bool, is_possible_divide nums k = Result.ok r ∧
          (r = true ↔ ∃ g : ℤ → ℕ, IsBlockDecomp nums k.val.toNat g)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or encounter an arithmetic overflow.
    Preconditions: k is a positive integer, 1 <= k <= len(nums) <= 100000, and every entry nums[i] with 0 <= i < len(nums) satisfies 1 <= nums[i] <= 10^9. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9) :
      ∃ r : Bool, is_possible_divide nums k = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9), ∃ r : Bool, is_possible_divide nums k = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, if there is no natural number m with len(nums) = m * k, then r = false.
    Preconditions: k is a positive integer, 1 <= k <= len(nums) <= 100000, and every entry nums[i] with 0 <= i < len(nums) satisfies 1 <= nums[i] <= 10^9. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9) :
      ∀ r : Bool, is_possible_divide nums k = .ok r →
        (¬ ∃ m : ℕ, (nums.val.length : ℤ) = (m : ℤ) * k.val) → r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9), ∀ r : Bool, is_possible_divide nums k = Result.ok r →
          (¬ ∃ m : ℕ, (nums.val.length : ℤ) = (m : ℤ) * k.val) → r = false) := by
    sorry

  /-- Whenever the function returns a result r, if k = 1 then r = true.
    Preconditions: k is a positive integer, 1 <= k <= len(nums) <= 100000, and every entry nums[i] with 0 <= i < len(nums) satisfies 1 <= nums[i] <= 10^9. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9) :
      ∀ r : Bool, is_possible_divide nums k = .ok r → k.val = 1 → r = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9), ∀ r : Bool, is_possible_divide nums k = Result.ok r → k.val = 1 → r = true) := by
    sorry

  /-- Whenever the function returns a result r, if k = len(nums), then r = true if and only if the entries of nums are pairwise distinct and max(nums) - min(nums) = k - 1, where max(nums) and min(nums) are the maximum and minimum entries of nums.
    Preconditions: k is a positive integer, 1 <= k <= len(nums) <= 100000, and every entry nums[i] with 0 <= i < len(nums) satisfies 1 <= nums[i] <= 10^9. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9) :
      ∀ r : Bool, is_possible_divide nums k = .ok r → k.val = (nums.val.length : ℤ) →
        (r = true ↔ (elems nums).Nodup ∧
          ∀ Mx mn : ℤ, IsMax nums Mx → IsMin nums mn → Mx - mn = k.val - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9), ∀ r : Bool, is_possible_divide nums k = Result.ok r → k.val = (nums.val.length : ℤ) →
          (r = true ↔ (elems nums).Nodup ∧
            ∀ Mx mn : ℤ, IsMax nums Mx → IsMin nums mn → Mx - mn = k.val - 1)) := by
    sorry

  /-- Whenever the function returns a result r on nums and a result r' on nums', we have r = r'.
    Preconditions: Let nums and nums' be two slices of i64 such that both satisfy the problem constraints with the same k: 1 <= k <= len(nums) = len(nums') <= 100000, and every entry of nums and nums' lies in 1..10^9. Suppose nums' is a permutation of nums, meaning that for every integer x, the number of indices i with nums'[i] = x equals the number of indices i with nums[i] = x. -/
  theorem spec_6 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen_eq : nums'.val.length = nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9)
      (hval' : ∀ v ∈ nums'.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9)
      (hperm : ∀ x : ℤ, cnt nums' x = cnt nums x) :
      ∀ r r' : Bool, is_possible_divide nums k = .ok r →
        is_possible_divide nums' k = .ok r' → r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen_eq : nums'.val.length = nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9)
        (hval' : ∀ v ∈ nums'.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9)
        (hperm : ∀ x : ℤ, cnt nums' x = cnt nums x), ∀ r r' : Bool, is_possible_divide nums k = Result.ok r →
          is_possible_divide nums' k = Result.ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r, if r = true then for every integer x, k * cnt(x) <= len(nums), where cnt(x) is the number of indices i with 0 <= i < len(nums) and nums[i] = x.
    Preconditions: k is a positive integer, 1 <= k <= len(nums) <= 100000, and every entry nums[i] with 0 <= i < len(nums) satisfies 1 <= nums[i] <= 10^9. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9) :
      ∀ r : Bool, is_possible_divide nums k = .ok r → r = true →
        ∀ x : ℤ, k.val * (cnt nums x : ℤ) ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9), ∀ r : Bool, is_possible_divide nums k = Result.ok r → r = true →
          ∀ x : ℤ, k.val * (cnt nums x : ℤ) ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if r = true and k > 1, then for every integer y with min(nums) <= y <= min(nums) + k - 1, cnt(y) >= cnt(min(nums)), where min(nums) is the minimum entry of nums and cnt(x) is the number of indices i with 0 <= i < len(nums) and nums[i] = x.
    Preconditions: k is a positive integer, 1 <= k <= len(nums) <= 100000, and every entry nums[i] with 0 <= i < len(nums) satisfies 1 <= nums[i] <= 10^9. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9) :
      ∀ r : Bool, is_possible_divide nums k = .ok r → r = true → 1 < k.val →
        ∀ mn : ℤ, IsMin nums mn → ∀ y : ℤ, mn ≤ y → y ≤ mn + k.val - 1 →
          cnt nums mn ≤ cnt nums y := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9), ∀ r : Bool, is_possible_divide nums k = Result.ok r → r = true → 1 < k.val →
          ∀ mn : ℤ, IsMin nums mn → ∀ y : ℤ, mn ≤ y → y ≤ mn + k.val - 1 →
            cnt nums mn ≤ cnt nums y) := by
    sorry

  /-- Whenever the function returns a result r, if r = true and k > 1, then for every integer y with max(nums) - k + 1 <= y <= max(nums), cnt(y) >= cnt(max(nums)), where max(nums) is the maximum entry of nums and cnt(x) is the number of indices i with 0 <= i < len(nums) and nums[i] = x.
    Preconditions: k is a positive integer, 1 <= k <= len(nums) <= 100000, and every entry nums[i] with 0 <= i < len(nums) satisfies 1 <= nums[i] <= 10^9. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9) :
      ∀ r : Bool, is_possible_divide nums k = .ok r → r = true → 1 < k.val →
        ∀ Mx : ℤ, IsMax nums Mx → ∀ y : ℤ, Mx - k.val + 1 ≤ y → y ≤ Mx →
          cnt nums Mx ≤ cnt nums y := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9), ∀ r : Bool, is_possible_divide nums k = Result.ok r → r = true → 1 < k.val →
          ∀ Mx : ℤ, IsMax nums Mx → ∀ y : ℤ, Mx - k.val + 1 ≤ y → y ≤ Mx →
            cnt nums Mx ≤ cnt nums y) := by
    sorry

  /-- If the function returns a result r on nums with r = true and returns a result r' on nums', then r' = true.
    Preconditions: Let nums be a slice satisfying 1 <= k <= len(nums) <= 100000 and all entries in 1..10^9. Let extra be a slice of length k whose entries are exactly the integers s, s+1, ..., s+k-1, each occurring once, for some integer s, and every entry of extra lies in 1..10^9. Let nums' be the concatenation of nums followed by extra, and assume len(nums') <= 100000. -/
  theorem spec_10 (nums extra nums' : Slice Std.I64) (k : Std.I64) (s : ℤ)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9)
      (hextra_len : extra.val.length = k.val.toNat)
      (hextra_cnt : ∀ x : ℤ, cnt extra x = if s ≤ x ∧ x < s + k.val then 1 else 0)
      (hextra_val : ∀ v ∈ extra.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9)
      (hcat : nums'.val = nums.val ++ extra.val)
      (hlen' : nums'.val.length ≤ 100000) :
      ∀ r r' : Bool, is_possible_divide nums k = .ok r → r = true →
        is_possible_divide nums' k = .ok r' → r' = true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums extra nums' : Slice Std.I64) (k : Std.I64) (s : ℤ)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9)
        (hextra_len : extra.val.length = k.val.toNat)
        (hextra_cnt : ∀ x : ℤ, cnt extra x = if s ≤ x ∧ x < s + k.val then 1 else 0)
        (hextra_val : ∀ v ∈ extra.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9)
        (hcat : nums'.val = nums.val ++ extra.val)
        (hlen' : nums'.val.length ≤ 100000), ∀ r r' : Bool, is_possible_divide nums k = Result.ok r → r = true →
          is_possible_divide nums' k = Result.ok r' → r' = true) := by
    sorry

  /-- Whenever the function returns a result r on nums, if r = true and len(nums) > k, then there exists an integer s and a slice nums' of length len(nums) - k such that: (a) for every integer x in {s, s+1, ..., s+k-1}, the count of x in nums is at least 1, and for every integer x, the count of x in nums' is cnt(x) - 1 when x is in {s, s+1, ..., s+k-1} and is cnt(x) otherwise; (b) the function returns true on nums'. Here cnt(x) is the number of indices i with 0 <= i < len(nums) and nums[i] = x.
    Preconditions: k is a positive integer, 1 <= k <= len(nums) <= 100000, and every entry nums[i] with 0 <= i < len(nums) satisfies 1 <= nums[i] <= 10^9. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9) :
      ∀ r : Bool, is_possible_divide nums k = .ok r → r = true →
        k.val < (nums.val.length : ℤ) →
        ∃ s : ℤ, ∃ nums' : Slice Std.I64,
          nums'.val.length = nums.val.length - k.val.toNat ∧
          (∀ x : ℤ, s ≤ x → x < s + k.val → 1 ≤ cnt nums x) ∧
          (∀ x : ℤ, cnt nums' x =
            if s ≤ x ∧ x < s + k.val then cnt nums x - 1 else cnt nums x) ∧
          is_possible_divide nums' k = .ok true := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9), ∀ r : Bool, is_possible_divide nums k = Result.ok r → r = true →
          k.val < (nums.val.length : ℤ) →
          ∃ s : ℤ, ∃ nums' : Slice Std.I64,
            nums'.val.length = nums.val.length - k.val.toNat ∧
            (∀ x : ℤ, s ≤ x → x < s + k.val → 1 ≤ cnt nums x) ∧
            (∀ x : ℤ, cnt nums' x =
              if s ≤ x ∧ x < s + k.val then cnt nums x - 1 else cnt nums x) ∧
            is_possible_divide nums' k = Result.ok true) := by
    sorry

  /-- Whenever the function returns a result r, if r = true and k > 1, then for every integer x with cnt(x) > 0, either cnt(x - 1) > 0 or cnt(x + 1) > 0, where cnt(x) is the number of indices i with 0 <= i < len(nums) and nums[i] = x.
    Preconditions: k is a positive integer, 1 <= k <= len(nums) <= 100000, and every entry nums[i] with 0 <= i < len(nums) satisfies 1 <= nums[i] <= 10^9. -/
  theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
      (hk_pos : 1 ≤ k.val)
      (hk_len : k.val ≤ (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9) :
      ∀ r : Bool, is_possible_divide nums k = .ok r → r = true → 1 < k.val →
        ∀ x : ℤ, 0 < cnt nums x → 0 < cnt nums (x - 1) ∨ 0 < cnt nums (x + 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk_pos : 1 ≤ k.val)
        (hk_len : k.val ≤ (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9), ∀ r : Bool, is_possible_divide nums k = Result.ok r → r = true → 1 < k.val →
          ∀ x : ℤ, 0 < cnt nums x → 0 < cnt nums (x - 1) ∨ 0 < cnt nums (x + 1)) := by
    sorry

  end AegisSpec.IsPossibleDivide
