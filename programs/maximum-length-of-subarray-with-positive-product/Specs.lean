import Aegis.GetMaxLen.Code.Funs

/-!
# Specifications of `Aegis.GetMaxLen.get_max_len`

LeetCode problem `maximum-length-of-subarray-with-positive-product`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GetMaxLen

  def entry (nums : Slice Std.I64) (k : ℕ) : Option ℤ :=
    Option.map (fun x => x.val) (nums.val[k]?)

  def seg (nums : Slice Std.I64) (i j : ℕ) : List ℤ :=
    List.map (fun x => x.val) (List.take (j - i) (List.drop i nums.val))

  def isNeg (nums : Slice Std.I64) (k : ℕ) : Bool :=
    Option.any (fun z => decide (z < 0)) (entry nums k)

  def isZero (nums : Slice Std.I64) (k : ℕ) : Bool :=
    Option.any (fun z => decide (z = 0)) (entry nums k)

  def zeroFree (nums : Slice Std.I64) (i j : ℕ) : Prop :=
    ∀ k, i ≤ k → k < j → entry nums k ≠ some 0

  def negCount (nums : Slice Std.I64) (i j : ℕ) : ℕ :=
    List.countP (fun z => decide (z < 0)) (seg nums i j)

  def posProd (nums : Slice Std.I64) (i j : ℕ) : Prop :=
    zeroFree nums i j ∧ negCount nums i j % 2 = 0

  def posProdLen (nums : Slice Std.I64) (L : ℕ) : Prop :=
    L ≤ nums.val.length ∧
      (L = 0 ∨ ∃ i j : ℕ, i < j ∧ j ≤ nums.val.length ∧ j - i = L ∧ posProd nums i j)

  def zeroFreeLen (nums : Slice Std.I64) (L : ℕ) : Prop :=
    ∃ i, i + L ≤ nums.val.length ∧ zeroFree nums i (i + L)

  noncomputable def maxLen (S : ℕ → Prop) (B : ℕ) : ℕ :=
    Finset.sup (@Finset.filter ℕ S (Classical.decPred S) (Finset.range (B + 1))) id

  noncomputable def maxZeroFreeLen (nums : Slice Std.I64) : ℕ :=
    maxLen (zeroFreeLen nums) nums.val.length

  def leftLen (nums : Slice Std.I64) (z L : ℕ) : Prop :=
    L = 0 ∨ ∃ i j : ℕ, i < j ∧ j ≤ z ∧ j - i = L ∧ posProd nums i j

  def rightLen (nums : Slice Std.I64) (z L : ℕ) : Prop :=
    L = 0 ∨
      ∃ i j : ℕ, z + 1 ≤ i ∧ i < j ∧ j ≤ nums.val.length ∧ j - i = L ∧ posProd nums i j

  noncomputable def leftMax (nums : Slice Std.I64) (z : ℕ) : ℕ :=
    maxLen (leftLen nums z) nums.val.length

  noncomputable def rightMax (nums : Slice Std.I64) (z : ℕ) : ℕ :=
    maxLen (rightLen nums z) nums.val.length

  def IsMaxBlock (nums : Slice Std.I64) (a b : ℕ) : Prop :=
    a < b ∧ b ≤ nums.val.length ∧ zeroFree nums a b ∧
      (a = 0 ∨ entry nums (a - 1) = some 0) ∧
      (b = nums.val.length ∨ entry nums b = some 0)

  def firstNeg (nums : Slice Std.I64) (a b : ℕ) : ℕ :=
    (List.find? (fun k => isNeg nums k)
      (List.map (fun t => a + t) (List.range (b - a)))).getD a

  def lastNeg (nums : Slice Std.I64) (a b : ℕ) : ℕ :=
    (List.find? (fun k => isNeg nums k)
      (List.reverse (List.map (fun t => a + t) (List.range (b - a))))).getD a

  def blockVal (nums : Slice Std.I64) (a b : ℕ) : ℕ :=
    if negCount nums a b % 2 = 0 then b - a
    else (b - a) - min (firstNeg nums a b - a + 1) (b - lastNeg nums a b)

  def blockLen (nums : Slice Std.I64) (L : ℕ) : Prop :=
    L = 0 ∨ ∃ a b : ℕ, IsMaxBlock nums a b ∧ blockVal nums a b = L

  /-- The function returns a result r (it does not fail) and r is the maximum of the set S = { L | 0 <= L <= len(nums) and (L = 0 or there exist indices i, j with 0 <= i < j <= len(nums), j - i = L, nums[k] != 0 for every k with i <= k < j, and the number of k with i <= k < j and nums[k] < 0 is even) }. Equivalently, r is the greatest length of a contiguous subarray whose product is positive, where the empty subarray of length 0 is allowed as a fallback; if no nonempty subarray has positive product, r = 0.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
        -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.GetMaxLen.get_max_len nums = ok r ∧
          r.val = ((maxLen (posProdLen nums) nums.val.length : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
          -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.GetMaxLen.get_max_len nums = ok r ∧
            r.val = ((maxLen (posProdLen nums) nums.val.length : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r and does not fail (in particular, no arithmetic overflow, no out-of-bounds indexing, and no panic) for every input satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
        -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
          -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, let M be the maximum length of a contiguous subarray of nums containing no zero: M = max { j - i | 0 <= i <= j <= len(nums) and nums[k] != 0 for every k with i <= k < j }. Then 0 <= r <= M <= len(nums).
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
        -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r →
        0 ≤ r.val ∧ r.val ≤ ((maxZeroFreeLen nums : ℕ) : ℤ) ∧
          ((maxZeroFreeLen nums : ℕ) : ℤ) ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
          -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r →
          0 ≤ r.val ∧ r.val ≤ ((maxZeroFreeLen nums : ℕ) : ℤ) ∧
            ((maxZeroFreeLen nums : ℕ) : ℤ) ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if r > 0 then there exist indices i and j such that 0 <= i < j <= len(nums), j - i = r, nums[k] != 0 for every k with i <= k < j, and the number of k with i <= k < j and nums[k] < 0 is even; if r = 0, the empty subarray of length 0 is allowed and no nonempty witness is required.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
        -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r → 0 < r.val →
        ∃ i j : ℕ, i < j ∧ j ≤ nums.val.length ∧ (j : ℤ) - (i : ℤ) = r.val ∧
          posProd nums i j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
          -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r → 0 < r.val →
          ∃ i j : ℕ, i < j ∧ j ≤ nums.val.length ∧ (j : ℤ) - (i : ℤ) = r.val ∧
            posProd nums i j) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of indices i, j with 0 <= i < j <= len(nums) and j - i > r, the subarray nums[i..j) does not have positive product; equivalently, either there exists k with i <= k < j and nums[k] = 0, or the number of k with i <= k < j and nums[k] < 0 is odd.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
        -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r →
        ∀ i j : ℕ, i < j → j ≤ nums.val.length → r.val < (j : ℤ) - (i : ℤ) →
          ¬ posProd nums i j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
          -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r →
          ∀ i j : ℕ, i < j → j ≤ nums.val.length → r.val < (j : ℤ) - (i : ℤ) →
            ¬ posProd nums i j) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums) if and only if nums[k] != 0 for every k with 0 <= k < len(nums) and the number of k with 0 <= k < len(nums) and nums[k] < 0 is even.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
        -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r →
        (r.val = (nums.val.length : ℤ) ↔ posProd nums 0 nums.val.length) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
          -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r →
          (r.val = (nums.val.length : ℤ) ↔ posProd nums 0 nums.val.length)) := by
    sorry

  /-- Whenever the function returns a result r, for every index z with 0 <= z < len(nums) and nums[z] = 0, define L(z) = max({0} union { j - i | 0 <= i < j <= z, nums[k] != 0 for every k with i <= k < j, and the number of k with i <= k < j and nums[k] < 0 is even }) and R(z) = max({0} union { j - i | z + 1 <= i < j <= len(nums), nums[k] != 0 for every k with i <= k < j, and the number of k with i <= k < j and nums[k] < 0 is even }). Then r = max(L(z), R(z)).
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
        -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r →
        ∀ z : ℕ, z < nums.val.length → entry nums z = some 0 →
          r.val = ((max (leftMax nums z) (rightMax nums z) : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
          -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : Std.I64, Aegis.GetMaxLen.get_max_len nums = ok r →
          ∀ z : ℕ, z < nums.val.length → entry nums z = some 0 →
            r.val = ((max (leftMax nums z) (rightMax nums z) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever get_max_len(nums) returns r and get_max_len(other) returns r2, we have r = r2.
    Preconditions: Both nums and other are slices of i64 with 1 <= len(nums) = len(other) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000 and -1000000000 <= other[i] <= 1000000000; and for every i with 0 <= i < len(nums), nums[i] = 0 if and only if other[i] = 0, and nums[i] < 0 if and only if other[i] < 0. -/
  theorem spec_8 (nums other : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length = other.val.length ∧
        nums.val.length ≤ 100000)
      (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
        -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hbnd' : ∀ (k : ℕ) (x : Std.I64), other.val[k]? = some x →
        -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hagree : ∀ (k : ℕ) (x y : Std.I64), nums.val[k]? = some x → other.val[k]? = some y →
        (x.val = 0 ↔ y.val = 0) ∧ (x.val < 0 ↔ y.val < 0)) :
      ∀ r r2 : Std.I64,
        Aegis.GetMaxLen.get_max_len nums = ok r →
          Aegis.GetMaxLen.get_max_len other = ok r2 → r.val = r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums other : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length = other.val.length ∧
          nums.val.length ≤ 100000)
        (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
          -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hbnd' : ∀ (k : ℕ) (x : Std.I64), other.val[k]? = some x →
          -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hagree : ∀ (k : ℕ) (x y : Std.I64), nums.val[k]? = some x → other.val[k]? = some y →
          (x.val = 0 ↔ y.val = 0) ∧ (x.val < 0 ↔ y.val < 0)), ∀ r r2 : Std.I64,
          Aegis.GetMaxLen.get_max_len nums = ok r →
            Aegis.GetMaxLen.get_max_len other = ok r2 → r.val = r2.val) := by
    sorry

  /-- Let the maximal contiguous zero-free blocks of nums be the intervals [a,b) with 0 <= a < b <= len(nums) such that nums[k] != 0 for every k with a <= k < b, (a = 0 or nums[a-1] = 0), and (b = len(nums) or nums[b] = 0). For each such block B = [a,b), let neg(B) be the number of k with a <= k < b and nums[k] < 0, and define val(B) = b - a if neg(B) is even; if neg(B) is odd, let first(B) = min { k | a <= k < b and nums[k] < 0 } and last(B) = max { k | a <= k < b and nums[k] < 0 }, and val(B) = (b - a) - min(first(B) - a + 1, b - last(B)). Then the function returns a result r and r = max({0} union { val(B) | B is a maximal contiguous zero-free block of nums }).
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
        -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.GetMaxLen.get_max_len nums = ok r ∧
          r.val = ((maxLen (blockLen nums) nums.val.length : ℕ) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hbnd : ∀ (k : ℕ) (x : Std.I64), nums.val[k]? = some x →
          -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.GetMaxLen.get_max_len nums = ok r ∧
            r.val = ((maxLen (blockLen nums) nums.val.length : ℕ) : ℤ)) := by
    sorry

  end AegisSpec.GetMaxLen
