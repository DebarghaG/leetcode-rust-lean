import Aegis.MinimumSplits.Code.Funs

/-!
# Specifications of `Aegis.MinimumSplits.minimum_splits`

LeetCode problem `minimum-split-into-subarrays-with-gcd-greater-than-one`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumSplits

  open Aegis.MinimumSplits

  def atVal (nums : List Std.I64) (i : ℕ) : ℤ :=
    if h : i < nums.length then (nums[i]).val else 0

  def gcd2 (nums : List Std.I64) (i j : ℕ) : ℕ := Int.gcd (atVal nums i) (atVal nums j)

  def segGCD (nums : List Std.I64) (a b : ℕ) : ℕ :=
    ((nums.drop a).take (b - a)).foldl (fun acc x => Int.gcd acc x.val) 0

  def cutPairs (cuts : List ℕ) : List (ℕ × ℕ) := cuts.zip cuts.tail

  def cutTriples : List ℕ → List (ℕ × ℕ × ℕ)
    | a :: b :: c :: rest => (a, b, c) :: cutTriples (b :: c :: rest)
    | _ => []

  def StrictInc (l : List ℕ) : Prop := ∀ p ∈ cutPairs l, p.1 < p.2

  def IsPartition (nums : List Std.I64) (cuts : List ℕ) : Prop :=
    cuts.head? = some 0 ∧
    cuts.getLast? = some nums.length ∧
    StrictInc cuts ∧
    ∀ p ∈ cutPairs cuts, 1 < segGCD nums p.1 p.2

  def HasPartition (nums : List Std.I64) (k : ℕ) : Prop :=
    ∃ cuts : List ℕ, IsPartition nums cuts ∧ cuts.length = k + 1

  def HasPartitionOn (nums : List Std.I64) (a b k : ℕ) : Prop :=
    ∃ cuts : List ℕ,
      cuts.head? = some a ∧
      cuts.getLast? = some b ∧
      StrictInc cuts ∧
      cuts.length = k + 1 ∧
      ∀ p ∈ cutPairs cuts, 1 < segGCD nums p.1 p.2

  noncomputable def M (nums : List Std.I64) (a b : ℕ) : ℕ :=
    sInf {k : ℕ | HasPartitionOn nums a b k}

  def ceilDiv2 (n : ℕ) : ℕ := (n + 1) / 2

  def ValidInput (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧
    nums.val.length ≤ 2000 ∧
    ∀ x ∈ nums.val, 2 ≤ x.val ∧ x.val ≤ 10 ^ 9

  /-- The function returns a result r, and r is the least positive integer k for which there exist cut indices 0 = i_0 < i_1 < ... < i_k = n such that, for every j with 1 <= j <= k, the GCD of nums[i_{j-1}], nums[i_{j-1}+1], ..., nums[i_j - 1] is strictly greater than 1.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_1 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∃ r : Std.I64,
        minimum_splits nums = ok r ∧
        1 ≤ r.val ∧
        HasPartition nums.val r.val.toNat ∧
        ∀ k : ℕ, 1 ≤ k → HasPartition nums.val k → r.val.toNat ≤ k := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∃ r : Std.I64,
          minimum_splits nums = ok r ∧
          1 ≤ r.val ∧
          HasPartition nums.val r.val.toNat ∧
          ∀ k : ℕ, 1 ≤ k → HasPartition nums.val k → r.val.toNat ≤ k) := by
    sorry

  /-- The function returns a result r; in particular, the call does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_2 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∃ r : Std.I64, minimum_splits nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∃ r : Std.I64, minimum_splits nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= n.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_3 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r : Std.I64,
        minimum_splits nums = ok r → 1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r : Std.I64,
          minimum_splits nums = ok r → 1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- If n = 1, then whenever the function returns a result r, r = 1.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_4 (nums : Slice Std.I64) (hpre : ValidInput nums)
      (hn : nums.val.length = 1) :
      ∀ r : Std.I64, minimum_splits nums = ok r → r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums)
        (hn : nums.val.length = 1), ∀ r : Std.I64, minimum_splits nums = ok r → r.val = 1) := by
    sorry

  /-- If n = 2, then whenever the function returns a result r, r = 1 if gcd(nums[0], nums[1]) > 1, and r = 2 otherwise.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_5 (nums : Slice Std.I64) (hpre : ValidInput nums)
      (hn : nums.val.length = 2) :
      ∀ r : Std.I64,
        minimum_splits nums = ok r →
          r.val = (if 1 < gcd2 nums.val 0 1 then (1 : ℤ) else 2) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums)
        (hn : nums.val.length = 2), ∀ r : Std.I64,
          minimum_splits nums = ok r →
            r.val = (if 1 < gcd2 nums.val 0 1 then (1 : ℤ) else 2)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if the GCD of nums[0], nums[1], ..., nums[n-1] is strictly greater than 1.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_6 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r : Std.I64,
        minimum_splits nums = ok r →
          (r.val = 1 ↔ 1 < segGCD nums.val 0 nums.val.length) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r : Std.I64,
          minimum_splits nums = ok r →
            (r.val = 1 ↔ 1 < segGCD nums.val 0 nums.val.length)) := by
    sorry

  /-- Whenever the function returns a result r, r = n if and only if gcd(nums[i], nums[i+1]) = 1 for every i with 0 <= i < n-1.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_7 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r : Std.I64,
        minimum_splits nums = ok r →
          (r.val = (nums.val.length : ℤ) ↔
            ∀ i : ℕ, i + 1 < nums.val.length → gcd2 nums.val i (i + 1) = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r : Std.I64,
          minimum_splits nums = ok r →
            (r.val = (nums.val.length : ℤ) ↔
              ∀ i : ℕ, i + 1 < nums.val.length → gcd2 nums.val i (i + 1) = 1)) := by
    sorry

  /-- Whenever the function returns a result r, there exist cut indices 0 = i_0 < i_1 < ... < i_r = n such that, for every j with 1 <= j <= r, the GCD of nums[i_{j-1}], nums[i_{j-1}+1], ..., nums[i_j - 1] is strictly greater than 1.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_8 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r : Std.I64,
        minimum_splits nums = ok r →
          ∃ cuts : List ℕ, IsPartition nums.val cuts ∧ cuts.length = r.val.toNat + 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r : Std.I64,
          minimum_splits nums = ok r →
            ∃ cuts : List ℕ, IsPartition nums.val cuts ∧ cuts.length = r.val.toNat + 1) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k >= 1 and every sequence of cut indices 0 = i_0 < i_1 < ... < i_k = n such that each segment nums[i_{j-1}], nums[i_{j-1}+1], ..., nums[i_j - 1] has GCD strictly greater than 1, we have k >= r.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_9 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r : Std.I64,
        minimum_splits nums = ok r →
          ∀ k : ℕ, 1 ≤ k → HasPartition nums.val k → r.val ≤ (k : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r : Std.I64,
          minimum_splits nums = ok r →
            ∀ k : ℕ, 1 ≤ k → HasPartition nums.val k → r.val ≤ (k : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every valid partition of nums into exactly r subarrays with cut indices 0 = i_0 < i_1 < ... < i_r = n, and for every j with 1 <= j < r, the GCD of the union nums[i_{j-1}], nums[i_{j-1}+1], ..., nums[i_{j+1} - 1] is equal to 1.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_10 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r : Std.I64,
        minimum_splits nums = ok r →
          ∀ cuts : List ℕ,
            IsPartition nums.val cuts → cuts.length = r.val.toNat + 1 →
              ∀ t ∈ cutTriples cuts, segGCD nums.val t.1 t.2.2 = 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r : Std.I64,
          minimum_splits nums = ok r →
            ∀ cuts : List ℕ,
              IsPartition nums.val cuts → cuts.length = r.val.toNat + 1 →
                ∀ t ∈ cutTriples cuts, segGCD nums.val t.1 t.2.2 = 1) := by
    sorry

  /-- Whenever the function returns a result r, if there exists an index c with 1 <= c < n such that the GCD of nums[0], nums[1], ..., nums[c-1] is greater than 1 and the GCD of nums[c], nums[c+1], ..., nums[n-1] is greater than 1, then r <= 2.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_11 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r : Std.I64,
        minimum_splits nums = ok r →
          (∃ c : ℕ,
              1 ≤ c ∧ c < nums.val.length ∧
                1 < segGCD nums.val 0 c ∧ 1 < segGCD nums.val c nums.val.length) →
            r.val ≤ 2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r : Std.I64,
          minimum_splits nums = ok r →
            (∃ c : ℕ,
                1 ≤ c ∧ c < nums.val.length ∧
                  1 < segGCD nums.val 0 c ∧ 1 < segGCD nums.val c nums.val.length) →
              r.val ≤ 2) := by
    sorry

  /-- Whenever the function returns a result r and r = 2, there exists an index c with 1 <= c < n such that the GCD of nums[0], nums[1], ..., nums[c-1] is greater than 1 and the GCD of nums[c], nums[c+1], ..., nums[n-1] is greater than 1.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_12 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r : Std.I64,
        minimum_splits nums = ok r → r.val = 2 →
          ∃ c : ℕ,
            1 ≤ c ∧ c < nums.val.length ∧
              1 < segGCD nums.val 0 c ∧ 1 < segGCD nums.val c nums.val.length := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r : Std.I64,
          minimum_splits nums = ok r → r.val = 2 →
            ∃ c : ℕ,
              1 ≤ c ∧ c < nums.val.length ∧
                1 < segGCD nums.val 0 c ∧ 1 < segGCD nums.val c nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, if an index i with 0 <= i < n satisfies gcd(nums[i], nums[j]) = 1 for every j with 0 <= j < n and j != i, then r = 1 + M(0,i) + M(i+1,n), where M(a,b) denotes the minimum number of contiguous pieces into which nums[a], nums[a+1], ..., nums[b-1] can be partitioned so that each piece has GCD greater than 1, with M(a,a) = 0.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_13 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r : Std.I64,
        minimum_splits nums = ok r →
          ∀ i : ℕ,
            i < nums.val.length →
              (∀ j : ℕ, j < nums.val.length → j ≠ i → gcd2 nums.val i j = 1) →
                r.val = 1 + (M nums.val 0 i : ℤ) + (M nums.val (i + 1) nums.val.length : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r : Std.I64,
          minimum_splits nums = ok r →
            ∀ i : ℕ,
              i < nums.val.length →
                (∀ j : ℕ, j < nums.val.length → j ≠ i → gcd2 nums.val i j = 1) →
                  r.val = 1 + (M nums.val 0 i : ℤ) + (M nums.val (i + 1) nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if gcd(nums[i], nums[i+1]) > 1 for every i with 0 <= i < n-1, then r <= ceil(n/2), where ceil(n/2) is the smallest integer greater than or equal to n/2.
    Preconditions: Let n = len(nums). The call is made only on inputs satisfying n >= 1, n <= 2000, and 2 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_14 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r : Std.I64,
        minimum_splits nums = ok r →
          (∀ i : ℕ, i + 1 < nums.val.length → 1 < gcd2 nums.val i (i + 1)) →
            r.val ≤ (ceilDiv2 nums.val.length : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r : Std.I64,
          minimum_splits nums = ok r →
            (∀ i : ℕ, i + 1 < nums.val.length → 1 < gcd2 nums.val i (i + 1)) →
              r.val ≤ (ceilDiv2 nums.val.length : ℤ)) := by
    sorry

  end AegisSpec.MinimumSplits
