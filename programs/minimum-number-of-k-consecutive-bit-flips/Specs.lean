import Aegis.MinKBitFlips.Code.Funs

/-!
# Specifications of `Aegis.MinKBitFlips.min_k_bit_flips`

LeetCode problem `minimum-number-of-k-consecutive-bit-flips`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinKBitFlips

  open Classical

  def bits (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def Admissible (k : Int) (n : Nat) (s : Nat) : Prop :=
    (s : Int) + k ≤ (n : Int)

  def allAdmissible (k : Int) (n : Nat) (starts : List Nat) : Prop :=
    ∀ s ∈ starts, Admissible k n s

  abbrev inWindow (k : Int) (s i : Nat) : Prop :=
    (s : Int) ≤ (i : Int) ∧ (i : Int) < (s : Int) + k

  def coverCount (k : Int) (starts : List Nat) (i : Nat) : Nat :=
    (starts.filter (fun s => decide (inWindow k s i))).length

  def flippedAt (b : List Int) (k : Int) (starts : List Nat) (i : Nat) : Int :=
    match b[i]? with
    | some x => if coverCount k starts i % 2 = 0 then x else 1 - x
    | none => 0

  def applyFlips (b : List Int) (k : Int) (starts : List Nat) : List Int :=
    (List.range b.length).map (flippedAt b k starts)

  def allOnes (b : List Int) : Prop := ∀ x ∈ b, x = 1

  def allZeros (b : List Int) : Prop := ∀ x ∈ b, x = 0

  def makesAllOnes (b : List Int) (k : Int) (starts : List Nat) : Prop :=
    allAdmissible k b.length starts ∧ allOnes (applyFlips b k starts)

  def zeroCount (b : List Int) : Nat := (b.filter (fun x => x == 0)).length

  def occCount (s : Nat) (l : List Nat) : Nat :=
    (l.filter (fun t => decide (t = s))).length

  noncomputable def minFlips (b : List Int) (k : Int) : Int :=
    if h : ∃ m : Nat, ∃ starts : List Nat, starts.length = m ∧ makesAllOnes b k starts
    then (Nat.find h : Int) else -1

  /-- Let n = len(nums). For an integer s with 0 <= s <= n-k, call a k-bit flip at s the operation that changes nums[i] to 1 - nums[i] for every i with s <= i < s+k and leaves every other position unchanged. The function returns a result r, and either: (a) r >= 0 and there exists a finite sequence s_0,...,s_{r-1} of start indices, each in [0, n-k], such that applying the flips at these starts (in any order) makes every entry equal to 1, and no finite sequence of fewer than r start indices in [0, n-k] has this property; or (b) r = -1 and no finite sequence of start indices in [0, n-k] makes every entry equal to 1.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∃ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r ∧
        ((0 ≤ r.val ∧
            ∃ starts : List Nat, (starts.length : Int) = r.val ∧
              makesAllOnes (bits nums) k.val starts ∧
              ∀ starts' : List Nat,
                makesAllOnes (bits nums) k.val starts' → r.val ≤ (starts'.length : Int)) ∨
          (r.val = -1 ∧ ∀ starts : List Nat, ¬ makesAllOnes (bits nums) k.val starts)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∃ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r ∧
          ((0 ≤ r.val ∧
              ∃ starts : List Nat, (starts.length : Int) = r.val ∧
                makesAllOnes (bits nums) k.val starts ∧
                ∀ starts' : List Nat,
                  makesAllOnes (bits nums) k.val starts' → r.val ≤ (starts'.length : Int)) ∨
            (r.val = -1 ∧ ∀ starts : List Nat, ¬ makesAllOnes (bits nums) k.val starts))) := by
    sorry

  /-- Under these preconditions, the function returns a result r; it does not fail, panic, or return an error.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∃ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∃ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 0 <= r <= n-k+1.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
        r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (n : Int) - k.val + 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
          r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (n : Int) - k.val + 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if nums[i] = 1 for every i with 0 <= i < n.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
        (r.val = 0 ↔ allOnes (bits nums)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
          (r.val = 0 ↔ allOnes (bits nums))) := by
    sorry

  /-- Whenever the function returns a result r, r equals the number of indices i with 0 <= i < n and nums[i] = 0.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, k = 1, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk : k.val = 1)
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
        r.val = (zeroCount (bits nums) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk : k.val = 1)
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
          r.val = (zeroCount (bits nums) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, the following holds: r = 0 if nums[i] = 1 for every i with 0 <= i < n; r = 1 if nums[i] = 0 for every i with 0 <= i < n; and r = -1 otherwise.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, 1 <= k = n, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val = (n : Int))
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
        (allOnes (bits nums) → r.val = 0) ∧
        (allZeros (bits nums) → r.val = 1) ∧
        (¬ allOnes (bits nums) → ¬ allZeros (bits nums) → r.val = -1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val = (n : Int))
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
          (allOnes (bits nums) → r.val = 0) ∧
          (allZeros (bits nums) → r.val = 1) ∧
          (¬ allOnes (bits nums) → ¬ allZeros (bits nums) → r.val = -1)) := by
    sorry

  /-- Let z be the number of indices i with 0 <= i < n and nums[i] = 0. Whenever the function returns a result r with r >= 0, r*k and z have the same parity; equivalently, r*k - z is even.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
        0 ≤ r.val →
        ∃ m : Int, r.val * k.val - (zeroCount (bits nums) : Int) = 2 * m := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
          0 ≤ r.val →
          ∃ m : Int, r.val * k.val - (zeroCount (bits nums) : Int) = 2 * m) := by
    sorry

  /-- Let z be the number of indices i with 0 <= i < n and nums[i] = 0. Whenever the function returns a result r with r >= 0, r*k >= z.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
        0 ≤ r.val → (zeroCount (bits nums) : Int) ≤ r.val * k.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
          0 ≤ r.val → (zeroCount (bits nums) : Int) ≤ r.val * k.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there exists an integer s with 0 <= s <= n-k such that nums[i] = 0 for every i with s <= i < s+k, and nums[i] = 1 for every i with 0 <= i < n and not (s <= i < s+k).
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
        (r.val = 1 ↔
          ∃ s : Nat, Admissible k.val n s ∧
            ∀ i, i < n →
              (inWindow k.val s i → (bits nums)[i]? = some 0) ∧
              (¬ inWindow k.val s i → (bits nums)[i]? = some 1)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
          (r.val = 1 ↔
            ∃ s : Nat, Admissible k.val n s ∧
              ∀ i, i < n →
                (inWindow k.val s i → (bits nums)[i]? = some 0) ∧
                (¬ inWindow k.val s i → (bits nums)[i]? = some 1))) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, there exists a set S of integers such that S is a subset of {s | 0 <= s <= n-k}, S has exactly r elements, and starting from nums, flipping exactly once at every s in S makes every entry equal to 1.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
        0 ≤ r.val →
        ∃ S : Finset Nat, (∀ s ∈ S, Admissible k.val n s) ∧
          (S.card : Int) = r.val ∧
          makesAllOnes (bits nums) k.val S.toList := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
          0 ≤ r.val →
          ∃ S : Finset Nat, (∀ s ∈ S, Admissible k.val n s) ∧
            (S.card : Int) = r.val ∧
            makesAllOnes (bits nums) k.val S.toList) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for any two finite sequences A and B of start indices in [0, n-k] such that applying A and applying B each make every entry of nums equal to 1, and for every s with 0 <= s <= n-k, the number of occurrences of s in A and the number of occurrences of s in B have the same parity.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
        r.val ≠ -1 →
        ∀ A B : List Nat,
          makesAllOnes (bits nums) k.val A →
          makesAllOnes (bits nums) k.val B →
          ∀ s : Nat, Admissible k.val n s →
            occCount s A % 2 = occCount s B % 2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
          r.val ≠ -1 →
          ∀ A B : List Nat,
            makesAllOnes (bits nums) k.val A →
            makesAllOnes (bits nums) k.val B →
            ∀ s : Nat, Admissible k.val n s →
              occCount s A % 2 = occCount s B % 2) := by
    sorry

  /-- Let rev be the array of length n defined by rev[i] = nums[n-1-i] for every i with 0 <= i < n. Whenever the function returns a result r, r is exactly the minimum number of k-bit flips needed to make rev all ones, with the convention that this minimum is -1 if no such sequence exists.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
  theorem spec_12 (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
      (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1) :
      ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
        r.val = minFlips (bits nums).reverse k.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : Int))
        (hbits : ∀ x ∈ bits nums, x = 0 ∨ x = 1), ∀ r, Aegis.MinKBitFlips.min_k_bit_flips nums k = Result.ok r →
          r.val = minFlips (bits nums).reverse k.val) := by
    sorry

  end AegisSpec.MinKBitFlips
