import Aegis.MinimumReplacement.Code.Funs

/-!
# Specifications of `Aegis.MinimumReplacement.minimum_replacement`

LeetCode problem `minimum-replacements-to-sort-the-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumReplacement

  def contents (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def nth (nums : Slice Std.I64) (i : ℕ) : ℤ :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  def Nondecreasing : List ℤ → Prop
    | [] => True
    | [_] => True
    | x :: y :: t => x ≤ y ∧ Nondecreasing (y :: t)

  def ceilDiv (a b : ℤ) : ℤ := if 1 ≤ b then (a + (b - 1)) / b else 0

  def sumInit (l : List ℤ) (f : ℤ → ℤ) : ℤ := (l.dropLast.map f).sum

  def IsReplacement (a a' : List ℤ) : Prop :=
    ∃ (pre : List ℤ) (x y : ℤ) (post : List ℤ),
      a = pre ++ [x + y] ++ post ∧ a' = pre ++ [x] ++ [y] ++ post ∧ 0 < x ∧ 0 < y

  def ReachIn : ℕ → List ℤ → List ℤ → Prop
    | 0, a, b => b = a
    | k + 1, a, c => ∃ b, ReachIn k a b ∧ IsReplacement b c

  structure SortedExpansion (a : List ℤ) : Type where

    blocks : List (List ℤ)

    blocks_ne : ∀ blk ∈ blocks, blk ≠ []

    blocks_pos : ∀ blk ∈ blocks, ∀ x ∈ blk, 0 < x

    blocks_sum : blocks.map List.sum = a

    blocks_sorted : Nondecreasing blocks.flatten

  namespace SortedExpansion

  def values {a : List ℤ} (e : SortedExpansion a) : List ℤ := e.blocks.flatten

  def cost {a : List ℤ} (e : SortedExpansion a) : ℤ :=
    (e.values.length : ℤ) - (a.length : ℤ)

  end SortedExpansion

  def kSumFrom : List ℤ → ℤ → ℤ
    | [], _ => 0
    | x :: xs, U =>
      let k := ceilDiv x U
      (k - 1) + kSumFrom xs (x / k)

  def kSum (a : List ℤ) : ℤ :=
    match a.reverse with
    | [] => 0
    | last :: rev => kSumFrom rev last

  /-- Let n = len(nums). Call an array b[0..m-1] a valid sorted expansion of nums when: (1) b is a finite nondecreasing sequence of positive integers; (2) there are indices 0 = p_0 < p_1 < ... < p_n = m such that for every i with 0 <= i < n, the sum of b[p_i], b[p_i+1], ..., b[p_{i+1}-1] equals nums[i]. The operation count of this expansion is m - n. Under the preconditions, minimum_replacement(nums) returns a result r, and r is equal to the minimum operation count over all valid sorted expansions of nums.
    Preconditions: Let n = len(nums). 1 <= n <= 10^5 and 1 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9) :
      ∃ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r ∧
        (∃ e : SortedExpansion (contents nums), e.cost = r.val) ∧
        (∀ e : SortedExpansion (contents nums), r.val ≤ e.cost) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9), ∃ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r ∧
          (∃ e : SortedExpansion (contents nums), e.cost = r.val) ∧
          (∀ e : SortedExpansion (contents nums), r.val ≤ e.cost)) := by
    sorry

  /-- Under the preconditions, minimum_replacement(nums) returns a result (it does not fail, overflow, or panic).
    Preconditions: Let n = len(nums). 1 <= n <= 10^5 and 1 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9) :
      ∃ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9), ∃ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r) := by
    sorry

  /-- Whenever minimum_replacement(nums) returns a result r under the preconditions, r >= 0.
    Preconditions: Let n = len(nums). The slice nums satisfies n >= 1 and 1 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hn : 1 ≤ nums.val.length)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9) :
      ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 1 ≤ nums.val.length)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9), ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever minimum_replacement(nums) returns a result r under the preconditions, r <= sum_{i=0}^{n-2} (nums[i] - 1), where n = len(nums) and the sum is 0 when n = 1.
    Preconditions: Let n = len(nums). The slice nums satisfies n >= 1 and 1 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hn : 1 ≤ nums.val.length)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9) :
      ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
        r.val ≤ sumInit (contents nums) (fun x => x - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 1 ≤ nums.val.length)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9), ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
          r.val ≤ sumInit (contents nums) (fun x => x - 1)) := by
    sorry

  /-- Under the preconditions, let r be the returned value. Then r = 0 if and only if for every i with 0 <= i < n-1, nums[i] <= nums[i+1].
    Preconditions: Let n = len(nums). 1 <= n <= 10^5 and 1 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9) :
      ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
        (r.val = 0 ↔ Nondecreasing (contents nums)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9), ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
          (r.val = 0 ↔ Nondecreasing (contents nums))) := by
    sorry

  /-- Under the preconditions, let r be the returned value. Then r = ceil(nums[0] / nums[1]) - 1, where ceil(a/b) is the least integer q with a <= q*b.
    Preconditions: Let n = len(nums). The slice nums satisfies n = 2 and 1 <= nums[i] <= 10^9 for i = 0,1. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hn : nums.val.length = 2)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9) :
      ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
        r.val = ceilDiv (nth nums 0) (nth nums 1) - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : nums.val.length = 2)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9), ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
          r.val = ceilDiv (nth nums 0) (nth nums 1) - 1) := by
    sorry

  /-- Let nums' be the slice obtained by appending v_0, ..., v_{k-1} to nums. Under the preconditions, minimum_replacement(nums') and minimum_replacement(nums) return results r' and r, and r' = r.
    Preconditions: Let n = len(nums). 1 <= n <= 10^5 and 1 <= nums[i] <= 10^9 for every i with 0 <= i < n. Let k >= 1 with n + k <= 10^5, and let v_0, ..., v_{k-1} be integers satisfying nums[n-1] <= v_0 <= v_1 <= ... <= v_{k-1} <= 10^9. -/
  theorem spec_7 (nums nums' : Slice Std.I64) (vs : List ℤ)
      (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9)
      (hk : vs ≠ [])
      (hkn : nums.val.length + vs.length ≤ 10 ^ 5)
      (hsorted : Nondecreasing vs)
      (hrange : ∀ v ∈ vs, nth nums (nums.val.length - 1) ≤ v ∧ v ≤ 10 ^ 9)
      (hcontents : contents nums' = contents nums ++ vs) :
      ∃ r r', Aegis.MinimumReplacement.minimum_replacement nums' = ok r' ∧
        Aegis.MinimumReplacement.minimum_replacement nums = ok r ∧ r'.val = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (vs : List ℤ)
        (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9)
        (hk : vs ≠ [])
        (hkn : nums.val.length + vs.length ≤ 10 ^ 5)
        (hsorted : Nondecreasing vs)
        (hrange : ∀ v ∈ vs, nth nums (nums.val.length - 1) ≤ v ∧ v ≤ 10 ^ 9)
        (hcontents : contents nums' = contents nums ++ vs), ∃ r r', Aegis.MinimumReplacement.minimum_replacement nums' = ok r' ∧
          Aegis.MinimumReplacement.minimum_replacement nums = ok r ∧ r'.val = r.val) := by
    sorry

  /-- Whenever minimum_replacement(nums) returns a result r under the preconditions, r >= sum_{i=0}^{n-2} (ceil(nums[i] / nums[n-1]) - 1), where ceil(a/b) is the least integer q with a <= q*b, and the sum is 0 when n = 1.
    Preconditions: Let n = len(nums). The slice nums satisfies n >= 1 and 1 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hn : 1 ≤ nums.val.length)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9) :
      ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
        sumInit (contents nums)
          (fun x => ceilDiv x (nth nums (nums.val.length - 1)) - 1) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 1 ≤ nums.val.length)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9), ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
          sumInit (contents nums)
            (fun x => ceilDiv x (nth nums (nums.val.length - 1)) - 1) ≤ r.val) := by
    sorry

  /-- Under the preconditions, let r be the returned value. There exists a finite sequence of exactly r valid replacement operations that transforms nums into a nondecreasing array.
    Preconditions: Let n = len(nums). 1 <= n <= 10^5 and 1 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9) :
      ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
        ∃ k : ℕ, (k : ℤ) = r.val ∧
          ∃ b : List ℤ, ReachIn k (contents nums) b ∧ Nondecreasing b := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9), ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
          ∃ k : ℕ, (k : ℤ) = r.val ∧
            ∃ b : List ℤ, ReachIn k (contents nums) b ∧ Nondecreasing b) := by
    sorry

  /-- Let A be the slice P followed by a, and let B be the slice P followed by b. Under the preconditions, minimum_replacement(A) and minimum_replacement(B) return results r_A and r_B, and r_A >= r_B.
    Preconditions: Let P be a finite sequence of integers with 0 <= len(P) and len(P)+1 <= 10^5, and 1 <= P[j] <= 10^9 for every j with 0 <= j < len(P). Let a and b be integers with 1 <= a <= b <= 10^9. -/
  theorem spec_10 (P : List ℤ) (a b : ℤ) (A B : Slice Std.I64)
      (hP : ∀ x ∈ P, 1 ≤ x ∧ x ≤ 10 ^ 9)
      (hlen : P.length + 1 ≤ 10 ^ 5)
      (hab : 1 ≤ a ∧ a ≤ b ∧ b ≤ 10 ^ 9)
      (hA : contents A = P ++ [a]) (hB : contents B = P ++ [b]) :
      ∃ rA rB, Aegis.MinimumReplacement.minimum_replacement A = ok rA ∧
        Aegis.MinimumReplacement.minimum_replacement B = ok rB ∧ rB.val ≤ rA.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (P : List ℤ) (a b : ℤ) (A B : Slice Std.I64)
        (hP : ∀ x ∈ P, 1 ≤ x ∧ x ≤ 10 ^ 9)
        (hlen : P.length + 1 ≤ 10 ^ 5)
        (hab : 1 ≤ a ∧ a ≤ b ∧ b ≤ 10 ^ 9)
        (hA : contents A = P ++ [a]) (hB : contents B = P ++ [b]), ∃ rA rB, Aegis.MinimumReplacement.minimum_replacement A = ok rA ∧
          Aegis.MinimumReplacement.minimum_replacement B = ok rB ∧ rB.val ≤ rA.val) := by
    sorry

  /-- Under the preconditions, let r be the returned value. Every nondecreasing array obtainable from nums by any finite sequence of valid replacement operations has length at least r + len(nums).
    Preconditions: Let n = len(nums). 1 <= n <= 10^5 and 1 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9) :
      ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
        ∀ (k : ℕ) (b : List ℤ), ReachIn k (contents nums) b → Nondecreasing b →
          r.val + ((contents nums).length : ℤ) ≤ (b.length : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9), ∀ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r →
          ∀ (k : ℕ) (b : List ℤ), ReachIn k (contents nums) b → Nondecreasing b →
            r.val + ((contents nums).length : ℤ) ≤ (b.length : ℤ)) := by
    sorry

  /-- Let U_{n-1} = nums[n-1] and k_{n-1} = 1. For i = n-2, n-3, ..., 0, define k_i = ceil(nums[i] / U_{i+1}) and U_i = floor(nums[i] / k_i), where ceil(a/b) is the least integer q with a <= q*b and floor(a/b) is the greatest integer q with q*b <= a. Then with r = minimum_replacement(nums), r = sum_{i=0}^{n-1} (k_i - 1).
    Preconditions: Let n = len(nums). 1 <= n <= 10^5 and 1 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9) :
      ∃ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r ∧
        r.val = kSum (contents nums) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9), ∃ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r ∧
          r.val = kSum (contents nums)) := by
    sorry

  /-- Under the preconditions, there exists an optimal valid sorted expansion of nums, i.e. one with operation count r, in which the block corresponding to nums[n-1] consists of the single element nums[n-1]. Equivalently, the last original element is never split in some optimal solution.
    Preconditions: Let n = len(nums). 1 <= n <= 10^5 and 1 <= nums[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_13 (nums : Slice Std.I64)
      (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9) :
      ∃ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r ∧
        ∃ e : SortedExpansion (contents nums), e.cost = r.val ∧
          e.blocks.getLast? = some [nth nums (nums.val.length - 1)] := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 1 ≤ nums.val.length) (hnmax : nums.val.length ≤ 10 ^ 5)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10 ^ 9), ∃ r, Aegis.MinimumReplacement.minimum_replacement nums = ok r ∧
          ∃ e : SortedExpansion (contents nums), e.cost = r.val ∧
            e.blocks.getLast? = some [nth nums (nums.val.length - 1)]) := by
    sorry

  end AegisSpec.MinimumReplacement
