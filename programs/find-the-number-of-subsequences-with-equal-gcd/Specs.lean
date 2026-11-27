import Aegis.SubsequencePairCount.Code.Funs

/-!
# Specifications of `Aegis.SubsequencePairCount.subsequence_pair_count`

LeetCode problem `find-the-number-of-subsequences-with-equal-gcd`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SubsequencePairCount

  open Aegis.SubsequencePairCount

  def entry (nums : Slice Std.I64) (i : Nat) : Int := (nums.val.getD i default).val

  def setGcd (nums : Slice Std.I64) (S : Finset Nat) : Nat :=
    S.gcd (fun i => (entry nums i).toNat)

  theorem entry_eq_getElem (nums : Slice Std.I64) (i : Nat) (h : i < nums.val.length) :
      entry nums i = (nums.val.get ⟨i, h⟩).val := by
    simp [entry, List.getElem?_eq_getElem h, List.get_eq_getElem]

  def goodPairs (nums : Slice Std.I64) : Finset (Finset Nat × Finset Nat) := by
    classical
    exact
      ((Finset.range nums.val.length).powerset ×ˢ
          (Finset.range nums.val.length).powerset).filter
        (fun p =>
          p.1.Nonempty ∧ p.2.Nonempty ∧ Disjoint p.1 p.2 ∧
            setGcd nums p.1 = setGcd nums p.2)

  def pairCount (nums : Slice Std.I64) : Nat := (goodPairs nums).card

  theorem mem_goodPairs (nums : Slice Std.I64) (p : Finset Nat × Finset Nat) :
      p ∈ goodPairs nums ↔
        p.1 ⊆ Finset.range nums.val.length ∧ p.2 ⊆ Finset.range nums.val.length ∧
          p.1.Nonempty ∧ p.2.Nonempty ∧ Disjoint p.1 p.2 ∧
            setGcd nums p.1 = setGcd nums p.2 := by
    simp [goodPairs, and_assoc]

  def equalPairCount (nums : Slice Std.I64) (n : Nat) : Nat := by
    classical
    exact
      ((Finset.range n) ×ˢ (Finset.range n)).filter
        (fun p => p.1 < p.2 ∧ entry nums p.1 = entry nums p.2) |>.card

  def tripleGcdCount (nums : Slice Std.I64) : Nat := by
    classical
    exact
      ((Finset.range 3).filter
          (fun i =>
            entry nums i =
              ((Nat.gcd (entry nums ((i + 1) % 3)).toNat
                  (entry nums ((i + 2) % 3)).toNat : Nat) : Int))).card

  /-- Let C be the number of ordered pairs (S, T) of finite sets of indices such that S is a subset of {0,...,n-1}, T is a subset of {0,...,n-1}, S is non-empty, T is non-empty, S and T are disjoint, and gcd({nums[i] : i in S}) = gcd({nums[i] : i in T}), where the gcd of a non-empty set of positive integers is the usual greatest common divisor. Let M = 1000000007. The function returns a result r and r is the unique integer such that 0 <= r < M and r is congruent to C modulo M; equivalently, r = C mod M.
    Preconditions: Let n = len(nums), with 1 <= n <= 200, and for every i with 0 <= i < n, 1 <= nums[i] <= 200. -/
  theorem spec_1 (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
      (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200) :
      ∃ r, subsequence_pair_count nums = ok r ∧
        r.val = (pairCount nums : Int) % 1000000007 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
        (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200), ∃ r, subsequence_pair_count nums = ok r ∧
          r.val = (pairCount nums : Int) % 1000000007) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: len(nums) = 1 and 1 <= nums[0] <= 200. -/
  theorem spec_2 (nums : Slice Std.I64) (hlen : nums.val.length = 1)
      (hval : 1 ≤ entry nums 0 ∧ entry nums 0 ≤ 200) :
      ∃ r, subsequence_pair_count nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : nums.val.length = 1)
        (hval : 1 ≤ entry nums 0 ∧ entry nums 0 ≤ 200), ∃ r, subsequence_pair_count nums = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r = 2 if nums[0] = nums[1], and r = 0 otherwise.
    Preconditions: len(nums) = 2, 1 <= nums[0] <= 200, and 1 <= nums[1] <= 200. -/
  theorem spec_3 (nums : Slice Std.I64) (hlen : nums.val.length = 2)
      (hval0 : 1 ≤ entry nums 0 ∧ entry nums 0 ≤ 200)
      (hval1 : 1 ≤ entry nums 1 ∧ entry nums 1 ≤ 200) :
      ∃ r, subsequence_pair_count nums = ok r ∧
        r.val = (if entry nums 0 = entry nums 1 then (2 : Int) else 0) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : nums.val.length = 2)
        (hval0 : 1 ≤ entry nums 0 ∧ entry nums 0 ≤ 200)
        (hval1 : 1 ≤ entry nums 1 ∧ entry nums 1 ≤ 200), ∃ r, subsequence_pair_count nums = ok r ∧
          r.val = (if entry nums 0 = entry nums 1 then (2 : Int) else 0)) := by
    sorry

  /-- Let e be the number of pairs (i,j) with 0 <= i < j < 3 and nums[i] = nums[j]. For each i in {0,1,2}, let j and k be the other two indices, and let m be the number of i in {0,1,2} such that nums[i] = gcd(nums[j], nums[k]). Then the function returns a result r and r = 2*e + 2*m.
    Preconditions: len(nums) = 3, and 1 <= nums[0], nums[1], nums[2] <= 200. -/
  theorem spec_4 (nums : Slice Std.I64) (hlen : nums.val.length = 3)
      (hval0 : 1 ≤ entry nums 0 ∧ entry nums 0 ≤ 200)
      (hval1 : 1 ≤ entry nums 1 ∧ entry nums 1 ≤ 200)
      (hval2 : 1 ≤ entry nums 2 ∧ entry nums 2 ≤ 200) :
      ∃ r, subsequence_pair_count nums = ok r ∧
        r.val = 2 * (equalPairCount nums 3 : Int) + 2 * (tripleGcdCount nums : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : nums.val.length = 3)
        (hval0 : 1 ≤ entry nums 0 ∧ entry nums 0 ≤ 200)
        (hval1 : 1 ≤ entry nums 1 ∧ entry nums 1 ≤ 200)
        (hval2 : 1 ≤ entry nums 2 ∧ entry nums 2 ≤ 200), ∃ r, subsequence_pair_count nums = ok r ∧
          r.val = 2 * (equalPairCount nums 3 : Int) + 2 * (tripleGcdCount nums : Int)) := by
    sorry

  /-- Let M = 1000000007. The function returns a result r and r = (3^n - 2*(2^n) + 1) mod M.
    Preconditions: Let n = len(nums), with 1 <= n <= 200, and suppose there is an integer v with 1 <= v <= 200 such that nums[i] = v for every i with 0 <= i < n. -/
  theorem spec_5 (nums : Slice Std.I64) (n : Nat) (v : Int) (hn : nums.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
      (hv_lo : 1 ≤ v) (hv_hi : v ≤ 200)
      (hall : ∀ i, i < n → entry nums i = v) :
      ∃ r, subsequence_pair_count nums = ok r ∧
        r.val = ((3 : Int) ^ n - 2 * (2 : Int) ^ n + 1) % 1000000007 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (v : Int) (hn : nums.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
        (hv_lo : 1 ≤ v) (hv_hi : v ≤ 200)
        (hall : ∀ i, i < n → entry nums i = v), ∃ r, subsequence_pair_count nums = ok r ∧
          r.val = ((3 : Int) ^ n - 2 * (2 : Int) ^ n + 1) % 1000000007) := by
    sorry

  /-- Let C be the exact count of ordered pairs of non-empty disjoint index subsets of nums whose gcds are equal, before reduction modulo 1000000007. The function returns a result r and r = C.
    Preconditions: Let n = len(nums), with 1 <= n <= 18, and for every i with 0 <= i < n, 1 <= nums[i] <= 200. -/
  theorem spec_6 (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 18)
      (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200) :
      ∃ r, subsequence_pair_count nums = ok r ∧ r.val = (pairCount nums : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 18)
        (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200), ∃ r, subsequence_pair_count nums = ok r ∧ r.val = (pairCount nums : Int)) := by
    sorry

  /-- If the function returns r when called on nums and returns r2 when called on nums2, then r = r2.
    Preconditions: Let nums and nums2 be two slices with the same length n, where 1 <= n <= 200, all entries of both slices lie in [1,200], and nums2 is a permutation of nums: there is a bijection p on {0,...,n-1} such that nums2[i] = nums[p(i)] for every i. -/
  theorem spec_7 (nums nums2 : Slice Std.I64) (n : Nat) (p : Nat → Nat)
      (hn : nums.val.length = n) (hn2 : nums2.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
      (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200)
      (hval2 : ∀ i, i < n → 1 ≤ entry nums2 i ∧ entry nums2 i ≤ 200)
      (hp_mem : ∀ i, i < n → p i < n)
      (hp_inj : ∀ i j, i < n → j < n → p i = p j → i = j)
      (hperm : ∀ i, i < n → entry nums2 i = entry nums (p i)) :
      ∀ r r2, subsequence_pair_count nums = ok r →
        subsequence_pair_count nums2 = ok r2 → r = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (n : Nat) (p : Nat → Nat)
        (hn : nums.val.length = n) (hn2 : nums2.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
        (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200)
        (hval2 : ∀ i, i < n → 1 ≤ entry nums2 i ∧ entry nums2 i ≤ 200)
        (hp_mem : ∀ i, i < n → p i < n)
        (hp_inj : ∀ i j, i < n → j < n → p i = p j → i = j)
        (hperm : ∀ i, i < n → entry nums2 i = entry nums (p i)), ∀ r r2, subsequence_pair_count nums = ok r →
          subsequence_pair_count nums2 = ok r2 → r = r2) := by
    sorry

  /-- Let M = 1000000007. The function returns a result r and r = (3^n - 2*(2^n + n*2^(n-1)) + (n^2 + n + 1)) mod M.
    Preconditions: Let n = len(nums), with 1 <= n <= 200, and suppose every nums[i] satisfies 1 < nums[i] <= 200 and every two distinct entries are coprime: for all i != j, gcd(nums[i], nums[j]) = 1. -/
  theorem spec_8 (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
      (hval : ∀ i, i < n → 1 < entry nums i ∧ entry nums i ≤ 200)
      (hcop : ∀ i j, i < n → j < n → i ≠ j →
        Nat.gcd (entry nums i).toNat (entry nums j).toNat = 1) :
      ∃ r, subsequence_pair_count nums = ok r ∧
        r.val = ((3 : Int) ^ n - 2 * ((2 : Int) ^ n + (n : Int) * (2 : Int) ^ (n - 1)) +
            ((n : Int) ^ 2 + (n : Int) + 1)) % 1000000007 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
        (hval : ∀ i, i < n → 1 < entry nums i ∧ entry nums i ≤ 200)
        (hcop : ∀ i j, i < n → j < n → i ≠ j →
          Nat.gcd (entry nums i).toNat (entry nums j).toNat = 1), ∃ r, subsequence_pair_count nums = ok r ∧
          r.val = ((3 : Int) ^ n - 2 * ((2 : Int) ^ n + (n : Int) * (2 : Int) ^ (n - 1)) +
              ((n : Int) ^ 2 + (n : Int) + 1)) % 1000000007) := by
    sorry

  /-- Let C be the exact count, before reduction modulo 1000000007, of ordered pairs (S,T) of non-empty disjoint index subsets of nums such that gcd({nums[i] : i in S}) = gcd({nums[i] : i in T}); this C is the number whose remainder modulo 1000000007 is the returned value. Then C <= 3^n - 2*2^n + 1.
    Preconditions: Let n = len(nums), with 1 <= n <= 200, and for every i with 0 <= i < n, 1 <= nums[i] <= 200. -/
  theorem spec_9 (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
      (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200) :
      ∃ r, subsequence_pair_count nums = ok r ∧
        r.val = (pairCount nums : Int) % 1000000007 ∧
        (pairCount nums : Int) ≤ (3 : Int) ^ n - 2 * (2 : Int) ^ n + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
        (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200), ∃ r, subsequence_pair_count nums = ok r ∧
          r.val = (pairCount nums : Int) % 1000000007 ∧
          (pairCount nums : Int) ≤ (3 : Int) ^ n - 2 * (2 : Int) ^ n + 1) := by
    sorry

  /-- Let C be the exact count, before reduction modulo 1000000007, of ordered pairs (S,T) of non-empty disjoint index subsets of nums with equal gcd; this C is the number whose remainder modulo 1000000007 is the returned value. Then C is even.
    Preconditions: Let n = len(nums), with 1 <= n <= 200, and for every i with 0 <= i < n, 1 <= nums[i] <= 200. -/
  theorem spec_10 (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
      (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200) :
      ∃ r, subsequence_pair_count nums = ok r ∧
        r.val = (pairCount nums : Int) % 1000000007 ∧
        Even (pairCount nums) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
        (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200), ∃ r, subsequence_pair_count nums = ok r ∧
          r.val = (pairCount nums : Int) % 1000000007 ∧
          Even (pairCount nums)) := by
    sorry

  /-- Let C be the exact count, before reduction modulo 1000000007, of ordered pairs (S,T) of non-empty disjoint index subsets of nums with equal gcd; this C is the number whose remainder modulo 1000000007 is the returned value. Then C >= 2.
    Preconditions: Let n = len(nums), with 1 <= n <= 200, for every i with 0 <= i < n, 1 <= nums[i] <= 200, and suppose there exist indices i and j with 0 <= i < j < n and nums[i] = nums[j]. -/
  theorem spec_11 (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
      (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200)
      (hwit : ∃ i j, i < j ∧ j < n ∧ entry nums i = entry nums j) :
      ∃ r, subsequence_pair_count nums = ok r ∧
        r.val = (pairCount nums : Int) % 1000000007 ∧
        2 ≤ pairCount nums := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 200)
        (hval : ∀ i, i < n → 1 ≤ entry nums i ∧ entry nums i ≤ 200)
        (hwit : ∃ i j, i < j ∧ j < n ∧ entry nums i = entry nums j), ∃ r, subsequence_pair_count nums = ok r ∧
          r.val = (pairCount nums : Int) % 1000000007 ∧
          2 ≤ pairCount nums) := by
    sorry

  end AegisSpec.SubsequencePairCount
