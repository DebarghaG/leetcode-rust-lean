import Aegis.BeautifulSubarrays.Code.Funs

/-!
# Specifications of `Aegis.BeautifulSubarrays.beautiful_subarrays`

LeetCode problem `count-the-number-of-beautiful-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.BeautifulSubarrays

  namespace AegisSpec.BeautifulSubarrays

  def intsOf (xs : List I64) : List Int := xs.map (fun x => x.val)

  def intAt (xs : List I64) (i : Nat) : Int := (intsOf xs).getD i 0

  def xorInt (a b : Int) : Int := ((a.toNat ^^^ b.toNat : Nat) : Int)

  def xorAll (xs : List Int) : Int := xs.foldl (fun acc x => xorInt acc x) 0

  def prefixXor (xs : List Int) (t : Nat) : Int := xorAll (xs.take t)

  def subarrayXor (xs : List Int) (l r : Nat) : Int := xorAll ((xs.drop l).take (r + 1 - l))

  def indexSquare (n : Nat) : Finset (Nat × Nat) := (Finset.range n).product (Finset.range n)

  def subarrayIndices (n : Nat) : Finset (Nat × Nat) :=
    (indexSquare n).filter (fun p => p.1 ≤ p.2)

  def countZeroXorSubarrays (xs : List Int) : Nat :=
    ((subarrayIndices xs.length).filter (fun p => subarrayXor xs p.1 p.2 = 0)).card

  def countZeros (xs : List Int) : Nat :=
    ((Finset.range xs.length).filter (fun i => xs.getD i 0 = 0)).card

  def countEqualNeighbours (xs : List Int) : Nat :=
    ((Finset.range (xs.length - 1)).filter (fun i => xs.getD i 0 = xs.getD (i + 1) 0)).card

  def prefixXorsDistinct (xs : List Int) : Prop :=
    ∀ a b : Nat, a ≤ xs.length → b ≤ xs.length → prefixXor xs a = prefixXor xs b → a = b

  def countEqualPrefixXorPairs (xs : List Int) : Nat :=
    ((indexSquare (xs.length + 1)).filter
      (fun p => p.1 < p.2 ∧ prefixXor xs p.1 = prefixXor xs p.2)).card

  def totalPairs (n : Nat) : Nat := n * (n + 1) / 2

  def revSlice (s : Slice I64) : Slice I64 where
    leng := s.val.reverse.length
    list := Aeneas.Data.ListN.ListN.fromList s.val.reverse
    bound := by
      have h : s.val.reverse.length = s.leng := by
        simp [Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN_length]
      have hb : s.leng ≤ Usize.max := s.bound
      omega

  theorem revSlice_val (s : Slice I64) : (revSlice s).val = s.val.reverse := by
    simp [revSlice, Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

  /-- The function returns a result res (it does not fail) and res equals the number of pairs (l, r) with 0 <= l <= r < len(nums) such that the bitwise XOR of nums[l], nums[l+1], ..., nums[r] is 0. Equivalently, for every bit position k >= 0, the number of indices t in [l, r] whose kth binary bit is 1 is even.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_1 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_entries : ∀ i, i < nums.val.length →
        0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000) :
      ∃ res : I64, beautiful_subarrays nums = ok res ∧
        res.val = (countZeroXorSubarrays (intsOf nums.val) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_entries : ∀ i, i < nums.val.length →
          0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000), ∃ res : I64, beautiful_subarrays nums = ok res ∧
          res.val = (countZeroXorSubarrays (intsOf nums.val) : Int)) := by
    sorry

  /-- For every nums satisfying the preconditions, beautiful_subarrays nums returns a result (Result.ok res for some integer res); it does not fail, panic, overflow, or access out of bounds.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_2 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_entries : ∀ i, i < nums.val.length →
        0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000) :
      ∃ res : I64, beautiful_subarrays nums = ok res := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_entries : ∀ i, i < nums.val.length →
          0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000), ∃ res : I64, beautiful_subarrays nums = ok res) := by
    sorry

  /-- Whenever beautiful_subarrays nums returns a result res, 0 <= res <= len(nums)*(len(nums)+1)/2.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_3 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_entries : ∀ i, i < nums.val.length →
        0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
      (res : I64) (h_res : beautiful_subarrays nums = ok res) :
      0 ≤ res.val ∧ res.val ≤ (totalPairs nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_entries : ∀ i, i < nums.val.length →
          0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
        (res : I64) (h_res : beautiful_subarrays nums = ok res), 0 ≤ res.val ∧ res.val ≤ (totalPairs nums.val.length : Int)) := by
    sorry

  /-- Whenever beautiful_subarrays nums returns a result res, res >= the number of indices i with 0 <= i < len(nums) and nums[i] = 0.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_4 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_entries : ∀ i, i < nums.val.length →
        0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
      (res : I64) (h_res : beautiful_subarrays nums = ok res) :
      (countZeros (intsOf nums.val) : Int) ≤ res.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_entries : ∀ i, i < nums.val.length →
          0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
        (res : I64) (h_res : beautiful_subarrays nums = ok res), (countZeros (intsOf nums.val) : Int) ≤ res.val) := by
    sorry

  /-- Whenever beautiful_subarrays nums returns a result res, res >= the number of indices i with 0 <= i < len(nums) - 1 and nums[i] = nums[i+1].
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_5 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_entries : ∀ i, i < nums.val.length →
        0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
      (res : I64) (h_res : beautiful_subarrays nums = ok res) :
      (countEqualNeighbours (intsOf nums.val) : Int) ≤ res.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_entries : ∀ i, i < nums.val.length →
          0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
        (res : I64) (h_res : beautiful_subarrays nums = ok res), (countEqualNeighbours (intsOf nums.val) : Int) ≤ res.val) := by
    sorry

  /-- Let nums_rev be the array of length len(nums) defined by nums_rev[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). For every nums satisfying the preconditions, if beautiful_subarrays nums returns res and beautiful_subarrays nums_rev returns res_rev, then res = res_rev.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_6 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_entries : ∀ i, i < nums.val.length →
        0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
      (res res_rev : I64)
      (h_res : beautiful_subarrays nums = ok res)
      (h_res_rev : beautiful_subarrays (revSlice nums) = ok res_rev) :
      res.val = res_rev.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_entries : ∀ i, i < nums.val.length →
          0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
        (res res_rev : I64)
        (h_res : beautiful_subarrays nums = ok res)
        (h_res_rev : beautiful_subarrays (revSlice nums) = ok res_rev), res.val = res_rev.val) := by
    sorry

  /-- Let P be defined by P[0] = 0 and, for 1 <= t <= len(nums), P[t] = the bitwise XOR of nums[0], nums[1], ..., nums[t-1]. Whenever beautiful_subarrays nums returns a result res, res equals the number of pairs (a, b) with 0 <= a < b <= len(nums) and P[a] = P[b].
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_7 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_entries : ∀ i, i < nums.val.length →
        0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
      (res : I64) (h_res : beautiful_subarrays nums = ok res) :
      res.val = (countEqualPrefixXorPairs (intsOf nums.val) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_entries : ∀ i, i < nums.val.length →
          0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
        (res : I64) (h_res : beautiful_subarrays nums = ok res), res.val = (countEqualPrefixXorPairs (intsOf nums.val) : Int)) := by
    sorry

  /-- Whenever beautiful_subarrays nums returns a result res, res = 0 if and only if all len(nums)+1 prefix XORs P[0], P[1], ..., P[len(nums)] are pairwise distinct, where P[0] = 0 and P[t] = nums[0] xor ... xor nums[t-1] for 1 <= t <= len(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_8 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_entries : ∀ i, i < nums.val.length →
        0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
      (res : I64) (h_res : beautiful_subarrays nums = ok res) :
      res.val = 0 ↔ prefixXorsDistinct (intsOf nums.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_entries : ∀ i, i < nums.val.length →
          0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
        (res : I64) (h_res : beautiful_subarrays nums = ok res), res.val = 0 ↔ prefixXorsDistinct (intsOf nums.val)) := by
    sorry

  /-- Whenever beautiful_subarrays nums returns a result res, res = len(nums)*(len(nums)+1)/2 if and only if for every i with 0 <= i < len(nums), nums[i] = 0.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_9 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_entries : ∀ i, i < nums.val.length →
        0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
      (res : I64) (h_res : beautiful_subarrays nums = ok res) :
      res.val = (totalPairs nums.val.length : Int) ↔
        ∀ i, i < nums.val.length → intAt nums.val i = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_entries : ∀ i, i < nums.val.length →
          0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
        (res : I64) (h_res : beautiful_subarrays nums = ok res), res.val = (totalPairs nums.val.length : Int) ↔
          ∀ i, i < nums.val.length → intAt nums.val i = 0) := by
    sorry

  /-- Whenever beautiful_subarrays nums returns a result res, res <= len(nums)*(len(nums)+1)/2 - len(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. Additionally for every i with 0 <= i < len(nums), nums[i] != 0. -/
  theorem spec_10 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_entries : ∀ i, i < nums.val.length →
        0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
      (h_nonzero : ∀ i, i < nums.val.length → intAt nums.val i ≠ 0)
      (res : I64) (h_res : beautiful_subarrays nums = ok res) :
      res.val ≤ (totalPairs nums.val.length : Int) - (nums.val.length : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_entries : ∀ i, i < nums.val.length →
          0 ≤ intAt nums.val i ∧ intAt nums.val i ≤ 1000000)
        (h_nonzero : ∀ i, i < nums.val.length → intAt nums.val i ≠ 0)
        (res : I64) (h_res : beautiful_subarrays nums = ok res), res.val ≤ (totalPairs nums.val.length : Int) - (nums.val.length : Int)) := by
    sorry

  end AegisSpec.BeautifulSubarrays
