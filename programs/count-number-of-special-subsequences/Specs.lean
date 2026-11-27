import Aegis.CountSpecialSubsequences.Code.Funs

/-!
# Specifications of `Aegis.CountSpecialSubsequences.count_special_subsequences`

LeetCode problem `count-number-of-special-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountSpecialSubsequences

  namespace AegisSpec.CountSpecialSubsequences

  def M : ℕ := 1000000007

  def elem (nums : Slice Std.I64) (i : Fin nums.val.length) : ℤ := (nums.val.get i).val

  def All012 (nums : Slice Std.I64) : Prop :=
    ∀ i : Fin nums.val.length, elem nums i = 0 ∨ elem nums i = 1 ∨ elem nums i = 2

  def cnt (nums : Slice Std.I64) (v : ℤ) : ℕ := (nums.val.map (fun x => x.val)).count v

  def cntIdx (nums : Slice Std.I64) (v : ℤ) (lo hi : ℕ) : ℕ :=
    (Finset.univ.filter
      (fun i : Fin nums.val.length => lo ≤ (i : ℕ) ∧ (i : ℕ) < hi ∧ elem nums i = v)).card

  def IsSpecialIndexSet (nums : Slice Std.I64) (S : Finset (Fin nums.val.length)) : Prop :=
    ∃ A B C : Finset (Fin nums.val.length),
      A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧ S = A ∪ B ∪ C ∧
        (∀ i ∈ A, elem nums i = 0) ∧
        (∀ i ∈ B, elem nums i = 1) ∧
        (∀ i ∈ C, elem nums i = 2) ∧
        (∀ i ∈ A, ∀ j ∈ B, (i : ℕ) < (j : ℕ)) ∧
        (∀ j ∈ B, ∀ k ∈ C, (j : ℕ) < (k : ℕ)) ∧
        (∀ i ∈ A, ∀ k ∈ C, (i : ℕ) < (k : ℕ))

  noncomputable def numSpecial (nums : Slice Std.I64) : ℕ := by
    classical
    exact ((Finset.univ : Finset (Fin nums.val.length)).powerset.filter
      (IsSpecialIndexSet nums)).card

  def subSlice (nums : Slice Std.I64) (a b : ℕ) : Slice Std.I64 :=
    Slice.mk ((nums.val.drop a).take (b + 1 - a)).length
      (Aeneas.Data.ListN.ListN.fromList ((nums.val.drop a).take (b + 1 - a)))
      (by
        have htake : ((nums.val.drop a).take (b + 1 - a)).length ≤ (nums.val.drop a).length := by
          rw [List.length_take]
          exact Nat.min_le_right _ _
        have hdrop : (nums.val.drop a).length ≤ nums.val.length := by
          rw [List.length_drop]
          exact Nat.sub_le _ _
        have hlen : nums.val.length = nums.leng := Aeneas.Data.ListN.ListN_length nums.list
        exact le_trans htake (le_trans hdrop (le_trans hlen.le nums.bound)))

  /-- Let M = 1000000007. Let N be the number of sets I subset of {0,...,len(nums)-1} such that, when the elements of I are written in increasing order as i_1 < ... < i_k, there exist positive integers p,q,s with k = p+q+s and: nums[i_j] = 0 for 1 <= j <= p; nums[i_j] = 1 for p < j <= p+q; nums[i_j] = 2 for p+q < j <= p+q+s. The function returns a result r (it does not fail) and r = N mod M.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] in {0,1,2}. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_vals : All012 nums) :
      ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
        r.val = ((numSpecial nums % M : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_vals : All012 nums), ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
          r.val = ((numSpecial nums % M : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, out-of-bounds access, or 64-bit overflow occurs).
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] in {0,1,2}. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_vals : All012 nums) :
      ∃ r : Std.I64, count_special_subsequences nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_vals : All012 nums), ∃ r : Std.I64, count_special_subsequences nums = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r < M, where M = 1000000007.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] in {0,1,2}. -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_vals : All012 nums) :
      ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
        0 ≤ r.val ∧ r.val < (M : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_vals : All012 nums), ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
          0 ≤ r.val ∧ r.val < (M : ℤ)) := by
    sorry

  /-- Let z = #{i | 0 <= i < len(nums) and nums[i]=0}, o = #{i | 0 <= i < len(nums) and nums[i]=1}, and t = #{i | 0 <= i < len(nums) and nums[i]=2}. The function returns a result r and r <= (2^z - 1)*(2^o - 1)*(2^t - 1). Here the right-hand side is an ordinary mathematical integer, not evaluated with 64-bit wrap-around.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] in {0,1,2}. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_vals : All012 nums) :
      ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
        r.val ≤ ((2 : ℤ) ^ (cnt nums 0) - 1) * ((2 : ℤ) ^ (cnt nums 1) - 1) *
          ((2 : ℤ) ^ (cnt nums 2) - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_vals : All012 nums), ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
          r.val ≤ ((2 : ℤ) ^ (cnt nums 0) - 1) * ((2 : ℤ) ^ (cnt nums 1) - 1) *
            ((2 : ℤ) ^ (cnt nums 2) - 1)) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] in {0,1,2}. There exists v in {0,1,2} such that for every i with 0 <= i < len(nums), nums[i] != v. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_vals : All012 nums)
      (h_missing : ∃ v : ℤ, (v = 0 ∨ v = 1 ∨ v = 2) ∧ ∀ i : Fin nums.val.length,
        elem nums i ≠ v) :
      ∃ r : Std.I64, count_special_subsequences nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_vals : All012 nums)
        (h_missing : ∃ v : ℤ, (v = 0 ∨ v = 1 ∨ v = 2) ∧ ∀ i : Fin nums.val.length,
          elem nums i ≠ v), ∃ r : Std.I64, count_special_subsequences nums = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r = 1 if nums[0]=0 and nums[1]=1 and nums[2]=2, and r = 0 otherwise.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] in {0,1,2}. len(nums) = 3. -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_vals : All012 nums) (h_len3 : nums.val.length = 3) :
      ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
        ((elem nums ⟨0, by omega⟩ = 0 ∧ elem nums ⟨1, by omega⟩ = 1 ∧
            elem nums ⟨2, by omega⟩ = 2) → r.val = 1) ∧
        (¬ (elem nums ⟨0, by omega⟩ = 0 ∧ elem nums ⟨1, by omega⟩ = 1 ∧
            elem nums ⟨2, by omega⟩ = 2) → r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_vals : All012 nums) (h_len3 : nums.val.length = 3), ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
          ((elem nums ⟨0, by omega⟩ = 0 ∧ elem nums ⟨1, by omega⟩ = 1 ∧
              elem nums ⟨2, by omega⟩ = 2) → r.val = 1) ∧
          (¬ (elem nums ⟨0, by omega⟩ = 0 ∧ elem nums ⟨1, by omega⟩ = 1 ∧
              elem nums ⟨2, by omega⟩ = 2) → r.val = 0)) := by
    sorry

  /-- Let z, o, t be the numbers of occurrences of 0, 1, 2 in nums, respectively. The function returns a result r and r = ((2^z - 1)*(2^o - 1)*(2^t - 1)) mod 1000000007.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] in {0,1,2}. For every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_7 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_vals : All012 nums)
      (h_sorted : ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
        i < j → elem nums ⟨i, hi⟩ ≤ elem nums ⟨j, hj⟩) :
      ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
        r.val = (((2 : ℤ) ^ (cnt nums 0) - 1) * ((2 : ℤ) ^ (cnt nums 1) - 1) *
          ((2 : ℤ) ^ (cnt nums 2) - 1)) % (M : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_vals : All012 nums)
        (h_sorted : ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
          i < j → elem nums ⟨i, hi⟩ ≤ elem nums ⟨j, hj⟩), ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
          r.val = (((2 : ℤ) ^ (cnt nums 0) - 1) * ((2 : ℤ) ^ (cnt nums 1) - 1) *
            ((2 : ℤ) ^ (cnt nums 2) - 1)) % (M : ℤ)) := by
    sorry

  /-- Let a be the smallest index with nums[a]=0 and b be the largest index with nums[b]=2. If a < b, then the function returns r and r = count_special_subsequences(nums[a..b]), where nums[a..b] is the slice containing exactly the indices a,a+1,...,b inclusive. If a > b, then the function returns r and r = 0.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] in {0,1,2}. There exists i with nums[i]=0 and there exists i with nums[i]=2. -/
  theorem spec_8 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_vals : All012 nums)
      (a b : ℕ)
      (ha : a < nums.val.length) (ha0 : elem nums ⟨a, ha⟩ = 0)
      (ha_min : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 0 → a ≤ i)
      (hb : b < nums.val.length) (hb2 : elem nums ⟨b, hb⟩ = 2)
      (hb_max : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 2 → i ≤ b) :
      (a < b → ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
        count_special_subsequences (subSlice nums a b) = ok r) ∧
      (b < a → ∃ r : Std.I64, count_special_subsequences nums = ok r ∧ r.val = 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_vals : All012 nums)
        (a b : ℕ)
        (ha : a < nums.val.length) (ha0 : elem nums ⟨a, ha⟩ = 0)
        (ha_min : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 0 → a ≤ i)
        (hb : b < nums.val.length) (hb2 : elem nums ⟨b, hb⟩ = 2)
        (hb_max : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 2 → i ≤ b), (a < b → ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
          count_special_subsequences (subSlice nums a b) = ok r) ∧
        (b < a → ∃ r : Std.I64, count_special_subsequences nums = ok r ∧ r.val = 0)) := by
    sorry

  /-- Let t = #{k | b < k < len(nums) and nums[k]=2}. The function returns a result r and r = (2^t - 1) mod 1000000007.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] in {0,1,2}. There is exactly one index a with nums[a]=0, there is exactly one index b with nums[b]=1, and a < b. -/
  theorem spec_9 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_vals : All012 nums)
      (a : ℕ) (ha : a < nums.val.length) (ha0 : elem nums ⟨a, ha⟩ = 0)
      (ha_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 0 → i = a)
      (b : ℕ) (hb : b < nums.val.length) (hb1 : elem nums ⟨b, hb⟩ = 1)
      (hb_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 1 → i = b)
      (hlt : a < b) :
      ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
        r.val = (((2 : ℤ) ^ (cntIdx nums 2 (b + 1) nums.val.length) - 1) % (M : ℤ)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_vals : All012 nums)
        (a : ℕ) (ha : a < nums.val.length) (ha0 : elem nums ⟨a, ha⟩ = 0)
        (ha_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 0 → i = a)
        (b : ℕ) (hb : b < nums.val.length) (hb1 : elem nums ⟨b, hb⟩ = 1)
        (hb_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 1 → i = b)
        (hlt : a < b), ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
          r.val = (((2 : ℤ) ^ (cntIdx nums 2 (b + 1) nums.val.length) - 1) % (M : ℤ))) := by
    sorry

  /-- Let z = #{i | 0 <= i < b and nums[i]=0}. The function returns a result r and r = (2^z - 1) mod 1000000007.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] in {0,1,2}. There is exactly one index b with nums[b]=1, there is exactly one index c with nums[c]=2, and b < c. -/
  theorem spec_10 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_vals : All012 nums)
      (b : ℕ) (hb : b < nums.val.length) (hb1 : elem nums ⟨b, hb⟩ = 1)
      (hb_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 1 → i = b)
      (c : ℕ) (hc : c < nums.val.length) (hc2 : elem nums ⟨c, hc⟩ = 2)
      (hc_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 2 → i = c)
      (hlt : b < c) :
      ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
        r.val = (((2 : ℤ) ^ (cntIdx nums 0 0 b) - 1) % (M : ℤ)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_vals : All012 nums)
        (b : ℕ) (hb : b < nums.val.length) (hb1 : elem nums ⟨b, hb⟩ = 1)
        (hb_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 1 → i = b)
        (c : ℕ) (hc : c < nums.val.length) (hc2 : elem nums ⟨c, hc⟩ = 2)
        (hc_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 2 → i = c)
        (hlt : b < c), ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
          r.val = (((2 : ℤ) ^ (cntIdx nums 0 0 b) - 1) % (M : ℤ))) := by
    sorry

  /-- Let o = #{i | a < i < c and nums[i]=1}. The function returns a result r and r = (2^o - 1) mod 1000000007.
    Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] in {0,1,2}. There is exactly one index a with nums[a]=0, there is exactly one index c with nums[c]=2, and a < c. -/
  theorem spec_11 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_vals : All012 nums)
      (a : ℕ) (ha : a < nums.val.length) (ha0 : elem nums ⟨a, ha⟩ = 0)
      (ha_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 0 → i = a)
      (c : ℕ) (hc : c < nums.val.length) (hc2 : elem nums ⟨c, hc⟩ = 2)
      (hc_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 2 → i = c)
      (hlt : a < c) :
      ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
        r.val = (((2 : ℤ) ^ (cntIdx nums 1 (a + 1) c) - 1) % (M : ℤ)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_vals : All012 nums)
        (a : ℕ) (ha : a < nums.val.length) (ha0 : elem nums ⟨a, ha⟩ = 0)
        (ha_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 0 → i = a)
        (c : ℕ) (hc : c < nums.val.length) (hc2 : elem nums ⟨c, hc⟩ = 2)
        (hc_uniq : ∀ (i : ℕ) (hi : i < nums.val.length), elem nums ⟨i, hi⟩ = 2 → i = c)
        (hlt : a < c), ∃ r : Std.I64, count_special_subsequences nums = ok r ∧
          r.val = (((2 : ℤ) ^ (cntIdx nums 1 (a + 1) c) - 1) % (M : ℤ))) := by
    sorry

  end AegisSpec.CountSpecialSubsequences
