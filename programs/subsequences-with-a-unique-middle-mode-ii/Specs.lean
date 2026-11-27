import Aegis.SubsequencesWithMiddleMode.Code.Funs

/-!
# Specifications of `Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode`

LeetCode problem `subsequences-with-a-unique-middle-mode-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SubsequencesWithMiddleMode

  open Aegis.SubsequencesWithMiddleMode

  def vals (nums : Slice Std.I64) : List ℤ := nums.list.toList.map (fun x => x.val)

  def len (nums : Slice Std.I64) : ℕ := (Slice.len nums).val

  def nth (nums : Slice Std.I64) (i : ℕ) : ℤ := (vals nums).getD i 0

  def freq (v : ℤ) (l : List ℤ) : ℕ := (l.filter (fun x => x = v)).length

  def sel (l : List ℤ) (a b c d e : ℕ) : List ℤ :=
    [l.getD a 0, l.getD b 0, l.getD c 0, l.getD d 0, l.getD e 0]

  def MiddleMode (l : List ℤ) (a b c d e : ℕ) : Prop :=
    ∀ t ∈ [a, b, d, e], l.getD t 0 ≠ l.getD c 0 →
      freq (l.getD t 0) (sel l a b c d e) < freq (l.getD c 0) (sel l a b c d e)

  def GoodTuple (l : List ℤ) (a b c d e : ℕ) : Prop :=
    a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < l.length ∧ MiddleMode l a b c d e

  noncomputable def numGoodTuples (l : List ℤ) : ℕ := by
    classical
    exact ∑ a ∈ Finset.range l.length, ∑ b ∈ Finset.range l.length,
          ∑ c ∈ Finset.range l.length, ∑ d ∈ Finset.range l.length,
          ∑ e ∈ Finset.range l.length, if GoodTuple l a b c d e then 1 else 0

  /-- The function returns a result r, and r is the unique integer with 0 <= r < 1000000007 such that r is congruent modulo 1000000007 to N(nums), where N(nums) is the number of index tuples (a,b,c,d,e) with 0 <= a < b < c < d < e < len(nums) for which the selected sequence s = [nums[a], nums[b], nums[c], nums[d], nums[e]] has nums[c] as a unique mode. Here nums[c] is a unique mode exactly when, for every t in {a,b,d,e} with nums[t] != nums[c], the number of u in {a,b,c,d,e} satisfying nums[u] = nums[t] is strictly less than the number of u in {a,b,c,d,e} satisfying nums[u] = nums[c]. Different index tuples are counted separately even if their value sequences are equal.
    Preconditions: 5 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_vals : ∀ i : ℕ, i < len nums →
        -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        subsequences_with_middle_mode nums = ok r ∧
          0 ≤ r.val ∧ r.val < 1000000007 ∧
          Int.ModEq 1000000007 r.val ((numGoodTuples (vals nums) : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_vals : ∀ i : ℕ, i < len nums →
          -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000), ∃ r : Std.I64,
          subsequences_with_middle_mode nums = ok r ∧
            0 ≤ r.val ∧ r.val < 1000000007 ∧
            Int.ModEq 1000000007 r.val ((numGoodTuples (vals nums) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 1000000007.
    Preconditions: 5 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_vals : ∀ i : ℕ, i < len nums →
        -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
      (r : Std.I64) (h_r : subsequences_with_middle_mode nums = ok r) :
      0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_vals : ∀ i : ℕ, i < len nums →
          -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
        (r : Std.I64) (h_r : subsequences_with_middle_mode nums = ok r), 0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- The function returns a result r on every input satisfying the preconditions; it does not fail, overflow, panic, or access out of bounds.
    Preconditions: 5 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_vals : ∀ i : ℕ, i < len nums →
        -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000) :
      ∃ r : Std.I64, subsequences_with_middle_mode nums = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_vals : ∀ i : ℕ, i < len nums →
          -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000), ∃ r : Std.I64, subsequences_with_middle_mode nums = ok r) := by
    sorry

  /-- The function returns a result r, and r = 1 if the single length-5 subsequence s = [nums[0], nums[1], nums[2], nums[3], nums[4]] has nums[2] as a unique mode, and r = 0 otherwise. Equivalently, r = 1 exactly when for every t in {0,1,3,4} with nums[t] != nums[2], the number of u in {0,1,2,3,4} with nums[u] = nums[t] is strictly less than the number of u in {0,1,2,3,4} with nums[u] = nums[2].
    Preconditions: 5 <= len(nums) <= 100000, for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000, and len(nums) = 5. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_vals : ∀ i : ℕ, i < len nums →
        -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
      (h_len : len nums = 5) :
      ∃ r : Std.I64,
        subsequences_with_middle_mode nums = ok r ∧
          (MiddleMode (vals nums) 0 1 2 3 4 → r.val = 1) ∧
          (¬ MiddleMode (vals nums) 0 1 2 3 4 → r.val = 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_vals : ∀ i : ℕ, i < len nums →
          -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
        (h_len : len nums = 5), ∃ r : Std.I64,
          subsequences_with_middle_mode nums = ok r ∧
            (MiddleMode (vals nums) 0 1 2 3 4 → r.val = 1) ∧
            (¬ MiddleMode (vals nums) 0 1 2 3 4 → r.val = 0)) := by
    sorry

  /-- The function returns a result r, and r = C(len(nums),5) mod 1000000007, where C(n,5) is the number of 5-element subsets of an n-element set.
    Preconditions: 5 <= len(nums) <= 100000, for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000, and there exists a value v such that for every i with 0 <= i < len(nums), nums[i] = v. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_vals : ∀ i : ℕ, i < len nums →
        -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
      (h_const : ∃ v : ℤ, ∀ i : ℕ, i < len nums → nth nums i = v) :
      ∃ r : Std.I64,
        subsequences_with_middle_mode nums = ok r ∧
          r.val = ((Nat.choose (len nums) 5 : ℕ) : ℤ) % 1000000007 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_vals : ∀ i : ℕ, i < len nums →
          -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
        (h_const : ∃ v : ℤ, ∀ i : ℕ, i < len nums → nth nums i = v), ∃ r : Std.I64,
          subsequences_with_middle_mode nums = ok r ∧
            r.val = ((Nat.choose (len nums) 5 : ℕ) : ℤ) % 1000000007) := by
    sorry

  /-- The function returns a result r, and r = 0.
    Preconditions: 5 <= len(nums) <= 100000 and for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_distinct : ∀ i j : ℕ, i < j → j < len nums → nth nums i ≠ nth nums j) :
      ∃ r : Std.I64,
        subsequences_with_middle_mode nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_distinct : ∀ i j : ℕ, i < j → j < len nums → nth nums i ≠ nth nums j), ∃ r : Std.I64,
          subsequences_with_middle_mode nums = ok r ∧ r.val = 0) := by
    sorry

  /-- If the function returns r on nums and r' on b, then r = r'.
    Preconditions: 5 <= len(nums) <= 100000, for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. Also b is a slice with len(b) = len(nums), 5 <= len(b) <= 100000, -1000000000 <= b[i] <= 1000000000 for all valid i, and for every i,j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] = nums[j] if and only if b[i] = b[j]. -/
  theorem spec_7 (nums b : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_vals : ∀ i : ℕ, i < len nums →
        -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
      (h_len_b : len b = len nums)
      (h_b_lo : 5 ≤ len b) (h_b_hi : len b ≤ 100000)
      (h_b_vals : ∀ i : ℕ, i < len b →
        -1000000000 ≤ nth b i ∧ nth b i ≤ 1000000000)
      (h_same : ∀ i j : ℕ, i < len nums → j < len nums →
        (nth nums i = nth nums j ↔ nth b i = nth b j))
      (r r' : Std.I64)
      (h_r : subsequences_with_middle_mode nums = ok r)
      (h_r' : subsequences_with_middle_mode b = ok r') :
      r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums b : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_vals : ∀ i : ℕ, i < len nums →
          -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
        (h_len_b : len b = len nums)
        (h_b_lo : 5 ≤ len b) (h_b_hi : len b ≤ 100000)
        (h_b_vals : ∀ i : ℕ, i < len b →
          -1000000000 ≤ nth b i ∧ nth b i ≤ 1000000000)
        (h_same : ∀ i j : ℕ, i < len nums → j < len nums →
          (nth nums i = nth nums j ↔ nth b i = nth b j))
        (r r' : Std.I64)
        (h_r : subsequences_with_middle_mode nums = ok r)
        (h_r' : subsequences_with_middle_mode b = ok r'), r = r') := by
    sorry

  /-- Let rev be the slice with len(rev) = len(nums) and rev[i] = nums[len(nums)-1-i] for every i with 0 <= i < len(nums). If the function returns r on nums and r_rev on rev, then r = r_rev.
    Preconditions: 5 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_8 (nums rev : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_vals : ∀ i : ℕ, i < len nums →
        -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
      (h_len_rev : len rev = len nums)
      (h_rev : ∀ i : ℕ, i < len nums → nth rev i = nth nums (len nums - 1 - i))
      (r r_rev : Std.I64)
      (h_r : subsequences_with_middle_mode nums = ok r)
      (h_r_rev : subsequences_with_middle_mode rev = ok r_rev) :
      r = r_rev := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums rev : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_vals : ∀ i : ℕ, i < len nums →
          -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
        (h_len_rev : len rev = len nums)
        (h_rev : ∀ i : ℕ, i < len nums → nth rev i = nth nums (len nums - 1 - i))
        (r r_rev : Std.I64)
        (h_r : subsequences_with_middle_mode nums = ok r)
        (h_r_rev : subsequences_with_middle_mode rev = ok r_rev), r = r_rev) := by
    sorry

  /-- Whenever the function returns a result r, if r > 0 then there exists at least one index tuple (a,b,c,d,e) with 0 <= a < b < c < d < e < len(nums) such that in s = [nums[a], nums[b], nums[c], nums[d], nums[e]], nums[c] is a unique mode, i.e. for every t in {a,b,d,e} with nums[t] != nums[c], the frequency of nums[t] in s is strictly less than the frequency of nums[c] in s.
    Preconditions: 5 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_vals : ∀ i : ℕ, i < len nums →
        -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
      (r : Std.I64) (h_r : subsequences_with_middle_mode nums = ok r)
      (h_pos : 0 < r.val) :
      ∃ a b c d e : ℕ, GoodTuple (vals nums) a b c d e := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_vals : ∀ i : ℕ, i < len nums →
          -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
        (r : Std.I64) (h_r : subsequences_with_middle_mode nums = ok r)
        (h_pos : 0 < r.val), ∃ a b c d e : ℕ, GoodTuple (vals nums) a b c d e) := by
    sorry

  /-- Whenever the function returns a result r, if there is no index tuple (a,b,c,d,e) with 0 <= a < b < c < d < e < len(nums) for which nums[c] is a unique mode in [nums[a], nums[b], nums[c], nums[d], nums[e]], then r = 0.
    Preconditions: 5 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_10 (nums : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_vals : ∀ i : ℕ, i < len nums →
        -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
      (r : Std.I64) (h_r : subsequences_with_middle_mode nums = ok r)
      (h_none : ¬ ∃ a b c d e : ℕ, GoodTuple (vals nums) a b c d e) :
      r.val = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_vals : ∀ i : ℕ, i < len nums →
          -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
        (r : Std.I64) (h_r : subsequences_with_middle_mode nums = ok r)
        (h_none : ¬ ∃ a b c d e : ℕ, GoodTuple (vals nums) a b c d e), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, if r > 0 then some integer value v occurs at least twice in nums, i.e. there exist indices i and j with 0 <= i < j < len(nums) and nums[i] = nums[j] = v.
    Preconditions: 5 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_11 (nums : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_vals : ∀ i : ℕ, i < len nums →
        -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
      (r : Std.I64) (h_r : subsequences_with_middle_mode nums = ok r)
      (h_pos : 0 < r.val) :
      ∃ i j : ℕ, i < j ∧ j < len nums ∧ nth nums i = nth nums j := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_vals : ∀ i : ℕ, i < len nums →
          -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
        (r : Std.I64) (h_r : subsequences_with_middle_mode nums = ok r)
        (h_pos : 0 < r.val), ∃ i j : ℕ, i < j ∧ j < len nums ∧ nth nums i = nth nums j) := by
    sorry

  /-- Whenever the function returns a result r, r <= C(len(nums),5), where C(n,5) is the number of 5-element subsets of an n-element set.
    Preconditions: 5 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_12 (nums : Slice Std.I64)
      (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
      (h_vals : ∀ i : ℕ, i < len nums →
        -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
      (r : Std.I64) (h_r : subsequences_with_middle_mode nums = ok r) :
      r.val ≤ ((Nat.choose (len nums) 5 : ℕ) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 5 ≤ len nums) (h_len_hi : len nums ≤ 100000)
        (h_vals : ∀ i : ℕ, i < len nums →
          -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
        (r : Std.I64) (h_r : subsequences_with_middle_mode nums = ok r), r.val ≤ ((Nat.choose (len nums) 5 : ℕ) : ℤ)) := by
    sorry

  end AegisSpec.SubsequencesWithMiddleMode
