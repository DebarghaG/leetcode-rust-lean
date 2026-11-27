import Aegis.SingleNonDuplicate.Code.Funs

/-!
# Specifications of `Aegis.SingleNonDuplicate.single_non_duplicate`

LeetCode problem `single-element-in-a-sorted-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.SingleNonDuplicate

  namespace AegisSpec.SingleNonDuplicate

  def elem (nums : Slice Std.I64) (i : Fin nums.val.length) : Int := (nums.val.get i).val

  def Nondecreasing (nums : Slice Std.I64) : Prop :=
    ∀ (i : Nat) (h : i + 1 < nums.val.length),
      elem nums ⟨i, by omega⟩ ≤ elem nums ⟨i + 1, h⟩

  def count (nums : Slice Std.I64) (x : Int) : Nat :=
    nums.val.countP (fun y => decide (y.val = x))

  def countLt (nums : Slice Std.I64) (x : Int) : Nat :=
    nums.val.countP (fun y => decide (y.val < x))

  def searchSteps : Nat → Nat
    | 0 => 0
    | n + 1 => 1 + searchSteps (n / 2)

  def comparisons (n : Nat) : Nat := 2 * searchSteps n + 2

  def auxSpace (_n : Nat) : Nat := 6

  /-- The function returns a result r, and r is the unique value occurring exactly once in nums: count(nums,r) = 1 and for every integer x with x != r, count(nums,x) = 0 or count(nums,x) = 2.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r ∧
        count nums r.val = 1 ∧
        ∀ x : Int, x ≠ r.val → count nums x = 0 ∨ count nums x = 2 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r ∧
          count nums r.val = 1 ∧
          ∀ x : Int, x ≠ r.val → count nums x = 0 ∨ count nums x = 2) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail due to arithmetic overflow, out-of-bounds indexing, or panic.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r) := by
    sorry

  /-- The function returns a result r and there exists an index i with 0 <= i < len(nums) such that nums[i] = r.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r ∧
        ∃ (i : Fin nums.val.length), elem nums i = r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r ∧
          ∃ (i : Fin nums.val.length), elem nums i = r.val) := by
    sorry

  /-- The function returns a result r and count(nums,r) = 1; that is, exactly one index i with 0 <= i < len(nums) satisfies nums[i] = r.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r ∧ count nums r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r ∧ count nums r.val = 1) := by
    sorry

  /-- The function returns a result r and, for every index i with 0 <= i < len(nums) and nums[i] != r, count(nums,nums[i]) = 2.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r ∧
        ∀ (i : Fin nums.val.length), elem nums i ≠ r.val → count nums (elem nums i) = 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r ∧
          ∀ (i : Fin nums.val.length), elem nums i ≠ r.val → count nums (elem nums i) = 2) := by
    sorry

  /-- The function returns a result r and, among all integer values occurring in nums, r is the only value whose occurrence count is odd.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r ∧
        count nums r.val % 2 = 1 ∧
        ∀ x : Int, (∃ (i : Fin nums.val.length), elem nums i = x) → x ≠ r.val →
          count nums x % 2 = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r ∧
          count nums r.val % 2 = 1 ∧
          ∀ x : Int, (∃ (i : Fin nums.val.length), elem nums i = x) → x ≠ r.val →
            count nums x % 2 = 0) := by
    sorry

  /-- The function returns a result r and, if len(nums) >= 2 and nums[0] != nums[1], then r = nums[0].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r ∧
        (∀ (h2 : 2 ≤ nums.val.length),
          elem nums ⟨0, by omega⟩ ≠ elem nums ⟨1, by omega⟩ →
            r.val = elem nums ⟨0, by omega⟩) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r ∧
          (∀ (h2 : 2 ≤ nums.val.length),
            elem nums ⟨0, by omega⟩ ≠ elem nums ⟨1, by omega⟩ →
              r.val = elem nums ⟨0, by omega⟩)) := by
    sorry

  /-- The function returns a result r and, if len(nums) >= 2 and nums[len(nums)-2] != nums[len(nums)-1], then r = nums[len(nums)-1].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r ∧
        (∀ (h2 : 2 ≤ nums.val.length),
          elem nums ⟨nums.val.length - 2, by omega⟩ ≠
            elem nums ⟨nums.val.length - 1, by omega⟩ →
          r.val = elem nums ⟨nums.val.length - 1, by omega⟩) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r ∧
          (∀ (h2 : 2 ≤ nums.val.length),
            elem nums ⟨nums.val.length - 2, by omega⟩ ≠
              elem nums ⟨nums.val.length - 1, by omega⟩ →
            r.val = elem nums ⟨nums.val.length - 1, by omega⟩)) := by
    sorry

  /-- The function returns a result r and there is an index i with 0 <= i < len(nums) and nums[i] = r such that every index j with 0 <= j < len(nums) and nums[j] = r satisfies j mod 2 = 0.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r ∧
        ∃ (i : Fin nums.val.length), elem nums i = r.val ∧
          ∀ (j : Fin nums.val.length), elem nums j = r.val → j.val % 2 = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r ∧
          ∃ (i : Fin nums.val.length), elem nums i = r.val ∧
            ∀ (j : Fin nums.val.length), elem nums j = r.val → j.val % 2 = 0) := by
    sorry

  /-- The function returns a result r and there is an index i with 0 <= i < len(nums) and nums[i] = r such that for every j with 0 <= j < i, nums[j] < r, and for every j with i < j < len(nums), r < nums[j].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r ∧
        ∃ (i : Fin nums.val.length), elem nums i = r.val ∧
          (∀ (j : Fin nums.val.length), j.val < i.val → elem nums j < r.val) ∧
          (∀ (j : Fin nums.val.length), i.val < j.val → r.val < elem nums j) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r ∧
          ∃ (i : Fin nums.val.length), elem nums i = r.val ∧
            (∀ (j : Fin nums.val.length), j.val < i.val → elem nums j < r.val) ∧
            (∀ (j : Fin nums.val.length), i.val < j.val → r.val < elem nums j)) := by
    sorry

  /-- The function returns a result r and the number of indices i with 0 <= i < len(nums) and nums[i] < r is even.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r ∧ countLt nums r.val % 2 = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r ∧ countLt nums r.val % 2 = 0) := by
    sorry

  /-- The function returns a result r, there exists an index i with 0 <= i < len(nums) and nums[i] = r, and for every such i, (i = 0 or nums[i-1] < r) and (i = len(nums)-1 or r < nums[i+1]).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]); there is exactly one value v with count(nums,v)=1, and for every integer x != v, count(nums,x)=0 or count(nums,x)=2. Here count(nums,x) is the number of indices i with 0 <= i < len(nums) and nums[i]=x. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (hsorted : Nondecreasing nums)
      (huniq : ∃ v : Int, count nums v = 1 ∧
        ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2) :
      ∃ r, single_non_duplicate nums = ok r ∧
        (∃ (i : Fin nums.val.length), elem nums i = r.val) ∧
        ∀ (j : Fin nums.val.length), elem nums j = r.val →
          (∀ (_hj : j.val ≠ 0), elem nums ⟨j.val - 1, by omega⟩ < r.val) ∧
          (∀ (_hj : j.val ≠ nums.val.length - 1),
            r.val < elem nums ⟨j.val + 1, by omega⟩) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Fin nums.val.length), 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (hsorted : Nondecreasing nums)
        (huniq : ∃ v : Int, count nums v = 1 ∧
          ∀ x : Int, x ≠ v → count nums x = 0 ∨ count nums x = 2), ∃ r, single_non_duplicate nums = ok r ∧
          (∃ (i : Fin nums.val.length), elem nums i = r.val) ∧
          ∀ (j : Fin nums.val.length), elem nums j = r.val →
            (∀ (_hj : j.val ≠ 0), elem nums ⟨j.val - 1, by omega⟩ < r.val) ∧
            (∀ (_hj : j.val ≠ nums.val.length - 1),
              r.val < elem nums ⟨j.val + 1, by omega⟩)) := by
    sorry

  end AegisSpec.SingleNonDuplicate
