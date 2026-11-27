import Aegis.CanSortArray.Code.Funs

/-!
# Specifications of `Aegis.CanSortArray.can_sort_array`

LeetCode problem `find-if-array-can-be-sorted`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CanSortArray (can_sort_array)

namespace AegisSpec.CanSortArray

def pcNat (n : ℕ) : ℕ := (List.range n).countP fun i => n.testBit i

def pc (x : ℤ) : ℕ := pcNat x.natAbs

def elemPc (l : List ℤ) (i : ℕ) : ℕ := pc (l.getD i 0)

def IsMaxSameBitBlock (l : List ℤ) (s e : ℕ) : Prop :=
  s < e ∧ e ≤ l.length ∧
    (∀ i, s ≤ i → i < e → elemPc l i = elemPc l s) ∧
    (s = 0 ∨ elemPc l (s - 1) ≠ elemPc l s) ∧
    (e = l.length ∨ elemPc l e ≠ elemPc l s)

def Nondecreasing (l : List ℤ) : Prop := l.Pairwise (· ≤ ·)

def SameBlockPerm (l l' : List ℤ) (s e : ℕ) : Prop :=
  ((l'.drop s).take (e - s)).Perm ((l.drop s).take (e - s))

def blockMin (l : List ℤ) (s e : ℕ) : Option ℤ := ((l.drop s).take (e - s)).min?

def blockMax (l : List ℤ) (s e : ℕ) : Option ℤ := ((l.drop s).take (e - s)).max?

def SameBitAdjSwapStep (l l' : List ℤ) : Prop :=
  ∃ (pre : List ℤ) (x y : ℤ) (post : List ℤ),
    l = pre ++ x :: y :: post ∧ l' = pre ++ y :: x :: post ∧ pc x = pc y

inductive SameBitSwapReach : List ℤ → List ℤ → Prop
  | refl (l : List ℤ) : SameBitSwapReach l l
  | step {l₁ l₂ l₃ : List ℤ} :
      SameBitAdjSwapStep l₁ l₂ → SameBitSwapReach l₂ l₃ → SameBitSwapReach l₁ l₃

/-- Let pc(x) be the number of 1-bits in the binary representation of x. The function returns a result r (it does not fail), and r = true if and only if for every pair of indices i, j with 0 <= i < j < len(nums) and pc(nums[i]) != pc(nums[j]), we have nums[i] <= nums[j].
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (i.e. 2^8). The bound is read as 2^8 rather than the literal text '28' because the examples contain 30 and 31. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256) :
    ∃ r, can_sort_array nums = ok r ∧
      (r = true ↔ ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
        i < j → pc (nums.val[i]).val ≠ pc (nums.val[j]).val →
          (nums.val[i]).val ≤ (nums.val[j]).val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256), ∃ r, can_sort_array nums = ok r ∧
      (r = true ↔ ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
        i < j → pc (nums.val[i]).val ≠ pc (nums.val[j]).val →
          (nums.val[i]).val ≤ (nums.val[j]).val)) := by
  sorry

/-- For every slice nums satisfying the preconditions, can_sort_array returns some result r; it does not fail (no panic, arithmetic overflow, or out-of-bounds access).
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (2^8). -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256) :
    ∃ r, can_sort_array nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256), ∃ r, can_sort_array nums = ok r) := by
  sorry

/-- Let pc(x) be the number of 1-bits in x. A maximal same-bit block of nums is a maximal contiguous interval [l,r] of indices on which pc(nums[i]) is constant. Whenever can_sort_array returns a result r, r = true if and only if for every pair of consecutive such blocks B (left) and C (right), max_{i in B} nums[i] <= min_{j in C} nums[j].
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (2^8). -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256) :
    ∀ r, can_sort_array nums = ok r →
      (r = true ↔ ∀ (s m e : ℕ), IsMaxSameBitBlock nums.val s m →
        IsMaxSameBitBlock nums.val m e →
          blockMax nums.val s m ≤ blockMin nums.val m e) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256), ∀ r, can_sort_array nums = ok r →
      (r = true ↔ ∀ (s m e : ℕ), IsMaxSameBitBlock nums.val s m →
        IsMaxSameBitBlock nums.val m e →
          blockMax nums.val s m ≤ blockMin nums.val m e)) := by
  sorry

/-- Let a maximal same-bit block of nums be a maximal contiguous interval [l,r] on which pc(nums[i]) is constant. Whenever can_sort_array returns a result r, r = true if and only if there exists an array b of length len(nums) such that (1) for every maximal same-bit block B, the multiset {b[i] : i in B} equals the multiset {nums[i] : i in B}, and (2) b[0] <= b[1] <= ... <= b[len(nums)-1].
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (2^8). -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256) :
    ∀ r, can_sort_array nums = ok r →
      (r = true ↔ ∃ b : List ℤ,
        b.length = nums.val.length ∧
          (∀ (s e : ℕ), IsMaxSameBitBlock nums.val s e → SameBlockPerm nums.val b s e) ∧
            Nondecreasing b) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256), ∀ r, can_sort_array nums = ok r →
      (r = true ↔ ∃ b : List ℤ,
        b.length = nums.val.length ∧
          (∀ (s e : ℕ), IsMaxSameBitBlock nums.val s e → SameBlockPerm nums.val b s e) ∧
            Nondecreasing b)) := by
  sorry

/-- Let pc(x) be the number of 1-bits in x. Whenever can_sort_array returns a result r, r = false if and only if there exist indices i, j with 0 <= i < j < len(nums), pc(nums[i]) != pc(nums[j]), and nums[i] > nums[j].
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (2^8). -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256) :
    ∀ r, can_sort_array nums = ok r →
      (r = false ↔ ∃ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
        i < j ∧ pc (nums.val[i]).val ≠ pc (nums.val[j]).val ∧
          (nums.val[i]).val > (nums.val[j]).val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256), ∀ r, can_sort_array nums = ok r →
      (r = false ↔ ∃ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
        i < j ∧ pc (nums.val[i]).val ≠ pc (nums.val[j]).val ∧
          (nums.val[i]).val > (nums.val[j]).val)) := by
  sorry

/-- Let pc(x) be the number of 1-bits in x. Whenever can_sort_array returns a result r, if pc(nums[0]) = pc(nums[1]) = ... = pc(nums[len(nums)-1]), then r = true.
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (2^8). -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256) :
    ∀ r, can_sort_array nums = ok r →
      (∀ (i : ℕ) (hi : i < nums.val.length), pc (nums.val[i]).val = pc (nums.val[0]).val) →
        r = true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256), ∀ r, can_sort_array nums = ok r →
      (∀ (i : ℕ) (hi : i < nums.val.length), pc (nums.val[i]).val = pc (nums.val[0]).val) →
        r = true) := by
  sorry

/-- Whenever can_sort_array returns a result r, if nums is nondecreasing (nums[0] <= nums[1] <= ... <= nums[len(nums)-1]), then r = true.
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (2^8). -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256) :
    ∀ r, can_sort_array nums = ok r → Nondecreasing nums.val → r = true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256), ∀ r, can_sort_array nums = ok r → Nondecreasing nums.val → r = true) := by
  sorry

/-- Let pc(x) be the number of 1-bits in x. Whenever can_sort_array returns a result r, if the values pc(nums[0]), ..., pc(nums[len(nums)-1]) are pairwise distinct, then r = true if and only if nums is nondecreasing.
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (2^8). -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256) :
    ∀ r, can_sort_array nums = ok r →
      (∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
        i ≠ j → pc (nums.val[i]).val ≠ pc (nums.val[j]).val) →
        (r = true ↔ Nondecreasing nums.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256), ∀ r, can_sort_array nums = ok r →
      (∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
        i ≠ j → pc (nums.val[i]).val ≠ pc (nums.val[j]).val) →
        (r = true ↔ Nondecreasing nums.val)) := by
  sorry

/-- For any two arrays nums and nums' both satisfying the preconditions and having the same length, if nums' is obtained from nums by permuting, for each maximal same-bit block B of nums, the values nums[i] (i in B) arbitrarily among the positions in B, then can_sort_array(nums) returns r, can_sort_array(nums') returns r', and r = r'.
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (2^8). -/
theorem spec_9 (nums nums' : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256)
    (hlen_pos' : 1 ≤ nums'.val.length) (hlen_bnd' : nums'.val.length ≤ 100)
    (hrange' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 256)
    (hsame : nums'.val.length = nums.val.length)
    (hperm : ∀ (s e : ℕ), IsMaxSameBitBlock nums.val s e → SameBlockPerm nums.val nums'.val s e) :
    ∃ r r', can_sort_array nums = ok r ∧ can_sort_array nums' = ok r' ∧ r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256)
    (hlen_pos' : 1 ≤ nums'.val.length) (hlen_bnd' : nums'.val.length ≤ 100)
    (hrange' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 256)
    (hsame : nums'.val.length = nums.val.length)
    (hperm : ∀ (s e : ℕ), IsMaxSameBitBlock nums.val s e → SameBlockPerm nums.val nums'.val s e), ∃ r r', can_sort_array nums = ok r ∧ can_sort_array nums' = ok r' ∧ r = r') := by
  sorry

/-- Let pc(x) be the number of 1-bits in x. For any two arrays nums and nums' both satisfying the preconditions and having the same length, suppose that for every i with 0 <= i < len(nums), pc(nums[i]) = pc(nums'[i]), and that for every maximal same-bit block B (the same index interval in both arrays), min_{i in B} nums[i] = min_{i in B} nums'[i] and max_{i in B} nums[i] = max_{i in B} nums'[i]. Then can_sort_array(nums) returns r, can_sort_array(nums') returns r', and r = r'.
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (2^8). -/
theorem spec_10 (nums nums' : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256)
    (hlen_pos' : 1 ≤ nums'.val.length) (hlen_bnd' : nums'.val.length ≤ 100)
    (hrange' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 256)
    (hsame : nums'.val.length = nums.val.length)
    (hpc : ∀ (i : ℕ) (hi : i < nums.val.length), pc (nums'.val[i]).val = pc (nums.val[i]).val)
    (hminmax : ∀ (s e : ℕ), IsMaxSameBitBlock nums.val s e →
      blockMin nums'.val s e = blockMin nums.val s e ∧
        blockMax nums'.val s e = blockMax nums.val s e) :
    ∃ r r', can_sort_array nums = ok r ∧ can_sort_array nums' = ok r' ∧ r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256)
    (hlen_pos' : 1 ≤ nums'.val.length) (hlen_bnd' : nums'.val.length ≤ 100)
    (hrange' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 256)
    (hsame : nums'.val.length = nums.val.length)
    (hpc : ∀ (i : ℕ) (hi : i < nums.val.length), pc (nums'.val[i]).val = pc (nums.val[i]).val)
    (hminmax : ∀ (s e : ℕ), IsMaxSameBitBlock nums.val s e →
      blockMin nums'.val s e = blockMin nums.val s e ∧
        blockMax nums'.val s e = blockMax nums.val s e), ∃ r r', can_sort_array nums = ok r ∧ can_sort_array nums' = ok r' ∧ r = r') := by
  sorry

/-- Whenever can_sort_array returns true, there exists a finite sequence of operations, each swapping two adjacent elements of the current array that have the same number of set bits, that transforms nums into a nondecreasing array.
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (2^8). -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256) :
    can_sort_array nums = ok true →
      ∃ b : List ℤ, b.length = nums.val.length ∧ SameBitSwapReach nums.val b ∧
        Nondecreasing b := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256), can_sort_array nums = ok true →
      ∃ b : List ℤ, b.length = nums.val.length ∧ SameBitSwapReach nums.val b ∧
        Nondecreasing b) := by
  sorry

/-- Whenever can_sort_array returns false, no finite sequence of operations, each swapping two adjacent elements of the current array that have the same number of set bits, transforms nums into a nondecreasing array.
  Preconditions: len(nums) >= 1 and len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 256 (2^8). -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256) :
    can_sort_array nums = ok false →
      ¬∃ b : List ℤ, b.length = nums.val.length ∧ SameBitSwapReach nums.val b ∧
        Nondecreasing b := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_bnd : nums.val.length ≤ 100)
    (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 256), can_sort_array nums = ok false →
      ¬∃ b : List ℤ, b.length = nums.val.length ∧ SameBitSwapReach nums.val b ∧
        Nondecreasing b) := by
  sorry

end AegisSpec.CanSortArray
