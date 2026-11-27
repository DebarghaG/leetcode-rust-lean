import Aegis.FindLhs.Code.Funs

/-!
# Specifications of `Aegis.FindLhs.find_lhs`

LeetCode problem `longest-harmonious-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindLhs

def atIdx (l : List Std.I64) (i : ℕ) (h : i < l.length) : ℤ := (l.get ⟨i, h⟩).val

def cnt (l : List Std.I64) (v : ℤ) : ℕ := l.countP (fun x => decide (x.val = v))

def InRange (l : List Std.I64) : Prop :=
  ∀ (i : ℕ) (h : i < l.length), -1000000000 ≤ atIdx l i h ∧ atIdx l i h ≤ 1000000000

def IsSubseq {α : Type} (sub l : List α) : Prop :=
  ∃ f : Fin sub.length → Fin l.length,
    StrictMono f ∧ ∀ i : Fin sub.length, sub.get i = l.get (f i)

def maxVal : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldl max x

def minVal : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldl min x

def vals (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

noncomputable def maxCnt (l : List Std.I64) : ℕ := (vals l).toFinset.sup (fun v => cnt l v)

/-- Let cnt(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. The function returns a result r, and r = 0 if there is no integer v such that cnt(v) > 0 and cnt(v+1) > 0; otherwise r = max { cnt(v) + cnt(v+1) | v is an integer, cnt(v) > 0, cnt(v+1) > 0 }.
  Preconditions: 1 <= len(nums) <= 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val) :
    ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      (((¬ ∃ v : ℤ, 0 < cnt nums.val v ∧ 0 < cnt nums.val (v + 1)) ∧ r.val = 0) ∨
        (∃ v : ℤ, 0 < cnt nums.val v ∧ 0 < cnt nums.val (v + 1) ∧
          r.val = ((cnt nums.val v + cnt nums.val (v + 1) : ℕ) : ℤ) ∧
          ∀ w : ℤ, 0 < cnt nums.val w → 0 < cnt nums.val (w + 1) →
            cnt nums.val w + cnt nums.val (w + 1) ≤ cnt nums.val v + cnt nums.val (v + 1))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val), ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      (((¬ ∃ v : ℤ, 0 < cnt nums.val v ∧ 0 < cnt nums.val (v + 1)) ∧ r.val = 0) ∨
        (∃ v : ℤ, 0 < cnt nums.val v ∧ 0 < cnt nums.val (v + 1) ∧
          r.val = ((cnt nums.val v + cnt nums.val (v + 1) : ℕ) : ℤ) ∧
          ∀ w : ℤ, 0 < cnt nums.val w → 0 < cnt nums.val (w + 1) →
            cnt nums.val w + cnt nums.val (w + 1) ≤ cnt nums.val v + cnt nums.val (v + 1)))) := by
  sorry

/-- The function returns a result r, and 0 <= r <= len(nums).
  Preconditions: 1 <= len(nums) <= 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val) :
    ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      0 ≤ r.val ∧ r.val ≤ ((nums.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val), ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      0 ≤ r.val ∧ r.val ≤ ((nums.val.length : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result r; no arithmetic overflow, out-of-bounds access, or panic occurs.
  Preconditions: 1 <= len(nums) <= 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val) :
    ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val), ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r) := by
  sorry

/-- The function returns a result r, and either r = 0 or r >= 2.
  Preconditions: 1 <= len(nums) <= 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val) :
    ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧ (r.val = 0 ∨ 2 ≤ r.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val), ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧ (r.val = 0 ∨ 2 ≤ r.val)) := by
  sorry

/-- The function returns a result r, and r = len(nums) if and only if there exists an integer a such that (1) for every i with 0 <= i < len(nums), nums[i] = a or nums[i] = a+1, and (2) there is at least one index i with nums[i] = a and at least one index j with nums[j] = a+1.
  Preconditions: 1 <= len(nums) <= 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val) :
    ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      (r.val = ((nums.val.length : ℕ) : ℤ) ↔
        ∃ a : ℤ,
          (∀ (i : ℕ) (h : i < nums.val.length),
              atIdx nums.val i h = a ∨ atIdx nums.val i h = a + 1) ∧
          (∃ (i : ℕ) (h : i < nums.val.length), atIdx nums.val i h = a) ∧
          (∃ (j : ℕ) (h : j < nums.val.length), atIdx nums.val j h = a + 1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val), ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      (r.val = ((nums.val.length : ℕ) : ℤ) ↔
        ∃ a : ℤ,
          (∀ (i : ℕ) (h : i < nums.val.length),
              atIdx nums.val i h = a ∨ atIdx nums.val i h = a + 1) ∧
          (∃ (i : ℕ) (h : i < nums.val.length), atIdx nums.val i h = a) ∧
          (∃ (j : ℕ) (h : j < nums.val.length), atIdx nums.val j h = a + 1))) := by
  sorry

/-- Let cnt(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. The function returns a result r. If r > 0, then there exists an integer v such that cnt(v) > 0, cnt(v+1) > 0, and r = cnt(v) + cnt(v+1).
  Preconditions: 1 <= len(nums) <= 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val) :
    ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      (0 < r.val →
        ∃ v : ℤ, 0 < cnt nums.val v ∧ 0 < cnt nums.val (v + 1) ∧
          r.val = ((cnt nums.val v + cnt nums.val (v + 1) : ℕ) : ℤ)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val), ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      (0 < r.val →
        ∃ v : ℤ, 0 < cnt nums.val v ∧ 0 < cnt nums.val (v + 1) ∧
          r.val = ((cnt nums.val v + cnt nums.val (v + 1) : ℕ) : ℤ))) := by
  sorry

/-- Let cnt(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. The function returns a result r, and for every integer v with cnt(v) > 0 and cnt(v+1) > 0, cnt(v) + cnt(v+1) <= r.
  Preconditions: 1 <= len(nums) <= 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val) :
    ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      ∀ v : ℤ, 0 < cnt nums.val v → 0 < cnt nums.val (v + 1) →
        ((cnt nums.val v + cnt nums.val (v + 1) : ℕ) : ℤ) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val), ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      ∀ v : ℤ, 0 < cnt nums.val v → 0 < cnt nums.val (v + 1) →
        ((cnt nums.val v + cnt nums.val (v + 1) : ℕ) : ℤ) ≤ r.val) := by
  sorry

/-- For any slice nums' satisfying the stated preconditions, if for every integer v the number of indices i with 0 <= i < len(nums) and nums[i] = v equals the number of indices j with 0 <= j < len(nums') and nums'[j] = v, then the function returns a result r on nums and a result r' on nums', and r = r'.
  Preconditions: 1 <= len(nums) <= 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and 1 <= len(nums') <= 20000 and for every i with 0 <= i < len(nums'), -1000000000 <= nums'[i] <= 1000000000. -/
theorem spec_8 (nums nums' : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val)
    (h1' : 1 ≤ nums'.val.length) (h2' : nums'.val.length ≤ 20000)
    (hb' : InRange nums'.val)
    (hsame : ∀ v : ℤ, cnt nums.val v = cnt nums'.val v) :
    ∃ r r' : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      Aegis.FindLhs.find_lhs nums' = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val)
    (h1' : 1 ≤ nums'.val.length) (h2' : nums'.val.length ≤ 20000)
    (hb' : InRange nums'.val)
    (hsame : ∀ v : ℤ, cnt nums.val v = cnt nums'.val v), ∃ r r' : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      Aegis.FindLhs.find_lhs nums' = ok r' ∧ r.val = r'.val) := by
  sorry

/-- Let nums' be the slice obtained by appending x to nums, so len(nums') = len(nums) + 1, nums'[i] = nums[i] for 0 <= i < len(nums), and nums'[len(nums)] = x. The function returns a result r on nums and a result r' on nums', and r' >= r.
  Preconditions: 1 <= len(nums) < 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and -1000000000 <= x <= 1000000000. -/
theorem spec_9 (nums nums' : Slice Std.I64) (x : Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length < 20000)
    (hb : InRange nums.val)
    (hxlo : -1000000000 ≤ x.val) (hxhi : x.val ≤ 1000000000)
    (hlen : nums'.val.length = nums.val.length + 1)
    (hprefix : ∀ (i : ℕ) (h : i < nums.val.length),
      atIdx nums'.val i (by omega) = atIdx nums.val i h)
    (hlast : atIdx nums'.val nums.val.length (by omega) = x.val) :
    ∃ r r' : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      Aegis.FindLhs.find_lhs nums' = ok r' ∧ r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (x : Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length < 20000)
    (hb : InRange nums.val)
    (hxlo : -1000000000 ≤ x.val) (hxhi : x.val ≤ 1000000000)
    (hlen : nums'.val.length = nums.val.length + 1)
    (hprefix : ∀ (i : ℕ) (h : i < nums.val.length),
      atIdx nums'.val i (by omega) = atIdx nums.val i h)
    (hlast : atIdx nums'.val nums.val.length (by omega) = x.val), ∃ r r' : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      Aegis.FindLhs.find_lhs nums' = ok r' ∧ r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r. If r > 0, then there exist indices 0 <= i_0 < i_1 < ... < i_{r-1} < len(nums) such that the difference between the maximum and minimum of the values nums[i_0], ..., nums[i_{r-1}] is exactly 1.
  Preconditions: 1 <= len(nums) <= 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val) :
    ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      (0 < r.val →
        ∃ sub : List Std.I64, IsSubseq sub nums.val ∧
          r.val = ((sub.length : ℕ) : ℤ) ∧
          maxVal (vals sub) - minVal (vals sub) = 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val), ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      (0 < r.val →
        ∃ sub : List Std.I64, IsSubseq sub nums.val ∧
          r.val = ((sub.length : ℕ) : ℤ) ∧
          maxVal (vals sub) - minVal (vals sub) = 1)) := by
  sorry

/-- Let cnt(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v, and let M be the maximum of cnt(v) over all integers v with cnt(v) > 0 (well-defined because len(nums) >= 1). The function returns a result r, and r <= 2 * M.
  Preconditions: 1 <= len(nums) <= 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_11 (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val) :
    ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      r.val ≤ 2 * ((maxCnt nums.val : ℕ) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val), ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      r.val ≤ 2 * ((maxCnt nums.val : ℕ) : ℤ)) := by
  sorry

/-- A harmonious subsequence of nums is a sequence nums[i_0], ..., nums[i_{k-1}] for indices 0 <= i_0 < ... < i_{k-1} < len(nums) with k >= 2 and max(nums[i_0], ..., nums[i_{k-1}]) - min(nums[i_0], ..., nums[i_{k-1}]) = 1. The function returns a result r, and for every harmonious subsequence of nums of length k, k <= r.
  Preconditions: 1 <= len(nums) <= 20000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_12 (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val) :
    ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      ∀ sub : List Std.I64, IsSubseq sub nums.val → 2 ≤ sub.length →
        maxVal (vals sub) - minVal (vals sub) = 1 →
        ((sub.length : ℕ) : ℤ) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 20000)
    (hb : InRange nums.val), ∃ r : Std.I64, Aegis.FindLhs.find_lhs nums = ok r ∧
      ∀ sub : List Std.I64, IsSubseq sub nums.val → 2 ≤ sub.length →
        maxVal (vals sub) - minVal (vals sub) = 1 →
        ((sub.length : ℕ) : ℤ) ≤ r.val) := by
  sorry

end AegisSpec.FindLhs
