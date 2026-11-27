import Aegis.MaxValueAfterReverse.Code.Funs

/-!
# Specifications of `Aegis.MaxValueAfterReverse.max_value_after_reverse`

LeetCode problem `reverse-subarray-to-maximize-array-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxValueAfterReverse (max_value_after_reverse)

  namespace AegisSpec.MaxValueAfterReverse

  def vals (a : Slice Std.I64) : List Int := a.val.map (fun (x : Std.I64) => x.val)

  def len (a : Slice Std.I64) : Nat := (vals a).length

  def nth (a : Slice Std.I64) (i : Nat) : Int := (vals a).getD i 0

  def InBounds (a : Slice Std.I64) : Prop :=
    ∀ i, i < len a → -100000 ≤ nth a i ∧ nth a i ≤ 100000

  def adjSum : List Int → Int
    | [] => 0
    | [_] => 0
    | x :: y :: rest => |y - x| + adjSum (y :: rest)

  def valOf (a : Slice Std.I64) : Int := adjSum (vals a)

  def reverseRange (xs : List Int) (l q : Nat) : List Int :=
    xs.take l ++ ((xs.drop l).take (q + 1 - l)).reverse ++ (xs.drop l).drop (q + 1 - l)

  def revVal (a : Slice Std.I64) (l q : Nat) : Int := adjSum (reverseRange (vals a) l q)

  def listMax (xs : List Int) : Int := (xs.max?).getD 0

  def listMin (xs : List Int) : Int := (xs.min?).getD 0

  def adjPairs (xs : List Int) : List (Int × Int) := xs.zip (xs.drop 1)

  def maxLower (xs : List Int) : Int := listMax ((adjPairs xs).map (fun p => min p.1 p.2))

  def minUpper (xs : List Int) : Int := listMin ((adjPairs xs).map (fun p => max p.1 p.2))

  def gPre (xs : List Int) : Int :=
    listMax ((adjPairs xs).map (fun p => |xs.headD 0 - p.2| - |p.1 - p.2|))

  def gSuf (xs : List Int) : Int :=
    listMax ((adjPairs xs).map (fun p => |p.1 - xs.getLastD 0| - |p.1 - p.2|))

  /-- Let n = len(nums). Define val(a) for an array a of length n as the sum over i from 0 to n-2 of |a[i+1] - a[i]|. Define reverse(nums, l, q) for 0 <= l <= q < n as the array obtained from nums by reversing the contiguous subarray from index l to index q inclusive. The function returns Result.ok R where R = max { val(reverse(nums, l, q)) | 0 <= l <= q < n }.
    Preconditions: len(nums) >= 2, len(nums) <= 30000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums) :
      ∃ R, max_value_after_reverse nums = ok R ∧
        (∀ l q, l ≤ q → q < len nums → revVal nums l q ≤ R.val) ∧
        (∃ l q, l ≤ q ∧ q < len nums ∧ revVal nums l q = R.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums), ∃ R, max_value_after_reverse nums = ok R ∧
          (∀ l q, l ≤ q → q < len nums → revVal nums l q ≤ R.val) ∧
          (∃ l q, l ≤ q ∧ q < len nums ∧ revVal nums l q = R.val)) := by
    sorry

  /-- The function returns a result r (i.e., it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: len(nums) >= 2, len(nums) <= 30000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums) :
      ∃ r, max_value_after_reverse nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums), ∃ r, max_value_after_reverse nums = ok r) := by
    sorry

  /-- The returned value r satisfies r >= val(nums), where val(nums) is the original value of the array, i.e., the sum over i from 0 to len(nums)-2 of |nums[i+1] - nums[i]|.
    Preconditions: len(nums) >= 2, len(nums) <= 30000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums) :
      ∃ r, max_value_after_reverse nums = ok r ∧ valOf nums ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums), ∃ r, max_value_after_reverse nums = ok r ∧ valOf nums ≤ r.val) := by
    sorry

  /-- The returned value r satisfies r <= (len(nums) - 1) * (max(nums) - min(nums)), where max(nums) is the maximum element of nums and min(nums) is the minimum element of nums.
    Preconditions: len(nums) >= 2, len(nums) <= 30000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums) :
      ∃ r, max_value_after_reverse nums = ok r ∧
        r.val ≤ ((len nums : Int) - 1) * (listMax (vals nums) - listMin (vals nums)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums), ∃ r, max_value_after_reverse nums = ok r ∧
          r.val ≤ ((len nums : Int) - 1) * (listMax (vals nums) - listMin (vals nums))) := by
    sorry

  /-- The returned value r equals |nums[0] - nums[1]|.
    Preconditions: len(nums) = 2, and for i=0,1, -100000 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : len nums = 2) (hbnd : InBounds nums) :
      ∃ r, max_value_after_reverse nums = ok r ∧ r.val = |nth nums 0 - nth nums 1| := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : len nums = 2) (hbnd : InBounds nums), ∃ r, max_value_after_reverse nums = ok r ∧ r.val = |nth nums 0 - nth nums 1|) := by
    sorry

  /-- The returned value r equals 0 if and only if all elements of nums are equal (i.e., there exists an integer c such that nums[i] = c for all 0 <= i < len(nums)).
    Preconditions: len(nums) >= 2, len(nums) <= 30000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums) :
      ∃ r, max_value_after_reverse nums = ok r ∧
        (r.val = 0 ↔ ∃ c : Int, ∀ i, i < len nums → nth nums i = c) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums), ∃ r, max_value_after_reverse nums = ok r ∧
          (r.val = 0 ↔ ∃ c : Int, ∀ i, i < len nums → nth nums i = c)) := by
    sorry

  /-- Let n = len(nums). If the function returns Result.ok R, then for every pair of indices l, q with 0 <= l <= q < n, val(reverse(nums, l, q)) <= R, where val and reverse are defined as in spec_1.
    Preconditions: len(nums) >= 2, len(nums) <= 30000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums) :
      ∀ R, max_value_after_reverse nums = ok R →
        ∀ l q, l ≤ q → q < len nums → revVal nums l q ≤ R.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums), ∀ R, max_value_after_reverse nums = ok R →
          ∀ l q, l ≤ q → q < len nums → revVal nums l q ≤ R.val) := by
    sorry

  /-- The returned value R satisfies -2^31 <= R <= 2^31 - 1.
    Preconditions: len(nums) >= 2, len(nums) <= 30000, for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000, and the problem's answer (the maximum value over all allowed subarray reversals) fits in a signed 32-bit integer, i.e. is at most 2^31 - 1. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums)
      (hfit : ∀ l q, l ≤ q → q < len nums → revVal nums l q ≤ (2 : Int) ^ 31 - 1) :
      ∃ r, max_value_after_reverse nums = ok r ∧
        -((2 : Int) ^ 31) ≤ r.val ∧ r.val ≤ (2 : Int) ^ 31 - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums)
        (hfit : ∀ l q, l ≤ q → q < len nums → revVal nums l q ≤ (2 : Int) ^ 31 - 1), ∃ r, max_value_after_reverse nums = ok r ∧
          -((2 : Int) ^ 31) ≤ r.val ∧ r.val ≤ (2 : Int) ^ 31 - 1) := by
    sorry

  /-- The result of max_value_after_reverse(b) equals the result of max_value_after_reverse(nums).
    Preconditions: nums satisfies len(nums) >= 2, len(nums) <= 30000, and for every i, -100000 <= nums[i] <= 100000. Let c be an integer such that the array b defined by b[i] = nums[i] + c for all i with 0 <= i < len(nums) also satisfies len(b) = len(nums) and -100000 <= b[i] <= 100000 for all i. -/
  theorem spec_9 (nums b : Slice Std.I64) (c : Int)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums)
      (hlenb : len b = len nums)
      (hshift : ∀ i, i < len b → nth b i = nth nums i + c)
      (hbndb : InBounds b) :
      max_value_after_reverse b = max_value_after_reverse nums := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums b : Slice Std.I64) (c : Int)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums)
        (hlenb : len b = len nums)
        (hshift : ∀ i, i < len b → nth b i = nth nums i + c)
        (hbndb : InBounds b), max_value_after_reverse b = max_value_after_reverse nums) := by
    sorry

  /-- Let rev_nums be the array of length len(nums) with rev_nums[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). Then max_value_after_reverse(rev_nums) = max_value_after_reverse(nums).
    Preconditions: nums satisfies len(nums) >= 2, len(nums) <= 30000, and for every i, -100000 <= nums[i] <= 100000. -/
  theorem spec_10 (nums b : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums)
      (hlenb : len b = len nums)
      (hrev : ∀ i, i < len nums → nth b i = nth nums (len nums - 1 - i)) :
      max_value_after_reverse b = max_value_after_reverse nums := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums b : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums)
        (hlenb : len b = len nums)
        (hrev : ∀ i, i < len nums → nth b i = nth nums (len nums - 1 - i)), max_value_after_reverse b = max_value_after_reverse nums) := by
    sorry

  /-- Let neg_nums be the array with neg_nums[i] = -nums[i] for 0 <= i < len(nums). Then max_value_after_reverse(neg_nums) = max_value_after_reverse(nums).
    Preconditions: nums satisfies len(nums) >= 2, len(nums) <= 30000, and for every i, -100000 <= nums[i] <= 100000. -/
  theorem spec_11 (nums b : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums)
      (hlenb : len b = len nums)
      (hneg : ∀ i, i < len nums → nth b i = -nth nums i) :
      max_value_after_reverse b = max_value_after_reverse nums := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums b : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums)
        (hlenb : len b = len nums)
        (hneg : ∀ i, i < len nums → nth b i = -nth nums i), max_value_after_reverse b = max_value_after_reverse nums) := by
    sorry

  /-- The returned value r satisfies r <= val(nums) + 2 * (max(nums) - min(nums)), where val(nums) is the original value (sum of absolute adjacent differences), and max(nums), min(nums) are the maximum and minimum elements of nums.
    Preconditions: len(nums) >= 2, len(nums) <= 30000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums) :
      ∃ r, max_value_after_reverse nums = ok r ∧
        r.val ≤ valOf nums + 2 * (listMax (vals nums) - listMin (vals nums)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums), ∃ r, max_value_after_reverse nums = ok r ∧
          r.val ≤ valOf nums + 2 * (listMax (vals nums) - listMin (vals nums))) := by
    sorry

  /-- The returned value r satisfies r >= max(nums) - min(nums), where max(nums) and min(nums) are the maximum and minimum elements of nums.
    Preconditions: len(nums) >= 2, len(nums) <= 30000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_13 (nums : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums) :
      ∃ r, max_value_after_reverse nums = ok r ∧
        listMax (vals nums) - listMin (vals nums) ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums), ∃ r, max_value_after_reverse nums = ok r ∧
          listMax (vals nums) - listMin (vals nums) ≤ r.val) := by
    sorry

  /-- The result of max_value_after_reverse(b) equals c * max_value_after_reverse(nums).
    Preconditions: nums satisfies len(nums) >= 2, len(nums) <= 30000, and for every i, -100000 <= nums[i] <= 100000. Let c be a non-negative integer such that the array b defined by b[i] = c * nums[i] for all i with 0 <= i < len(nums) also satisfies -100000 <= b[i] <= 100000 for all i. -/
  theorem spec_14 (nums b : Slice Std.I64) (c : Nat)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums)
      (hlenb : len b = len nums)
      (hscale : ∀ i, i < len b → nth b i = (c : Int) * nth nums i)
      (hbndb : InBounds b) :
      ∀ R, max_value_after_reverse nums = ok R →
        ∃ Rb, max_value_after_reverse b = ok Rb ∧ Rb.val = (c : Int) * R.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums b : Slice Std.I64) (c : Nat)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums)
        (hlenb : len b = len nums)
        (hscale : ∀ i, i < len b → nth b i = (c : Int) * nth nums i)
        (hbndb : InBounds b), ∀ R, max_value_after_reverse nums = ok R →
          ∃ Rb, max_value_after_reverse b = ok Rb ∧ Rb.val = (c : Int) * R.val) := by
    sorry

  /-- The returned value r equals max( |nums[0]-nums[1]| + |nums[0]-nums[2]|, |nums[0]-nums[2]| + |nums[1]-nums[2]|, |nums[0]-nums[1]| + |nums[1]-nums[2]| ).
    Preconditions: len(nums) = 3, and for i=0,1,2, -100000 <= nums[i] <= 100000. -/
  theorem spec_15 (nums : Slice Std.I64)
      (hlen : len nums = 3) (hbnd : InBounds nums) :
      ∃ r, max_value_after_reverse nums = ok r ∧
        r.val = max (|nth nums 0 - nth nums 1| + |nth nums 0 - nth nums 2|)
                    (max (|nth nums 0 - nth nums 2| + |nth nums 1 - nth nums 2|)
                         (|nth nums 0 - nth nums 1| + |nth nums 1 - nth nums 2|)) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : len nums = 3) (hbnd : InBounds nums), ∃ r, max_value_after_reverse nums = ok r ∧
          r.val = max (|nth nums 0 - nth nums 1| + |nth nums 0 - nth nums 2|)
                      (max (|nth nums 0 - nth nums 2| + |nth nums 1 - nth nums 2|)
                           (|nth nums 0 - nth nums 1| + |nth nums 1 - nth nums 2|))) := by
    sorry

  /-- Let n = len(nums), base = sum_{i=0}^{n-2} |nums[i+1]-nums[i]|, M = max_{0 <= i <= n-2} min(nums[i], nums[i+1]), m = min_{0 <= i <= n-2} max(nums[i], nums[i+1]), g_pre = max_{0 <= i <= n-2} (|nums[0]-nums[i+1]| - |nums[i]-nums[i+1]|), and g_suf = max_{0 <= i <= n-2} (|nums[i]-nums[n-1]| - |nums[i]-nums[i+1]|). Then the returned value R equals base + max(0, 2*max(0, M-m), g_pre, g_suf).
    Preconditions: len(nums) >= 2, len(nums) <= 30000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_16 (nums : Slice Std.I64)
      (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums) :
      ∃ R, max_value_after_reverse nums = ok R ∧
        R.val = valOf nums +
          max 0 (max (2 * max 0 (maxLower (vals nums) - minUpper (vals nums)))
            (max (gPre (vals nums)) (gSuf (vals nums)))) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ len nums) (hlen' : len nums ≤ 30000) (hbnd : InBounds nums), ∃ R, max_value_after_reverse nums = ok R ∧
          R.val = valOf nums +
            max 0 (max (2 * max 0 (maxLower (vals nums) - minUpper (vals nums)))
              (max (gPre (vals nums)) (gSuf (vals nums))))) := by
    sorry

  end AegisSpec.MaxValueAfterReverse
