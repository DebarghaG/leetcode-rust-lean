import Aegis.FindGcd.Code.Funs

/-!
# Specifications of `Aegis.FindGcd.find_gcd`

LeetCode problem `find-greatest-common-divisor-of-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindGcd

  def sliceVals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def listMin : List Int → Option Int
    | [] => none
    | x :: xs => some (xs.foldl (fun a b => min a b) x)

  def listMax : List Int → Option Int
    | [] => none
    | x :: xs => some (xs.foldl (fun a b => max a b) x)

  /-- Let mn = min{ nums[i] : 0 <= i < len(nums) } and mx = max{ nums[i] : 0 <= i < len(nums) }. Whenever find_gcd(nums) returns a result r, r is the greatest positive integer that divides both mn and mx; equivalently, r = gcd(mn, mx).
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_1
      (nums : Slice Std.I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (mn mx : Int)
      (hmn : listMin (sliceVals nums) = some mn)
      (hmx : listMax (sliceVals nums) = some mx) :
      ∀ r, Aegis.FindGcd.find_gcd nums = ok r → r.val = (Int.gcd mn mx : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (mn mx : Int)
        (hmn : listMin (sliceVals nums) = some mn)
        (hmx : listMax (sliceVals nums) = some mx), ∀ r, Aegis.FindGcd.find_gcd nums = ok r → r.val = (Int.gcd mn mx : Int)) := by
    sorry

  /-- find_gcd(nums) returns a result r; it does not fail, panic, or overflow.
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_2
      (nums : Slice Std.I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.FindGcd.find_gcd nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000), ∃ r : Std.I64, Aegis.FindGcd.find_gcd nums = ok r) := by
    sorry

  /-- Let mn = min{ nums[i] : 0 <= i < len(nums) }. Whenever find_gcd(nums) returns a result r, 1 <= r <= mn.
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_3
      (nums : Slice Std.I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (mn : Int)
      (hmn : listMin (sliceVals nums) = some mn) :
      ∀ r, Aegis.FindGcd.find_gcd nums = ok r → 1 ≤ r.val ∧ r.val ≤ mn := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (mn : Int)
        (hmn : listMin (sliceVals nums) = some mn), ∀ r, Aegis.FindGcd.find_gcd nums = ok r → 1 ≤ r.val ∧ r.val ≤ mn) := by
    sorry

  /-- Let mn = min{ nums[i] : 0 <= i < len(nums) }. Whenever find_gcd(nums) returns a result r, r divides mn, meaning there exists an integer k with mn = r * k.
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_4
      (nums : Slice Std.I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (mn : Int)
      (hmn : listMin (sliceVals nums) = some mn) :
      ∀ r, Aegis.FindGcd.find_gcd nums = ok r → ∃ k : Int, mn = r.val * k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (mn : Int)
        (hmn : listMin (sliceVals nums) = some mn), ∀ r, Aegis.FindGcd.find_gcd nums = ok r → ∃ k : Int, mn = r.val * k) := by
    sorry

  /-- Let mx = max{ nums[i] : 0 <= i < len(nums) }. Whenever find_gcd(nums) returns a result r, r divides mx, meaning there exists an integer k with mx = r * k.
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_5
      (nums : Slice Std.I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (mx : Int)
      (hmx : listMax (sliceVals nums) = some mx) :
      ∀ r, Aegis.FindGcd.find_gcd nums = ok r → ∃ k : Int, mx = r.val * k := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (mx : Int)
        (hmx : listMax (sliceVals nums) = some mx), ∀ r, Aegis.FindGcd.find_gcd nums = ok r → ∃ k : Int, mx = r.val * k) := by
    sorry

  /-- Let mn = min{ nums[i] : 0 <= i < len(nums) } and mx = max{ nums[i] : 0 <= i < len(nums) }. Whenever find_gcd(nums) returns a result r, for every positive integer d, if d divides mn and d divides mx, then d <= r.
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_6
      (nums : Slice Std.I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (mn mx : Int)
      (hmn : listMin (sliceVals nums) = some mn)
      (hmx : listMax (sliceVals nums) = some mx) :
      ∀ r, Aegis.FindGcd.find_gcd nums = ok r →
        ∀ d : Int, 0 < d →
          (∃ k : Int, mn = d * k) → (∃ k : Int, mx = d * k) → d ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (mn mx : Int)
        (hmn : listMin (sliceVals nums) = some mn)
        (hmx : listMax (sliceVals nums) = some mx), ∀ r, Aegis.FindGcd.find_gcd nums = ok r →
          ∀ d : Int, 0 < d →
            (∃ k : Int, mn = d * k) → (∃ k : Int, mx = d * k) → d ≤ r.val) := by
    sorry

  /-- Let mn = min{ nums[i] : 0 <= i < len(nums) }, mx = max{ nums[i] : 0 <= i < len(nums) }, mn2 = min{ nums2[i] : 0 <= i < len(nums2) }, and mx2 = max{ nums2[i] : 0 <= i < len(nums2) }. If mn = mn2 and mx = mx2, then whenever find_gcd(nums) returns r and find_gcd(nums2) returns r2, we have r = r2.
    Preconditions: Both nums and nums2 satisfy: len(nums) >= 2 and len(nums) <= 1000; len(nums2) >= 2 and len(nums2) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; and for every i with 0 <= i < len(nums2), 1 <= nums2[i] <= 1000. -/
  theorem spec_7
      (nums nums2 : Slice Std.I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
      (hlen_low2 : 2 ≤ nums2.val.length) (hlen_high2 : nums2.val.length ≤ 1000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hval2 : ∀ x ∈ nums2.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (mn mx mn2 mx2 : Int)
      (hmn : listMin (sliceVals nums) = some mn)
      (hmx : listMax (sliceVals nums) = some mx)
      (hmn2 : listMin (sliceVals nums2) = some mn2)
      (hmx2 : listMax (sliceVals nums2) = some mx2)
      (hmin_eq : mn = mn2) (hmax_eq : mx = mx2) :
      ∀ r r2, Aegis.FindGcd.find_gcd nums = ok r →
        Aegis.FindGcd.find_gcd nums2 = ok r2 → r = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
        (hlen_low2 : 2 ≤ nums2.val.length) (hlen_high2 : nums2.val.length ≤ 1000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hval2 : ∀ x ∈ nums2.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (mn mx mn2 mx2 : Int)
        (hmn : listMin (sliceVals nums) = some mn)
        (hmx : listMax (sliceVals nums) = some mx)
        (hmn2 : listMin (sliceVals nums2) = some mn2)
        (hmx2 : listMax (sliceVals nums2) = some mx2)
        (hmin_eq : mn = mn2) (hmax_eq : mx = mx2), ∀ r r2, Aegis.FindGcd.find_gcd nums = ok r →
          Aegis.FindGcd.find_gcd nums2 = ok r2 → r = r2) := by
    sorry

  /-- Whenever find_gcd(nums) returns a result r, for every positive integer d, if d divides nums[i] for every i with 0 <= i < len(nums), then d divides r.
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_8
      (nums : Slice Std.I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000) :
      ∀ r, Aegis.FindGcd.find_gcd nums = ok r →
        ∀ d : Int, 0 < d →
          (∀ x ∈ nums.val, ∃ k : Int, x.val = d * k) → ∃ k : Int, r.val = d * k := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 1000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000), ∀ r, Aegis.FindGcd.find_gcd nums = ok r →
          ∀ d : Int, 0 < d →
            (∀ x ∈ nums.val, ∃ k : Int, x.val = d * k) → ∃ k : Int, r.val = d * k) := by
    sorry

  end AegisSpec.FindGcd
