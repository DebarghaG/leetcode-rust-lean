import Aegis.ReplaceNonCoprimes.Code.Funs

/-!
# Specifications of `Aegis.ReplaceNonCoprimes.replace_non_coprimes`

LeetCode problem `replace-non-coprime-numbers-in-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ReplaceNonCoprimes

  abbrev Arr : Type := List Std.I64

  def entry (l : Arr) (i : Nat) : Int :=
    match l[i]? with
    | some x => x.val
    | none => 0

  def vals (l : Arr) : List Int := l.map (fun x => x.val)

  def lcmList : List Int → Int
    | [] => 1
    | x :: xs => (Int.lcm x (lcmList xs) : Int)

  def Stable (l : Arr) : Prop :=
    ∀ i, i + 1 < l.length → Int.gcd (entry l i) (entry l (i + 1)) = 1

  def Step (a b : Arr) : Prop :=
    ∃ (l u : Arr) (x y z : Std.I64),
      a = l ++ x :: y :: u ∧
        1 < Int.gcd x.val y.val ∧
          z.val = (Int.lcm x.val y.val : Int) ∧ b = l ++ z :: u

  def Reachable (a b : Arr) : Prop := Relation.ReflTransGen Step a b

  def FinalValueBound (nums : Slice Std.I64) : Prop :=
    ∀ s : Arr, Reachable nums.val s → Stable s → ∀ i, i < s.length → entry s i ≤ 100000000

  /-- Whenever the function returns a result r, r is exactly the unique stable array reachable from nums by zero or more legal replacements. Equivalently: (1) r is reachable from nums by zero or more legal replacements; (2) for every i with 0 <= i < len(r)-1, gcd(r[i], r[i+1]) = 1; and (3) for every array s of i64 values that is reachable from nums by zero or more legal replacements and satisfies gcd(s[i], s[i+1]) = 1 for every 0 <= i < len(s)-1, we have len(s) = len(r) and s[i] = r[i] for every 0 <= i < len(r).
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent entries x,y with gcd(x,y) > 1 by their least common multiple; an array is stable if no adjacent pair has gcd greater than 1. -/
  theorem spec_1 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_final : FinalValueBound nums)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      Reachable nums.val r.val ∧ Stable r.val ∧
        (∀ s : Arr, Reachable nums.val s → Stable s →
          s.length = r.val.length ∧
            ∀ i, i < r.val.length → entry s i = entry r.val i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_final : FinalValueBound nums)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), Reachable nums.val r.val ∧ Stable r.val ∧
          (∀ s : Arr, Reachable nums.val s → Stable s →
            s.length = r.val.length ∧
              ∀ i, i < r.val.length → entry s i = entry r.val i)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, go out of bounds, or report arithmetic overflow) for every input satisfying the preconditions. This specification asserts nothing else about r.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent entries x,y with gcd(x,y) > 1 by their least common multiple. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_final : FinalValueBound nums) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_final : FinalValueBound nums), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= len(r) <= len(nums).
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent x,y with gcd(x,y) > 1 by their least common multiple. -/
  theorem spec_3 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_final : FinalValueBound nums)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      1 ≤ r.val.length ∧ r.val.length ≤ nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_final : FinalValueBound nums)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), 1 ≤ r.val.length ∧ r.val.length ≤ nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] >= 1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent x,y with gcd(x,y) > 1 by their least common multiple. -/
  theorem spec_4 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_final : FinalValueBound nums)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      ∀ i, i < r.val.length → 1 ≤ entry r.val i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_final : FinalValueBound nums)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), ∀ i, i < r.val.length → 1 ≤ entry r.val i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r)-1, gcd(r[i], r[i+1]) = 1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent x,y with gcd(x,y) > 1 by their least common multiple. -/
  theorem spec_5 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_final : FinalValueBound nums)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      ∀ i, i + 1 < r.val.length → Int.gcd (entry r.val i) (entry r.val (i + 1)) = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_final : FinalValueBound nums)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), ∀ i, i + 1 < r.val.length → Int.gcd (entry r.val i) (entry r.val (i + 1)) = 1) := by
    sorry

  /-- Whenever the function returns a result r, there exist an integer m >= 0 and arrays A_0, ..., A_m of i64 values such that A_0 = nums, A_m = r, and for every t with 0 <= t < m, A_{t+1} is obtained from A_t by choosing an index i with 0 <= i < len(A_t)-1 and gcd(A_t[i], A_t[i+1]) > 1, deleting A_t[i] and A_t[i+1], and inserting their least common multiple at that position.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent x,y with gcd(x,y) > 1 by their least common multiple. -/
  theorem spec_6 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_final : FinalValueBound nums)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      ∃ (m : Nat) (A : Nat → Arr),
        A 0 = nums.val ∧ A m = r.val ∧ ∀ t, t < m → Step (A t) (A (t + 1)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_final : FinalValueBound nums)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), ∃ (m : Nat) (A : Nat → Arr),
          A 0 = nums.val ∧ A m = r.val ∧ ∀ t, t < m → Step (A t) (A (t + 1))) := by
    sorry

  /-- Whenever the function returns a result r, for every array s of i64 values that is reachable from nums by zero or more legal replacements and satisfies gcd(s[i], s[i+1]) = 1 for every 0 <= i < len(s)-1, we have len(s) = len(r) and s[i] = r[i] for every 0 <= i < len(r).
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent x,y with gcd(x,y) > 1 by their least common multiple. -/
  theorem spec_7 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_final : FinalValueBound nums)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      ∀ s : Arr, Reachable nums.val s → Stable s →
        s.length = r.val.length ∧
          ∀ i, i < r.val.length → entry s i = entry r.val i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_final : FinalValueBound nums)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), ∀ s : Arr, Reachable nums.val s → Stable s →
          s.length = r.val.length ∧
            ∀ i, i < r.val.length → entry s i = entry r.val i) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = n and r[i] = nums[i] for every 0 <= i < n.
    Preconditions: Let n = len(nums). Assume n >= 2, 1 <= nums[i] <= 100000 for every 0 <= i < n, and for every i with 0 <= i < n-1, gcd(nums[i], nums[i+1]) = 1. The final-value bound is automatic because the final array is nums itself. -/
  theorem spec_8 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len : 2 ≤ nums.val.length)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_stable : ∀ i, i + 1 < nums.val.length →
        Int.gcd (entry nums.val i) (entry nums.val (i + 1)) = 1)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      r.val.length = nums.val.length ∧
        ∀ i, i < nums.val.length → entry r.val i = entry nums.val i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len : 2 ≤ nums.val.length)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_stable : ∀ i, i + 1 < nums.val.length →
          Int.gcd (entry nums.val i) (entry nums.val (i + 1)) = 1)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), r.val.length = nums.val.length ∧
          ∀ i, i < nums.val.length → entry r.val i = entry nums.val i) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 1 and r[0] = nums[0].
    Preconditions: Assume len(nums) = 1 and 1 <= nums[0] <= 100000. The final-value bound is automatic because the final array is [nums[0]]. -/
  theorem spec_9 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len : nums.val.length = 1)
      (h_range : 1 ≤ entry nums.val 0 ∧ entry nums.val 0 ≤ 100000)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      r.val.length = 1 ∧ entry r.val 0 = entry nums.val 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len : nums.val.length = 1)
        (h_range : 1 ≤ entry nums.val 0 ∧ entry nums.val 0 ≤ 100000)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), r.val.length = 1 ∧ entry r.val 0 = entry nums.val 0) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 1 and r[0] is the least common multiple of all entries nums[0], ..., nums[n-1].
    Preconditions: Let n = len(nums). Assume n >= 2, 1 <= nums[i] <= 100000 for every 0 <= i < n, there exists an integer p > 1 such that p divides nums[i] for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent x,y with gcd(x,y) > 1 by their least common multiple. -/
  theorem spec_10 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len : 2 ≤ nums.val.length)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_common : ∃ p : Int, 1 < p ∧ ∀ i, i < nums.val.length → p ∣ entry nums.val i)
      (h_final : FinalValueBound nums)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      r.val.length = 1 ∧ entry r.val 0 = lcmList (vals nums.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len : 2 ≤ nums.val.length)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_common : ∃ p : Int, 1 < p ∧ ∀ i, i < nums.val.length → p ∣ entry nums.val i)
        (h_final : FinalValueBound nums)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), r.val.length = 1 ∧ entry r.val 0 = lcmList (vals nums.val)) := by
    sorry

  /-- Whenever the function returns a result r, let m = len(r). There exist indices 0 = b_0 < b_1 < ... < b_m = len(nums) such that for every k with 0 <= k < m, r[k] is the least common multiple of the nonempty contiguous block nums[b_k], nums[b_k+1], ..., nums[b_{k+1}-1].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent x,y with gcd(x,y) > 1 by their least common multiple. -/
  theorem spec_11 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_final : FinalValueBound nums)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      ∃ b : Nat → Nat,
        b 0 = 0 ∧ b r.val.length = nums.val.length ∧
          (∀ k, k < r.val.length → b k < b (k + 1)) ∧
            (∀ k, k < r.val.length →
              entry r.val k =
                lcmList (vals ((nums.val.drop (b k)).take (b (k + 1) - b k)))) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_final : FinalValueBound nums)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), ∃ b : Nat → Nat,
          b 0 = 0 ∧ b r.val.length = nums.val.length ∧
            (∀ k, k < r.val.length → b k < b (k + 1)) ∧
              (∀ k, k < r.val.length →
                entry r.val k =
                  lcmList (vals ((nums.val.drop (b k)).take (b (k + 1) - b k))))) := by
    sorry

  /-- Whenever the function returns a result r, let L_in be the least common multiple of all entries nums[0], ..., nums[len(nums)-1], and let L_out be the least common multiple of all entries r[0], ..., r[len(r)-1] (the lcm of a finite nonempty sequence is the least positive integer divisible by every entry). Then L_out = L_in.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent x,y with gcd(x,y) > 1 by their least common multiple. -/
  theorem spec_12 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_final : FinalValueBound nums)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      lcmList (vals r.val) = lcmList (vals nums.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_final : FinalValueBound nums)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), lcmList (vals r.val) = lcmList (vals nums.val)) := by
    sorry

  /-- Whenever the function returns a result r, the number of indices i with 0 <= i < len(r) and r[i] = 1 equals the number of indices j with 0 <= j < len(nums) and nums[j] = 1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent x,y with gcd(x,y) > 1 by their least common multiple. -/
  theorem spec_13 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_final : FinalValueBound nums)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      (vals r.val).countP (fun x => decide (x = 1)) =
        (vals nums.val).countP (fun x => decide (x = 1)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_final : FinalValueBound nums)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), (vals r.val).countP (fun x => decide (x = 1)) =
          (vals nums.val).countP (fun x => decide (x = 1))) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] <= 100000000.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and the problem's final-value guarantee holds: every stable array reachable from nums by legal replacements has all entries at most 100000000. A legal replacement replaces adjacent entries x,y with gcd(x,y) > 1 by their least common multiple. -/
  theorem spec_14 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
      (h_range : ∀ i, i < nums.val.length →
        1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
      (h_final : FinalValueBound nums)
      (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r) :
      ∀ i, i < r.val.length → entry r.val i ≤ 100000000 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len1 : 1 ≤ nums.val.length) (h_len2 : nums.val.length ≤ 100000)
        (h_range : ∀ i, i < nums.val.length →
          1 ≤ entry nums.val i ∧ entry nums.val i ≤ 100000)
        (h_final : FinalValueBound nums)
        (hr : Aegis.ReplaceNonCoprimes.replace_non_coprimes nums = ok r), ∀ i, i < r.val.length → entry r.val i ≤ 100000000) := by
    sorry

end AegisSpec.ReplaceNonCoprimes
