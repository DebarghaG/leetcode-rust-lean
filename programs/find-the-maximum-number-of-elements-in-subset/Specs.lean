import Aegis.MaximumLength.Code.Funs

/-!
# Specifications of `Aegis.MaximumLength.maximum_length`

LeetCode problem `find-the-maximum-number-of-elements-in-subset`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.MaximumLength

def mult (S : List ℤ) (v : ℤ) : ℕ :=
  (S.filter (fun y => y = v)).length

def freq (nums : Slice Std.I64) (v : ℤ) : ℕ :=
  (nums.val.filter (fun x => x.val = v)).length

def DrawnFrom (nums : Slice Std.I64) (S : List ℤ) : Prop :=
  ∀ v : ℤ, mult S v ≤ freq nums v

def patternList (x : ℤ) (q : ℕ) : List ℤ :=
  (List.range q).flatMap (fun j => [x ^ (2 ^ j), x ^ (2 ^ j)]) ++ [x ^ (2 ^ q)]

def PatternValid (S : List ℤ) : Prop :=
  ∃ x : ℤ, 1 ≤ x ∧ ∃ q : ℕ,
    (x = 1 ∧ S.Perm (List.replicate (2 * q + 1) 1)) ∨
    (2 ≤ x ∧ S.Perm (patternList x q))

def Chain (nums : Slice Std.I64) (x : ℤ) (q : ℕ) : Prop :=
  (∀ j : ℕ, j < q → 2 ≤ freq nums (x ^ (2 ^ j))) ∧ 1 ≤ freq nums (x ^ (2 ^ q))

/-- Write freq(v) for the number of indices i with 0 <= i < len(nums) and nums[i] = v. A multiset S drawn from nums means that for every integer v, the number of copies of v in S is at most freq(v). Say S is pattern-valid if there exist an integer x >= 1 and an integer q >= 0 such that either (i) x = 1 and S consists of exactly 2*q+1 copies of 1, or (ii) x > 1 and S consists of exactly two copies of x^(2^j) for each j with 0 <= j < q, exactly one copy of x^(2^q), and no other elements. For q = 0 this means one copy of x; the case q >= 1 matches the required pattern with k = 2^q. Then the function returns a result r, and r is the maximum of |S| over all pattern-valid multisets S drawn from nums.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r ∧
      (∀ S : List ℤ, PatternValid S → DrawnFrom nums S → (S.length : ℤ) ≤ r.val) ∧
      (∃ S : List ℤ, PatternValid S ∧ DrawnFrom nums S ∧ (S.length : ℤ) = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r ∧
      (∀ S : List ℤ, PatternValid S → DrawnFrom nums S → (S.length : ℤ) ≤ r.val) ∧
      (∃ S : List ℤ, PatternValid S ∧ DrawnFrom nums S ∧ (S.length : ℤ) = r.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or signal integer overflow or out-of-bounds access.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= len(nums).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r) :
    1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r), 1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r is odd; that is, r = 2*q+1 for some integer q >= 0.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r) :
    ∃ q : ℕ, r.val = 2 * (q : ℤ) + 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r), ∃ q : ℕ, r.val = 2 * (q : ℤ) + 1) := by
  sorry

/-- If there is an integer v such that nums[i] = v for every i with 0 <= i < len(nums), then: when v = 1, the returned value r equals len(nums) if len(nums) is odd and equals len(nums)-1 if len(nums) is even; when v > 1, r = 1.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (v : ℤ) (hv : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = v) :
    (v = 1 → ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      (nums.val.length % 2 = 1 → r.val = (nums.val.length : ℤ)) ∧
      (nums.val.length % 2 = 0 → r.val = (nums.val.length : ℤ) - 1)) ∧
    (1 < v → ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r → r.val = 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (v : ℤ) (hv : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = v), (v = 1 → ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      (nums.val.length % 2 = 1 → r.val = (nums.val.length : ℤ)) ∧
      (nums.val.length % 2 = 0 → r.val = (nums.val.length : ℤ) - 1)) ∧
    (1 < v → ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r → r.val = 1)) := by
  sorry

/-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Whenever the function returns a result r, r = 1 if and only if freq(1) < 3 and, for every integer x >= 2 with freq(x) >= 2, freq(x*x) = 0.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r) :
    (r.val = 1) ↔
      (freq nums 1 < 3 ∧
        ∀ x : ℤ, 2 ≤ x → 2 ≤ freq nums x → freq nums (x * x) = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r), (r.val = 1) ↔
      (freq nums 1 < 3 ∧
        ∀ x : ℤ, 2 ≤ x → 2 ≤ freq nums x → freq nums (x * x) = 0)) := by
  sorry

/-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v, and let c = freq(1). If c > 0, then the returned value r is at least the largest odd integer not exceeding c; explicitly, r >= c when c is odd and r >= c-1 when c is even.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r) :
    0 < freq nums 1 →
      ((freq nums 1 % 2 = 1 → (freq nums 1 : ℤ) ≤ r.val) ∧
       (freq nums 1 % 2 = 0 → (freq nums 1 : ℤ) - 1 ≤ r.val)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r), 0 < freq nums 1 →
      ((freq nums 1 % 2 = 1 → (freq nums 1 : ℤ) ≤ r.val) ∧
       (freq nums 1 % 2 = 0 → (freq nums 1 : ℤ) - 1 ≤ r.val))) := by
  sorry

/-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. For every integer x >= 2 and every integer q >= 0 such that freq(x^(2^j)) >= 2 for all integers j with 0 <= j < q and freq(x^(2^q)) >= 1, the returned value r satisfies r >= 2*q+1.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r) :
    ∀ (x : ℤ) (q : ℕ), 2 ≤ x → Chain nums x q → 2 * (q : ℤ) + 1 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r), ∀ (x : ℤ) (q : ℕ), 2 ≤ x → Chain nums x q → 2 * (q : ℤ) + 1 ≤ r.val) := by
  sorry

/-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. There exist an integer x >= 1 with freq(x) > 0 and an integer q >= 0 such that the returned value r satisfies r = 2*q+1 and either (x = 1 and freq(1) >= r), or (x >= 2, freq(x^(2^j)) >= 2 for all j with 0 <= j < q, and freq(x^(2^q)) >= 1).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r) :
    ∃ (x : ℤ) (q : ℕ), 1 ≤ x ∧ 0 < freq nums x ∧ r.val = 2 * (q : ℤ) + 1 ∧
      ((x = 1 ∧ r.val ≤ (freq nums 1 : ℤ)) ∨ (2 ≤ x ∧ Chain nums x q)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r), ∃ (x : ℤ) (q : ℕ), 1 ≤ x ∧ 0 < freq nums x ∧ r.val = 2 * (q : ℤ) + 1 ∧
      ((x = 1 ∧ r.val ≤ (freq nums 1 : ℤ)) ∨ (2 ≤ x ∧ Chain nums x q))) := by
  sorry

/-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. If freq(1) = 0, then the returned value r equals the maximum, over all integers x >= 2 with freq(x) > 0, of 2*Q(x)+1, where Q(x) is the largest integer q >= 0 such that freq(x^(2^j)) >= 2 for all j with 0 <= j < q and freq(x^(2^q)) >= 1.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r)
    (h1 : freq nums 1 = 0) :
    (∀ (x : ℤ) (q : ℕ), 2 ≤ x → 0 < freq nums x → Chain nums x q →
      2 * (q : ℤ) + 1 ≤ r.val) ∧
    (∃ (x : ℤ) (q : ℕ), 2 ≤ x ∧ 0 < freq nums x ∧ Chain nums x q ∧
      r.val = 2 * (q : ℤ) + 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r)
    (h1 : freq nums 1 = 0), (∀ (x : ℤ) (q : ℕ), 2 ≤ x → 0 < freq nums x → Chain nums x q →
      2 * (q : ℤ) + 1 ≤ r.val) ∧
    (∃ (x : ℤ) (q : ℕ), 2 ≤ x ∧ 0 < freq nums x ∧ Chain nums x q ∧
      r.val = 2 * (q : ℤ) + 1)) := by
  sorry

/-- Let r be the result returned for nums. For every slice nums' of 64-bit integers with len(nums') = len(nums) and, for every integer v, the number of indices i with nums'[i] = v equals the number of indices i with nums[i] = v, if the function returns r' on nums', then r' = r.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_11 (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen : nums'.val.length = nums.val.length)
    (hfreq : ∀ v : ℤ, freq nums' v = freq nums v)
    (r r' : Std.I64)
    (hr : Aegis.MaximumLength.maximum_length nums = ok r)
    (hr' : Aegis.MaximumLength.maximum_length nums' = ok r') :
    r' = r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen : nums'.val.length = nums.val.length)
    (hfreq : ∀ v : ℤ, freq nums' v = freq nums v)
    (r r' : Std.I64)
    (hr : Aegis.MaximumLength.maximum_length nums = ok r)
    (hr' : Aegis.MaximumLength.maximum_length nums' = ok r'), r' = r) := by
  sorry

/-- Let nums' be any slice obtained from nums by appending one extra integer v with 1 <= v <= 1000000000, and assume len(nums)+1 <= 100000. If the function returns r on nums and r' on nums', then r' >= r.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (x : Std.I64) (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 1000000000)
    (nums' : Slice Std.I64) (happend : nums'.val = nums.val ++ [x])
    (hlen : nums.val.length + 1 ≤ 100000)
    (r r' : Std.I64)
    (hr : Aegis.MaximumLength.maximum_length nums = ok r)
    (hr' : Aegis.MaximumLength.maximum_length nums' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (x : Std.I64) (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 1000000000)
    (nums' : Slice Std.I64) (happend : nums'.val = nums.val ++ [x])
    (hlen : nums.val.length + 1 ≤ 100000)
    (r r' : Std.I64)
    (hr : Aegis.MaximumLength.maximum_length nums = ok r)
    (hr' : Aegis.MaximumLength.maximum_length nums' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Whenever the function returns a result r, for every integer x >= 1 and every integer q >= 0, if either (i) x = 1 and freq(1) >= 2*q+1, or (ii) x >= 2 and freq(x^(2^j)) >= 2 for all integers j with 0 <= j < q and freq(x^(2^q)) >= 1, then 2*q+1 <= r.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_13 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r) :
    ∀ (x : ℤ) (q : ℕ), 1 ≤ x →
      ((x = 1 ∧ (freq nums 1 : ℤ) ≥ 2 * (q : ℤ) + 1) ∨ (2 ≤ x ∧ Chain nums x q)) →
      2 * (q : ℤ) + 1 ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r), ∀ (x : ℤ) (q : ℕ), 1 ≤ x →
      ((x = 1 ∧ (freq nums 1 : ℤ) ≥ 2 * (q : ℤ) + 1) ∨ (2 ≤ x ∧ Chain nums x q)) →
      2 * (q : ℤ) + 1 ≤ r.val) := by
  sorry

/-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Whenever the function returns a result r with r >= 3, either freq(1) >= 3 or there exists an integer x >= 2 such that freq(x) >= 2 and freq(x*x) >= 1.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_14 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r) (h3 : 3 ≤ r.val) :
    3 ≤ freq nums 1 ∨ ∃ x : ℤ, 2 ≤ x ∧ 2 ≤ freq nums x ∧ 1 ≤ freq nums (x * x) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.MaximumLength.maximum_length nums = ok r) (h3 : 3 ≤ r.val), 3 ≤ freq nums 1 ∨ ∃ x : ℤ, 2 ≤ x ∧ 2 ≤ freq nums x ∧ 1 ≤ freq nums (x * x)) := by
  sorry

end AegisSpec.MaximumLength
