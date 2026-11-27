import Aegis.DeleteAndEarn.Code.Funs

/-!
# Specifications of `Aegis.DeleteAndEarn.delete_and_earn`

LeetCode problem `delete-and-earn`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DeleteAndEarn

  open scoped BigOperators

  def count (nums : Slice Std.I64) (v : ℤ) : ℕ :=
    (nums.val.filter (fun x => x.val = v)).length

  def total (nums : Slice Std.I64) : ℤ :=
    (nums.val.map (fun x => x.val)).sum

  def sumEven (nums : Slice Std.I64) : ℤ :=
    ((nums.val.filter (fun x => Even x.val)).map (fun x => x.val)).sum

  def sumOdd (nums : Slice Std.I64) : ℤ :=
    ((nums.val.filter (fun x => Odd x.val)).map (fun x => x.val)).sum

  def weight (nums : Slice Std.I64) (S : Finset ℤ) : ℤ :=
    ∑ v ∈ S, v * (count nums v : ℤ)

  def HasSupport (nums : Slice Std.I64) (S : Finset ℤ) : Prop :=
    ∀ v ∈ S, 0 < count nums v

  def NoAdjacent (S : Finset ℤ) : Prop :=
    ∀ v : ℤ, ¬ (v ∈ S ∧ (v + 1) ∈ S)

  def Admissible (nums : Slice Std.I64) (S : Finset ℤ) : Prop :=
    HasSupport nums S ∧ NoAdjacent S

  /-- Let count(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v, and for a finite set S of integers let W(S) = sum_{v in S} v * count(v). The function returns a result r (it does not fail), and r = max { W(S) | S is a finite set of integers such that (a) for every v in S, count(v) > 0, and (b) for every integer v, not (v in S and v+1 in S) }.
    Preconditions: nums is a nonempty slice of 64-bit signed integers with 1 <= len(nums) <= 20000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. All arithmetic below is mathematical, identifying each nums[i] and the returned i64 value with its integer value. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
      (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∃ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r ∧
        (∀ S : Finset ℤ, Admissible nums S → weight nums S ≤ r.val) ∧
        (∃ S : Finset ℤ, Admissible nums S ∧ weight nums S = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
        (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r ∧
          (∀ S : Finset ℤ, Admissible nums S → weight nums S ≤ r.val) ∧
          (∃ S : Finset ℤ, Admissible nums S ∧ weight nums S = r.val)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: nums is a nonempty slice of 64-bit signed integers with 1 <= len(nums) <= 20000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
      (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∃ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
        (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_{i=0}^{len(nums)-1} nums[i].
    Preconditions: nums is a nonempty slice of 64-bit signed integers with 1 <= len(nums) <= 20000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
      (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r → r.val ≤ total nums := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
        (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r → r.val ≤ total nums) := by
    sorry

  /-- Whenever the function returns a result r, r >= max(E, O), where E = sum of nums[i] over all indices i with 0 <= i < len(nums) and nums[i] even, and O = sum of nums[i] over all indices i with 0 <= i < len(nums) and nums[i] odd.
    Preconditions: nums is a nonempty slice of 64-bit signed integers with 1 <= len(nums) <= 20000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
      (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
        max (sumEven nums) (sumOdd nums) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
        (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
          max (sumEven nums) (sumOdd nums) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a finite set S of integers such that (a) for every v in S, count(v) > 0, where count(v) is the number of indices i with 0 <= i < len(nums) and nums[i] = v; (b) for every integer v, not (v in S and v+1 in S); and (c) sum_{v in S} v * count(v) = r.
    Preconditions: nums is a nonempty slice of 64-bit signed integers with 1 <= len(nums) <= 20000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
      (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
        ∃ S : Finset ℤ, Admissible nums S ∧ weight nums S = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
        (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
          ∃ S : Finset ℤ, Admissible nums S ∧ weight nums S = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every finite set T of integers such that (a) for every v in T, count(v) > 0, where count(v) is the number of indices i with 0 <= i < len(nums) and nums[i] = v, and (b) for every integer v, not (v in T and v+1 in T), we have sum_{v in T} v * count(v) <= r.
    Preconditions: nums is a nonempty slice of 64-bit signed integers with 1 <= len(nums) <= 20000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
      (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
        ∀ T : Finset ℤ, Admissible nums T → weight nums T ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
        (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
          ∀ T : Finset ℤ, Admissible nums T → weight nums T ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = nums[0] * len(nums).
    Preconditions: nums is a nonempty slice of 64-bit signed integers with 1 <= len(nums) <= 20000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000, and for every i with 0 <= i < len(nums), nums[i] = nums[0]. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
      (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (hconst : ∀ (i : ℕ) (hi : i < nums.val.length),
        (nums.val[i]).val = (nums.val[0]).val) :
      ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
        r.val = (nums.val[0]).val * (nums.val.length : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
        (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (hconst : ∀ (i : ℕ) (hi : i < nums.val.length),
          (nums.val[i]).val = (nums.val[0]).val), ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
          r.val = (nums.val[0]).val * (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_{i=0}^{len(nums)-1} nums[i].
    Preconditions: nums is a nonempty slice of 64-bit signed integers with 1 <= len(nums) <= 20000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000, there exist indices i and j with nums[i] != nums[j], and for every integer v, not (count(v) > 0 and count(v+1) > 0), where count(v) is the number of indices i with 0 <= i < len(nums) and nums[i] = v. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
      (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (hnonconst : ∃ i j : Fin nums.val.length, (nums.val[i]).val ≠ (nums.val[j]).val)
      (hsep : ∀ v : ℤ, ¬ (0 < count nums v ∧ 0 < count nums (v + 1))) :
      ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r → r.val = total nums := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
        (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (hnonconst : ∃ i j : Fin nums.val.length, (nums.val[i]).val ≠ (nums.val[j]).val)
        (hsep : ∀ v : ℤ, ¬ (0 < count nums v ∧ 0 < count nums (v + 1))), ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r → r.val = total nums) := by
    sorry

  /-- Whenever the function returns a result r, r = max(v * count(v), (v+1) * count(v+1)).
    Preconditions: nums is a nonempty slice of 64-bit signed integers with 1 <= len(nums) <= 20000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000, and there exists an integer v such that count(v) > 0 and count(v+1) > 0, where count(w) is the number of indices i with nums[i] = w, and for every integer w not equal to v or v+1, count(w) = 0. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
      (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (htwo : ∃ v : ℤ, 0 < count nums v ∧ 0 < count nums (v + 1) ∧
        ∀ w : ℤ, w ≠ v → w ≠ v + 1 → count nums w = 0) :
      ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
        ∀ v : ℤ, 0 < count nums v → 0 < count nums (v + 1) →
          (∀ w : ℤ, w ≠ v → w ≠ v + 1 → count nums w = 0) →
          r.val = max (v * (count nums v : ℤ)) ((v + 1) * (count nums (v + 1) : ℤ)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
        (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (htwo : ∃ v : ℤ, 0 < count nums v ∧ 0 < count nums (v + 1) ∧
          ∀ w : ℤ, w ≠ v → w ≠ v + 1 → count nums w = 0), ∀ r : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
          ∀ v : ℤ, 0 < count nums v → 0 < count nums (v + 1) →
            (∀ w : ℤ, w ≠ v → w ≠ v + 1 → count nums w = 0) →
            r.val = max (v * (count nums v : ℤ)) ((v + 1) * (count nums (v + 1) : ℤ))) := by
    sorry

  /-- Whenever delete_and_earn(nums) returns a result r and delete_and_earn(nums') returns a result r', we have r = r'.
    Preconditions: nums and nums' are two nonempty slices of 64-bit signed integers, each satisfying 1 <= len <= 20000 and all elements between 1 and 10000 inclusive, and for every integer v, count_nums(v) = count_nums'(v), where count_x(v) is the number of indices i with x[i] = v. -/
  theorem spec_10 (nums nums' : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
      (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (hlen' : 1 ≤ nums'.val.length) (hlen_ub' : nums'.val.length ≤ 20000)
      (hrange' : ∀ (i : ℕ) (hi : i < nums'.val.length),
        1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10000)
      (hcount : ∀ v : ℤ, count nums v = count nums' v) :
      ∀ r r' : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
        Aegis.DeleteAndEarn.delete_and_earn nums' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
        (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (hlen' : 1 ≤ nums'.val.length) (hlen_ub' : nums'.val.length ≤ 20000)
        (hrange' : ∀ (i : ℕ) (hi : i < nums'.val.length),
          1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10000)
        (hcount : ∀ v : ℤ, count nums v = count nums' v), ∀ r r' : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
          Aegis.DeleteAndEarn.delete_and_earn nums' = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever delete_and_earn(nums) returns a result r and delete_and_earn(nums') returns a result r', we have r' >= r.
    Preconditions: nums and nums' are two nonempty slices of 64-bit signed integers, each satisfying 1 <= len <= 20000 and all elements between 1 and 10000 inclusive, for every integer v, count_{nums'}(v) >= count_nums(v), and len(nums') = len(nums) + 1, where count_x(v) is the number of indices i with x[i] = v. -/
  theorem spec_11 (nums nums' : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
      (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (hlen' : 1 ≤ nums'.val.length) (hlen_ub' : nums'.val.length ≤ 20000)
      (hrange' : ∀ (i : ℕ) (hi : i < nums'.val.length),
        1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10000)
      (hcount : ∀ v : ℤ, count nums v ≤ count nums' v)
      (hlen_eq : nums'.val.length = nums.val.length + 1) :
      ∀ r r' : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
        Aegis.DeleteAndEarn.delete_and_earn nums' = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 20000)
        (hrange : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (hlen' : 1 ≤ nums'.val.length) (hlen_ub' : nums'.val.length ≤ 20000)
        (hrange' : ∀ (i : ℕ) (hi : i < nums'.val.length),
          1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10000)
        (hcount : ∀ v : ℤ, count nums v ≤ count nums' v)
        (hlen_eq : nums'.val.length = nums.val.length + 1), ∀ r r' : Std.I64, Aegis.DeleteAndEarn.delete_and_earn nums = ok r →
          Aegis.DeleteAndEarn.delete_and_earn nums' = ok r' → r.val ≤ r'.val) := by
    sorry

  end AegisSpec.DeleteAndEarn
