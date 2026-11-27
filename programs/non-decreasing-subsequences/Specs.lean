import Aegis.FindSubsequences.Code.Funs

/-!
# Specifications of `Aegis.FindSubsequences.find_subsequences`

LeetCode problem `non-decreasing-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindSubsequences

open Aegis.FindSubsequences (find_subsequences)

def ValidInput (nums : Slice I64) : Prop :=
  (1 ≤ nums.val.length ∧ nums.val.length ≤ 15) ∧
    (∀ (i : Nat) (hi : i < nums.val.length),
      -100 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)

def Nondecreasing (s : List I64) : Prop :=
  ∀ (k : Nat) (h : k + 1 < s.length),
    (s.get ⟨k, Nat.lt_of_succ_lt h⟩).val ≤ (s.get ⟨k + 1, h⟩).val

def IsSubseq (s : List I64) (nums : List I64) : Prop :=
  ∃ idx : (Fin s.length → Fin nums.length),
    (∀ a b : Fin s.length, a < b → idx a < idx b) ∧
      (∀ t : Fin s.length, (nums.get (idx t)).val = (s.get t).val)

def IsQualified (s : List I64) (nums : List I64) : Prop :=
  2 ≤ s.length ∧ Nondecreasing s ∧ IsSubseq s nums

/-- Whenever the function returns a result r, r is exactly the list of all distinct sequences s of 64-bit signed integers such that: (a) 2 <= len(s); (b) s is non-decreasing, meaning s[k] <= s[k+1] for every k with 0 <= k < len(s)-1; and (c) s is a subsequence of nums, meaning there exist indices j_0, ..., j_{len(s)-1} with 0 <= j_0 < ... < j_{len(s)-1} < len(nums) and nums[j_t] = s[t] for every t with 0 <= t < len(s). The phrase exactly means: every entry r[q] satisfies (a)-(c); every sequence s satisfying (a)-(c) equals some entry r[q] (same length and same values at each index); and no two entries of r are equal as sequences. The order of the entries of r is arbitrary and unconstrained.
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_1 (nums : Slice I64) (hpre : ValidInput nums) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        (∀ (q : Nat) (hq : q < r.val.length),
            IsQualified (r.val.get ⟨q, hq⟩).val nums.val) ∧
        (∀ s : List I64, IsQualified s nums.val →
            ∃ (q : Nat) (hq : q < r.val.length),
              (r.val.get ⟨q, hq⟩).val = s) ∧
        (∀ (a b : Nat) (ha : a < r.val.length) (hb : b < r.val.length),
            (r.val.get ⟨a, ha⟩).val = (r.val.get ⟨b, hb⟩).val → a = b) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        (∀ (q : Nat) (hq : q < r.val.length),
            IsQualified (r.val.get ⟨q, hq⟩).val nums.val) ∧
        (∀ s : List I64, IsQualified s nums.val →
            ∃ (q : Nat) (hq : q < r.val.length),
              (r.val.get ⟨q, hq⟩).val = s) ∧
        (∀ (a b : Nat) (ha : a < r.val.length) (hb : b < r.val.length),
            (r.val.get ⟨a, ha⟩).val = (r.val.get ⟨b, hb⟩).val → a = b)) := by
  sorry

/-- The function returns a result r for every nums satisfying the preconditions; in other words, it does not fail on these bounded inputs.
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_2 (nums : Slice I64) (hpre : ValidInput nums) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64), find_subsequences nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64), find_subsequences nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every q with 0 <= q < len(r), the sequence r[q] has length at least 2.
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_3 (nums : Slice I64) (hpre : ValidInput nums) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ (q : Nat) (hq : q < r.val.length),
          2 ≤ (r.val.get ⟨q, hq⟩).val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ (q : Nat) (hq : q < r.val.length),
          2 ≤ (r.val.get ⟨q, hq⟩).val.length) := by
  sorry

/-- Whenever the function returns a result r, for every q with 0 <= q < len(r), len(r[q]) <= len(nums).
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_4 (nums : Slice I64) (hpre : ValidInput nums) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ (q : Nat) (hq : q < r.val.length),
          (r.val.get ⟨q, hq⟩).val.length ≤ nums.val.length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ (q : Nat) (hq : q < r.val.length),
          (r.val.get ⟨q, hq⟩).val.length ≤ nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every q with 0 <= q < len(r) and every k with 0 <= k < len(r[q])-1, r[q][k] <= r[q][k+1].
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice I64) (hpre : ValidInput nums) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ (q : Nat) (hq : q < r.val.length),
          Nondecreasing (r.val.get ⟨q, hq⟩).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ (q : Nat) (hq : q < r.val.length),
          Nondecreasing (r.val.get ⟨q, hq⟩).val) := by
  sorry

/-- Whenever the function returns a result r, for every q with 0 <= q < len(r), letting m = len(r[q]), there exist integers j_0, ..., j_{m-1} such that 0 <= j_0 < ... < j_{m-1} < len(nums) and nums[j_t] = r[q][t] for every t with 0 <= t < m.
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice I64) (hpre : ValidInput nums) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ (q : Nat) (hq : q < r.val.length),
          IsSubseq (r.val.get ⟨q, hq⟩).val nums.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ (q : Nat) (hq : q < r.val.length),
          IsSubseq (r.val.get ⟨q, hq⟩).val nums.val) := by
  sorry

/-- Whenever the function returns a result r, for all a and b with 0 <= a < len(r) and 0 <= b < len(r), if len(r[a]) = len(r[b]) and r[a][k] = r[b][k] for every k with 0 <= k < len(r[a]), then a = b.
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_7 (nums : Slice I64) (hpre : ValidInput nums) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ (a b : Nat) (ha : a < r.val.length) (hb : b < r.val.length),
          (r.val.get ⟨a, ha⟩).val = (r.val.get ⟨b, hb⟩).val → a = b := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ (a b : Nat) (ha : a < r.val.length) (hb : b < r.val.length),
          (r.val.get ⟨a, ha⟩).val = (r.val.get ⟨b, hb⟩).val → a = b) := by
  sorry

/-- Whenever the function returns a result r, for every sequence s of 64-bit signed integers such that 2 <= len(s) <= len(nums), s is non-decreasing (s[k] <= s[k+1] for all 0 <= k < len(s)-1), and s is a subsequence of nums (there exist indices j_0 < ... < j_{len(s)-1} with nums[j_t] = s[t] for all t), there exists q with 0 <= q < len(r) such that len(r[q]) = len(s) and r[q][k] = s[k] for every k with 0 <= k < len(s).
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_8 (nums : Slice I64) (hpre : ValidInput nums) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ s : List I64,
          2 ≤ s.length → s.length ≤ nums.val.length → Nondecreasing s →
            IsSubseq s nums.val →
              ∃ (q : Nat) (hq : q < r.val.length),
                (r.val.get ⟨q, hq⟩).val = s := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        ∀ s : List I64,
          2 ≤ s.length → s.length ≤ nums.val.length → Nondecreasing s →
            IsSubseq s nums.val →
              ∃ (q : Nat) (hq : q < r.val.length),
                (r.val.get ⟨q, hq⟩).val = s) := by
  sorry

/-- Whenever the function returns a result r, len(r) is equal to the number of distinct sequences s of 64-bit signed integers with 2 <= len(s), s non-decreasing, and s a subsequence of nums (as defined by strictly increasing matching indices).
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_9 (nums : Slice I64) (hpre : ValidInput nums) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        r.val.length = Nat.card { s : List I64 // IsQualified s nums.val } := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        r.val.length = Nat.card { s : List I64 // IsQualified s nums.val }) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 0 if and only if there do not exist indices i and j with 0 <= i < j < len(nums) and nums[i] <= nums[j].
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_10 (nums : Slice I64) (hpre : ValidInput nums) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        (r.val.length = 0 ↔
          ¬ ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
              i < j ∧ (nums.val.get ⟨i, hi⟩).val ≤ (nums.val.get ⟨j, hj⟩).val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        (r.val.length = 0 ↔
          ¬ ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
              i < j ∧ (nums.val.get ⟨i, hi⟩).val ≤ (nums.val.get ⟨j, hj⟩).val)) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= 2^(len(nums)) - len(nums) - 1.
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_11 (nums : Slice I64) (hpre : ValidInput nums) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        r.val.length ≤ 2 ^ nums.val.length - nums.val.length - 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        r.val.length ≤ 2 ^ nums.val.length - nums.val.length - 1) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) >= 2 and nums is non-decreasing (nums[i] <= nums[i+1] for every i with 0 <= i < len(nums)-1), then there exists q with 0 <= q < len(r) such that len(r[q]) = len(nums) and r[q][i] = nums[i] for every i with 0 <= i < len(nums).
  Preconditions: len(nums) is between 1 and 15 inclusive, and -100 <= nums[i] <= 100 for every integer i with 0 <= i < len(nums). -/
theorem spec_12 (nums : Slice I64) (hpre : ValidInput nums) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        2 ≤ nums.val.length → Nondecreasing nums.val →
          ∃ (q : Nat) (hq : q < r.val.length),
            (r.val.get ⟨q, hq⟩).val = nums.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (hpre : ValidInput nums), ∀ (r : alloc.vec.Vec (alloc.vec.Vec I64)),
      find_subsequences nums = ok r →
        2 ≤ nums.val.length → Nondecreasing nums.val →
          ∃ (q : Nat) (hq : q < r.val.length),
            (r.val.get ⟨q, hq⟩).val = nums.val) := by
  sorry

end AegisSpec.FindSubsequences
