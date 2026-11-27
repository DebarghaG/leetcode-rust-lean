import Aegis.PermuteUnique.Code.Funs

/-!
# Specifications of `Aegis.PermuteUnique.permute_unique`

LeetCode problem `permutations-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PermuteUnique

def countVal (v : Int) (l : List Std.I64) : Nat :=
  l.countP (fun x => decide (x.val = v))

def distinctVals (l : List Std.I64) : List Int :=
  (l.map (fun x => x.val)).dedup

def permCount (l : List Std.I64) : Nat :=
  l.length.factorial / ((distinctVals l).map (fun v => (countVal v l).factorial)).prod

def rows (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List Std.I64) :=
  r.val.map (fun row => row.val)

def totalCount (v : Int) (rs : List (List Std.I64)) : Nat :=
  (rs.map (fun row => countVal v row)).sum

def validInput (nums : Slice Std.I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 8 ∧
    ∀ (i : Nat) (hi : i < nums.val.length), -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10

/-- The function returns a result r such that: (1) for every i with 0 <= i < len(r), len(r[i]) = len(nums) and for every integer v, the number of indices k with 0 <= k < len(r[i]) and r[i][k] = v equals the number of indices k with 0 <= k < len(nums) and nums[k] = v; (2) for every i, j with 0 <= i < j < len(r), the lists r[i] and r[j] are not equal; (3) for every list p of 64-bit integers, if len(p) = len(nums) and for every integer v, the number of indices k with 0 <= k < len(p) and p[k] = v equals the number of indices k with 0 <= k < len(nums) and nums[k] = v, then there exists i with 0 <= i < len(r) and r[i] = p.
  Preconditions: 1 <= len(nums) <= 8 and for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10. -/
theorem spec_1 (nums : Slice Std.I64) (hpre : validInput nums) :
    ∃ r, Aegis.PermuteUnique.permute_unique nums = ok r ∧
      (∀ (i : Nat) (hi : i < r.val.length),
        (r.val[i]).val.length = nums.val.length ∧
          ∀ v : Int, countVal v (r.val[i]).val = countVal v nums.val) ∧
      (∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length),
        (r.val[i]).val ≠ (r.val[j]).val) ∧
      (∀ p : List Std.I64, p.length = nums.val.length →
        (∀ v : Int, countVal v p = countVal v nums.val) →
          ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]).val = p) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : validInput nums), ∃ r, Aegis.PermuteUnique.permute_unique nums = ok r ∧
      (∀ (i : Nat) (hi : i < r.val.length),
        (r.val[i]).val.length = nums.val.length ∧
          ∀ v : Int, countVal v (r.val[i]).val = countVal v nums.val) ∧
      (∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length),
        (r.val[i]).val ≠ (r.val[j]).val) ∧
      (∀ p : List Std.I64, p.length = nums.val.length →
        (∀ v : Int, countVal v p = countVal v nums.val) →
          ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]).val = p)) := by
  sorry

/-- Whenever the preconditions hold, the function returns a result r; it does not fail, overflow, panic, or access memory out of bounds.
  Preconditions: 1 <= len(nums) <= 8 and for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10. -/
theorem spec_2 (nums : Slice Std.I64) (hpre : validInput nums) :
    ∃ r, Aegis.PermuteUnique.permute_unique nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : validInput nums), ∃ r, Aegis.PermuteUnique.permute_unique nums = ok r) := by
  sorry

/-- Let n = len(nums). Let D be the set of distinct values occurring in nums, i.e., D = { v | there exists i with 0 <= i < n and nums[i] = v }. Whenever the function returns a result r, len(r) = n! / (product over v in D of count(v, nums)!), where count(v, nums) is the number of indices i with 0 <= i < n and nums[i] = v.
  Preconditions: 1 <= len(nums) <= 8 and for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10. -/
theorem spec_3 (nums : Slice Std.I64) (hpre : validInput nums) :
    ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      r.val.length = permCount nums.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : validInput nums), ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      r.val.length = permCount nums.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), len(r[i]) = len(nums).
  Preconditions: 1 <= len(nums) <= 8 and for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10. -/
theorem spec_4 (nums : Slice Std.I64) (hpre : validInput nums) :
    ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      ∀ (i : Nat) (hi : i < r.val.length), (r.val[i]).val.length = nums.val.length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : validInput nums), ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      ∀ (i : Nat) (hi : i < r.val.length), (r.val[i]).val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and every integer v, the number of indices k with 0 <= k < len(r[i]) and r[i][k] = v equals the number of indices k with 0 <= k < len(nums) and nums[k] = v.
  Preconditions: 1 <= len(nums) <= 8 and for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10. -/
theorem spec_5 (nums : Slice Std.I64) (hpre : validInput nums) :
    ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      ∀ (i : Nat) (hi : i < r.val.length) (v : Int),
        countVal v (r.val[i]).val = countVal v nums.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : validInput nums), ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      ∀ (i : Nat) (hi : i < r.val.length) (v : Int),
        countVal v (r.val[i]).val = countVal v nums.val) := by
  sorry

/-- Whenever the function returns a result r, for every i, j with 0 <= i < j < len(r), the lists r[i] and r[j] are not equal elementwise.
  Preconditions: 1 <= len(nums) <= 8 and for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10. -/
theorem spec_6 (nums : Slice Std.I64) (hpre : validInput nums) :
    ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      ∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length),
        (r.val[i]).val ≠ (r.val[j]).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : validInput nums), ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      ∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length),
        (r.val[i]).val ≠ (r.val[j]).val) := by
  sorry

/-- Whenever the function returns a result r, for every list p of 64-bit integers such that len(p) = len(nums) and for every integer v, the number of indices k with 0 <= k < len(p) and p[k] = v equals the number of indices k with 0 <= k < len(nums) and nums[k] = v, there exists an index i with 0 <= i < len(r) and r[i] = p.
  Preconditions: 1 <= len(nums) <= 8 and for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10. -/
theorem spec_7 (nums : Slice Std.I64) (hpre : validInput nums) :
    ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      ∀ p : List Std.I64, p.length = nums.val.length →
        (∀ v : Int, countVal v p = countVal v nums.val) →
          ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]).val = p := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : validInput nums), ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      ∀ p : List Std.I64, p.length = nums.val.length →
        (∀ v : Int, countVal v p = countVal v nums.val) →
          ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]).val = p) := by
  sorry

/-- If for every i, j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] = nums[j], then whenever the function returns a result r, len(r) = 1 and r[0] is a list of length len(nums) whose every element equals nums[0].
  Preconditions: 1 <= len(nums) <= 8 and for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10. -/
theorem spec_8 (nums : Slice Std.I64) (hpre : validInput nums)
    (hall : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
      nums.val[i] = nums.val[j]) :
    ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      r.val.length = 1 ∧
        ∀ w ∈ r.val, w.val.length = nums.val.length ∧ ∀ x ∈ w.val, x = nums.val[0]! := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : validInput nums)
    (hall : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
      nums.val[i] = nums.val[j]), ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      r.val.length = 1 ∧
        ∀ w ∈ r.val, w.val.length = nums.val.length ∧ ∀ x ∈ w.val, x = nums.val[0]!) := by
  sorry

/-- Whenever permute_unique(a) returns ra and permute_unique(b) returns rb, for every list p of 64-bit integers, p occurs in ra (i.e., there exists i with 0 <= i < len(ra) and ra[i] = p) if and only if p occurs in rb (i.e., there exists j with 0 <= j < len(rb) and rb[j] = p).
  Preconditions: For two slices a and b of 64-bit integers: 1 <= len(a) <= 8, 1 <= len(b) <= 8, for every i with 0 <= i < len(a), -10 <= a[i] <= 10, for every i with 0 <= i < len(b), -10 <= b[i] <= 10, len(a) = len(b), and for every integer v, the number of indices k with 0 <= k < len(a) and a[k] = v equals the number of indices k with 0 <= k < len(b) and b[k] = v. -/
theorem spec_9 (a b : Slice Std.I64) (hprea : validInput a) (hpreb : validInput b)
    (hlen : a.val.length = b.val.length)
    (hcount : ∀ v : Int, countVal v a.val = countVal v b.val) :
    ∀ ra rb, Aegis.PermuteUnique.permute_unique a = ok ra →
      Aegis.PermuteUnique.permute_unique b = ok rb →
        ∀ p : List Std.I64,
          (∃ (i : Nat) (hi : i < ra.val.length), (ra.val[i]).val = p) ↔
            (∃ (j : Nat) (hj : j < rb.val.length), (rb.val[j]).val = p) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b : Slice Std.I64) (hprea : validInput a) (hpreb : validInput b)
    (hlen : a.val.length = b.val.length)
    (hcount : ∀ v : Int, countVal v a.val = countVal v b.val), ∀ ra rb, Aegis.PermuteUnique.permute_unique a = ok ra →
      Aegis.PermuteUnique.permute_unique b = ok rb →
        ∀ p : List Std.I64,
          (∃ (i : Nat) (hi : i < ra.val.length), (ra.val[i]).val = p) ↔
            (∃ (j : Nat) (hj : j < rb.val.length), (rb.val[j]).val = p)) := by
  sorry

/-- If there exist i, j with 0 <= i < j < len(nums) and nums[i] = nums[j], then whenever the function returns a result r, len(r) < (len(nums))!.
  Preconditions: 1 <= len(nums) <= 8 and for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10. -/
theorem spec_10 (nums : Slice Std.I64) (hpre : validInput nums)
    (hrep : ∃ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      nums.val[i] = nums.val[j]) :
    ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      r.val.length < nums.val.length.factorial := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : validInput nums)
    (hrep : ∃ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      nums.val[i] = nums.val[j]), ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      r.val.length < nums.val.length.factorial) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the total number of pairs (i, k) with 0 <= i < len(r), 0 <= k < len(r[i]), and r[i][k] = v equals len(r) multiplied by the number of indices k with 0 <= k < len(nums) and nums[k] = v.
  Preconditions: 1 <= len(nums) <= 8 and for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10. -/
theorem spec_11 (nums : Slice Std.I64) (hpre : validInput nums) :
    ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      ∀ v : Int, totalCount v (rows r) = r.val.length * countVal v nums.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : validInput nums), ∀ r, Aegis.PermuteUnique.permute_unique nums = ok r →
      ∀ v : Int, totalCount v (rows r) = r.val.length * countVal v nums.val) := by
  sorry

end AegisSpec.PermuteUnique
