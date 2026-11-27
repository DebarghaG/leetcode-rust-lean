import Aegis.MaxDivScore.Code.Funs

/-!
# Specifications of `Aegis.MaxDivScore.max_div_score`

LeetCode problem `find-the-maximum-divisibility-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxDivScore

open Aegis.MaxDivScore (max_div_score)

def score (nums : Slice Std.I64) (d : Int) : Nat :=
  nums.val.countP (fun x => decide (d ∣ x.val))

def maxScore (nums divisors : Slice Std.I64) : Nat :=
  (divisors.val.map (fun d => score nums d.val)).foldr max 0

def listMin : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldr (fun y acc => min y acc) x)

def listMax : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldr (fun y acc => max y acc) x)

def divMin (divisors : Slice Std.I64) : Option Int :=
  listMin (divisors.val.map (fun d => d.val))

def divMax (divisors : Slice Std.I64) : Option Int :=
  listMax (divisors.val.map (fun d => d.val))

def dividingDivs (divisors : Slice Std.I64) (x : Int) : List Int :=
  (divisors.val.filter (fun d => decide (d.val ∣ x))).map (fun d => d.val)

/-- The function returns a result r and: (1) there exists an index i with 0 <= i < len(divisors) such that divisors[i] = r; (2) for every i with 0 <= i < len(divisors), score(divisors[i]) <= score(r); (3) for every i with 0 <= i < len(divisors), if score(divisors[i]) = score(r), then r <= divisors[i]. Here score(d) is the number of indices j with 0 <= j < len(nums) such that d divides nums[j], i.e. there exists an integer k with nums[j] = d*k.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_1 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      max_div_score nums divisors = ok r ∧
      (∃ (i : Nat) (hi : i < divisors.val.length), (divisors.val[i]).val = r.val) ∧
      (∀ i (hi : i < divisors.val.length),
        score nums (divisors.val[i]).val ≤ score nums r.val) ∧
      (∀ i (hi : i < divisors.val.length),
        score nums (divisors.val[i]).val = score nums r.val →
          r.val ≤ (divisors.val[i]).val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∃ r : Std.I64,
      max_div_score nums divisors = ok r ∧
      (∃ (i : Nat) (hi : i < divisors.val.length), (divisors.val[i]).val = r.val) ∧
      (∀ i (hi : i < divisors.val.length),
        score nums (divisors.val[i]).val ≤ score nums r.val) ∧
      (∀ i (hi : i < divisors.val.length),
        score nums (divisors.val[i]).val = score nums r.val →
          r.val ≤ (divisors.val[i]).val)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_2 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∃ r : Std.I64, max_div_score nums divisors = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∃ r : Std.I64, max_div_score nums divisors = ok r) := by
  sorry

/-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(divisors) such that divisors[i] = r.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_3 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∃ (i : Nat) (hi : i < divisors.val.length), (divisors.val[i]).val = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∃ (i : Nat) (hi : i < divisors.val.length), (divisors.val[i]).val = r.val) := by
  sorry

/-- Whenever the function returns a result r, score(r) = max{score(divisors[i]) | 0 <= i < len(divisors)}, where score(d) is the number of indices j with 0 <= j < len(nums) such that d divides nums[j].
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_4 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      score nums r.val = maxScore nums divisors := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      score nums r.val = maxScore nums divisors) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(divisors), if score(divisors[i]) = score(r), then r <= divisors[i], where score(d) is the number of indices j with 0 <= j < len(nums) such that d divides nums[j].
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_5 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∀ i (hi : i < divisors.val.length),
        score nums (divisors.val[i]).val = score nums r.val →
          r.val ≤ (divisors.val[i]).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∀ i (hi : i < divisors.val.length),
        score nums (divisors.val[i]).val = score nums r.val →
          r.val ≤ (divisors.val[i]).val) := by
  sorry

/-- Whenever the function returns a result r, if lo = min{divisors[i] | 0 <= i < len(divisors)} and hi = max{divisors[i] | 0 <= i < len(divisors)}, then lo <= r <= hi.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_6 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∀ lo hi : Int, divMin divisors = some lo → divMax divisors = some hi →
        lo ≤ r.val ∧ r.val ≤ hi := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∀ lo hi : Int, divMin divisors = some lo → divMax divisors = some hi →
        lo ≤ r.val ∧ r.val ≤ hi) := by
  sorry

/-- Whenever the function returns a result r and for every i with 0 <= i < len(divisors), score(divisors[i]) = 0, then r equals the smallest value occurring in divisors, where score(d) is the number of indices j with 0 <= j < len(nums) such that d divides nums[j].
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_7 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      (∀ i (hi : i < divisors.val.length), score nums (divisors.val[i]).val = 0) →
        divMin divisors = some r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      (∀ i (hi : i < divisors.val.length), score nums (divisors.val[i]).val = 0) →
        divMin divisors = some r.val) := by
  sorry

/-- Whenever the function returns a result r and there exists an index i with 0 <= i < len(divisors) and divisors[i] = 1, then r = 1.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_8 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      (∃ (i : Nat) (hi : i < divisors.val.length), (divisors.val[i]).val = 1) → r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      (∃ (i : Nat) (hi : i < divisors.val.length), (divisors.val[i]).val = 1) → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r and len(nums) = 1, let D be the set of values divisors[i] with 0 <= i < len(divisors) that divide nums[0]. If D is nonempty, then r = min D; if D is empty, then r = min{divisors[i] | 0 <= i < len(divisors)}.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_9 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9)
    (h_len_one : nums.val.length = 1) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      (dividingDivs divisors (nums.val[0]'(by simp [h_len_one])).val ≠ [] →
        listMin (dividingDivs divisors (nums.val[0]'(by simp [h_len_one])).val) =
          some r.val) ∧
      (dividingDivs divisors (nums.val[0]'(by simp [h_len_one])).val = [] →
        divMin divisors = some r.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9)
    (h_len_one : nums.val.length = 1), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      (dividingDivs divisors (nums.val[0]'(by simp [h_len_one])).val ≠ [] →
        listMin (dividingDivs divisors (nums.val[0]'(by simp [h_len_one])).val) =
          some r.val) ∧
      (dividingDivs divisors (nums.val[0]'(by simp [h_len_one])).val = [] →
        divMin divisors = some r.val)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(divisors), if divisors[i] divides every nums[j] for all j with 0 <= j < len(nums), then score(r) = len(nums) and r <= divisors[i], where score(d) is the number of indices j with 0 <= j < len(nums) such that d divides nums[j].
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_10 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∀ i (hi : i < divisors.val.length),
        (∀ j (hj : j < nums.val.length),
          (divisors.val[i]).val ∣ (nums.val[j]).val) →
          score nums r.val = nums.val.length ∧ r.val ≤ (divisors.val[i]).val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∀ i (hi : i < divisors.val.length),
        (∀ j (hj : j < nums.val.length),
          (divisors.val[i]).val ∣ (nums.val[j]).val) →
          score nums r.val = nums.val.length ∧ r.val ≤ (divisors.val[i]).val) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index i with 0 <= i < len(divisors) such that score(divisors[i]) > score(divisors[k]) for every k with 0 <= k < len(divisors) and divisors[k] != divisors[i], then r = divisors[i], where score(d) is the number of indices j with 0 <= j < len(nums) such that d divides nums[j].
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_11 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∀ i (hi : i < divisors.val.length),
        (∀ k (hk : k < divisors.val.length), (divisors.val[k]).val ≠ (divisors.val[i]).val →
          score nums (divisors.val[k]).val < score nums (divisors.val[i]).val) →
            r.val = (divisors.val[i]).val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∀ i (hi : i < divisors.val.length),
        (∀ k (hk : k < divisors.val.length), (divisors.val[k]).val ≠ (divisors.val[i]).val →
          score nums (divisors.val[k]).val < score nums (divisors.val[i]).val) →
            r.val = (divisors.val[i]).val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(divisors), if divisors[i] < r, then score(divisors[i]) < score(r), where score(d) is the number of indices j with 0 <= j < len(nums) such that d divides nums[j].
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_12 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∀ i (hi : i < divisors.val.length), (divisors.val[i]).val < r.val →
        score nums (divisors.val[i]).val < score nums r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      ∀ i (hi : i < divisors.val.length), (divisors.val[i]).val < r.val →
        score nums (divisors.val[i]).val < score nums r.val) := by
  sorry

/-- Whenever the function returns a result r, if there exist indices i and j with 0 <= i < len(divisors) and 0 <= j < len(nums) such that divisors[i] divides nums[j], then score(r) >= 1, where score(d) is the number of indices k with 0 <= k < len(nums) such that d divides nums[k].
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_13 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      (∃ (i : Nat) (hi : i < divisors.val.length), ∃ (j : Nat) (hj : j < nums.val.length),
        (divisors.val[i]).val ∣ (nums.val[j]).val) → 1 ≤ score nums r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      (∃ (i : Nat) (hi : i < divisors.val.length), ∃ (j : Nat) (hj : j < nums.val.length),
        (divisors.val[i]).val ∣ (nums.val[j]).val) → 1 ≤ score nums r.val) := by
  sorry

/-- Whenever the function returns a result r and len(divisors) = 1, then r = divisors[0].
  Preconditions: 1 <= len(nums) <= 1000; 1 <= len(divisors) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 10^9; for every i with 0 <= i < len(divisors), 1 <= divisors[i] <= 10^9. -/
theorem spec_14 (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9)
    (h_len_one : divisors.val.length = 1) :
    ∀ r : Std.I64, max_div_score nums divisors = ok r →
      r.val = (divisors.val[0]'(by simp [h_len_one])).val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums divisors : Slice Std.I64)
    (h_nums_len : 1 ≤ nums.val.length) (h_nums_len_ub : nums.val.length ≤ 1000)
    (h_div_len : 1 ≤ divisors.val.length) (h_div_len_ub : divisors.val.length ≤ 1000)
    (h_nums_bounds : ∀ j (hj : j < nums.val.length),
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 10 ^ 9)
    (h_div_bounds : ∀ i (hi : i < divisors.val.length),
      1 ≤ (divisors.val[i]).val ∧ (divisors.val[i]).val ≤ 10 ^ 9)
    (h_len_one : divisors.val.length = 1), ∀ r : Std.I64, max_div_score nums divisors = ok r →
      r.val = (divisors.val[0]'(by simp [h_len_one])).val) := by
  sorry

end AegisSpec.MaxDivScore
