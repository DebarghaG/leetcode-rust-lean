import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `maximize-score-after-pair-deletions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxScore

namespace AegisSpec.MaxScore

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def total (l : List ℤ) : ℤ := l.sum

def listMin : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldl min x

def listMax : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldl max x

def adjacentSums (l : List ℤ) : List ℤ := (l.zip (l.drop 1)).map (fun p => p.1 + p.2)

def seg (l : List ℤ) (i k : ℕ) : List ℤ := (l.drop i).take k

def keep (n : ℕ) : ℕ := if n % 2 = 1 then 1 else 2

inductive Op : Type

  | front

  | back

  | both

def Op.apply (op : Op) (l : List ℤ) : Option (List ℤ × ℤ) :=
  match l with
  | [] | [_] | [_, _] => none
  | x :: y :: z :: rest =>
      let arr := x :: y :: z :: rest
      match op with
      | Op.front => some (z :: rest, x + y)
      | Op.back =>
          match arr.reverse with
          | a :: b :: mid => some (mid.reverse, a + b)
          | _ => none
      | Op.both =>
          match arr.reverse with
          | a :: _ => some ((arr.drop 1).dropLast, x + a)
          | _ => none

def runOps : List Op → List ℤ → Option (List ℤ × ℤ)
  | [], l => some (l, 0)
  | op :: ops, l =>
      match Op.apply op l with
      | none => none
      | some (l', s) =>
          match runOps ops l' with
          | none => none
          | some (l'', s') => some (l'', s + s')

/-- The function returns a result r, and r = total - m, where total = sum_{i=0}^{n-1} nums[i], n = len(nums), and m = min_{0 <= i < n} nums[i] if n is odd, and m = min_{0 <= i < n-1} (nums[i] + nums[i+1]) if n is even. Equivalently, r is the maximum total sum of removed elements over all sequences of allowed operations (removing the first two elements, the last two elements, or the first and last element) performed until the array has at most two elements.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_1 (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : I64, max_score nums = ok r ∧
      r.val = total (vals nums) -
        (if nums.len.val % 2 = 1 then listMin (vals nums)
         else listMin (adjacentSums (vals nums))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : I64, max_score nums = ok r ∧
      r.val = total (vals nums) -
        (if nums.len.val % 2 = 1 then listMin (vals nums)
         else listMin (adjacentSums (vals nums)))) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_2 (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : I64, max_score nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : I64, max_score nums = ok r) := by
  sorry

/-- The returned result r satisfies -1000000000 <= r <= 1000000000.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_3 (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : I64, max_score nums = ok r ∧ -1000000000 ≤ r.val ∧ r.val ≤ 1000000000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : I64, max_score nums = ok r ∧ -1000000000 ≤ r.val ∧ r.val ≤ 1000000000) := by
  sorry

/-- The function returns total - min_{0 <= i < n} nums[i], where n = len(nums) and total = sum_{i=0}^{n-1} nums[i].
  Preconditions: len(nums) is odd, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_4 (nums : Slice I64)
    (h_odd : nums.len.val % 2 = 1)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : I64, max_score nums = ok r ∧
      r.val = total (vals nums) - listMin (vals nums) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (h_odd : nums.len.val % 2 = 1)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : I64, max_score nums = ok r ∧
      r.val = total (vals nums) - listMin (vals nums)) := by
  sorry

/-- The function returns total - min_{0 <= i < n-1} (nums[i] + nums[i+1]), where n = len(nums) and total = sum_{i=0}^{n-1} nums[i].
  Preconditions: len(nums) is even, 2 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_5 (nums : Slice I64)
    (h_even : nums.len.val % 2 = 0)
    (h_len : 2 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : I64, max_score nums = ok r ∧
      r.val = total (vals nums) - listMin (adjacentSums (vals nums)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (h_even : nums.len.val % 2 = 0)
    (h_len : 2 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : I64, max_score nums = ok r ∧
      r.val = total (vals nums) - listMin (adjacentSums (vals nums))) := by
  sorry

/-- There exists an index i with 0 <= i < n (if n is odd) or 0 <= i < n-1 (if n is even) and a sequence of allowed operations such that the final remaining elements are exactly nums[i..i+k-1] (where k=1 if n is odd and k=2 if n is even) and the total sum of removed elements is r, where n = len(nums).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_6 (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : I64, max_score nums = ok r ∧
      ∃ i : ℕ, i + keep nums.len.val ≤ nums.len.val ∧
        ∃ (ops : List Op) (rest : List ℤ) (s : ℤ),
          runOps ops (vals nums) = some (rest, s) ∧
            rest = seg (vals nums) i (keep nums.len.val) ∧ s = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : I64, max_score nums = ok r ∧
      ∃ i : ℕ, i + keep nums.len.val ≤ nums.len.val ∧
        ∃ (ops : List Op) (rest : List ℤ) (s : ℤ),
          runOps ops (vals nums) = some (rest, s) ∧
            rest = seg (vals nums) i (keep nums.len.val) ∧ s = r.val) := by
  sorry

/-- For every index i with 0 <= i < n (if n is odd) or 0 <= i < n-1 (if n is even) and every sequence of allowed operations that leaves exactly nums[i..i+k-1] (where k=1 if n is odd and k=2 if n is even), the total sum of removed elements is at most r, where n = len(nums).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_7 (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : I64, max_score nums = ok r ∧
      ∀ (i : ℕ), i + keep nums.len.val ≤ nums.len.val →
        ∀ (ops : List Op) (rest : List ℤ) (s : ℤ),
          runOps ops (vals nums) = some (rest, s) →
            rest = seg (vals nums) i (keep nums.len.val) → s ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : I64, max_score nums = ok r ∧
      ∀ (i : ℕ), i + keep nums.len.val ≤ nums.len.val →
        ∀ (ops : List Op) (rest : List ℤ) (s : ℤ),
          runOps ops (vals nums) = some (rest, s) →
            rest = seg (vals nums) i (keep nums.len.val) → s ≤ r.val) := by
  sorry

/-- Let nums' be the array defined by nums'[i] = nums[n-1-i] for 0 <= i < n, where n = len(nums). Then the result of max_score on nums equals the result of max_score on nums'.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_8 (nums nums' : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_rev : vals nums' = (vals nums).reverse) :
    max_score nums' = max_score nums := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_rev : vals nums' = (vals nums).reverse), max_score nums' = max_score nums) := by
  sorry

/-- Let d be an integer such that -10000 <= nums[i] + d <= 10000 for all 0 <= i < n, and let nums' be the array defined by nums'[i] = nums[i] + d. Then max_score(nums') = max_score(nums) + (n - k) * d, where n = len(nums), k = 1 if n is odd and k = 2 if n is even.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_9 (nums nums' : Slice I64) (d : ℤ)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_d : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val + d ∧ (nums.val[i]).val + d ≤ 10000)
    (h_shift : vals nums' = (vals nums).map (fun x => x + d)) :
    ∃ r r' : I64, max_score nums = ok r ∧ max_score nums' = ok r' ∧
      r'.val = r.val + ((nums.len.val - keep nums.len.val : ℕ) : ℤ) * d := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice I64) (d : ℤ)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_d : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val + d ∧ (nums.val[i]).val + d ≤ 10000)
    (h_shift : vals nums' = (vals nums).map (fun x => x + d)), ∃ r r' : I64, max_score nums = ok r ∧ max_score nums' = ok r' ∧
      r'.val = r.val + ((nums.len.val - keep nums.len.val : ℕ) : ℤ) * d) := by
  sorry

/-- The returned result r satisfies r >= total - max_{0 <= i < n} nums[i] if n is odd, and r >= total - max_{0 <= i < n-1} (nums[i] + nums[i+1]) if n is even, where n = len(nums) and total = sum_{i=0}^{n-1} nums[i].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_10 (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : I64, max_score nums = ok r ∧
      (if nums.len.val % 2 = 1 then
        total (vals nums) - listMax (vals nums) ≤ r.val
       else
        total (vals nums) - listMax (adjacentSums (vals nums)) ≤ r.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.len.val) (h_len_ub : nums.len.val ≤ 100000)
    (h_bounds : ∀ (i : ℕ) (_ : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : I64, max_score nums = ok r ∧
      (if nums.len.val % 2 = 1 then
        total (vals nums) - listMax (vals nums) ≤ r.val
       else
        total (vals nums) - listMax (adjacentSums (vals nums)) ≤ r.val)) := by
  sorry

end AegisSpec.MaxScore
