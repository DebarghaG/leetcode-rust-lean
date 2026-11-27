import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `find-the-maximum-factor-score-of-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxScore

def i64Max : ℤ := 2 ^ 63 - 1

def gcdList (l : List ℤ) : ℕ := l.foldl (fun acc x => Nat.gcd acc x.natAbs) 0

def lcmList (l : List ℤ) : ℕ := l.foldl (fun acc x => Nat.lcm acc x.natAbs) 1

def factorScore (l : List ℤ) : ℤ :=
  if l = [] then 0 else (gcdList l : ℤ) * (lcmList l : ℤ)

def cands (l : List ℤ) : List (List ℤ) :=
  l :: (List.finRange l.length).map (fun i => l.eraseIdx (i : ℕ))

def maxFactorScore (l : List ℤ) : ℤ :=
  (cands l).foldl (fun acc B => max acc (factorScore B)) (factorScore l)

def listMax : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldl max x

def listProd (l : List ℤ) : ℤ := l.foldl (fun acc x => acc * x) 1

/-- The function returns a result r, and r = max_{B in S} factor_score(B), where S = { nums } ∪ { nums with element i removed for 0 <= i < len(nums) }, and for a non-empty array B, factor_score(B) = gcd(B) * lcm(B) with gcd(B) the greatest common divisor of the elements of B and lcm(B) the least common multiple of the elements of B; for the empty array, factor_score = 0.
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), nums[i] >= 1; and for every array B in S (defined below), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ r.val = maxFactorScore nums.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ r.val = maxFactorScore nums.val) := by
  sorry

/-- The function returns a result r, and r >= factor_score(nums), where factor_score(nums) = gcd(nums) * lcm(nums) (nums is non-empty, so this is well-defined).
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), nums[i] >= 1; and for every array B in S (defined as in spec_1), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ factorScore nums.val ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ factorScore nums.val ≤ r.val) := by
  sorry

/-- The function returns a result r, and for every i with 0 <= i < len(nums), r >= factor_score(nums without element i), where factor_score(B) = gcd(B) * lcm(B) for non-empty B, and factor_score(empty) = 0.
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), nums[i] >= 1; and for every array B in S (defined as in spec_1), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧
      ∀ i (hi : i < nums.val.length), factorScore (nums.val.eraseIdx i) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧
      ∀ i (hi : i < nums.val.length), factorScore (nums.val.eraseIdx i) ≤ r.val) := by
  sorry

/-- The function returns a result r, and there exists B in S such that r = factor_score(B), where S = { nums } ∪ { nums with element i removed for 0 <= i < len(nums) }, and factor_score is defined as gcd * lcm for non-empty B and 0 for empty B.
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), nums[i] >= 1; and for every array B in S (defined as in spec_1), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ ∃ B ∈ cands nums.val, r.val = factorScore B := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ ∃ B ∈ cands nums.val, r.val = factorScore B) := by
  sorry

/-- The function returns a result r, and r >= 1.
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), nums[i] >= 1; and for every array B in S (defined as in spec_1), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns a result r, and r = nums[0] * nums[0].
  Preconditions: len(nums) = 1; nums[0] >= 1; and for the array nums itself, lcm(nums) <= 2^63 - 1 and gcd(nums)*lcm(nums) <= 2^63 - 1 (i.e., nums[0] <= 2^63 - 1 and nums[0]*nums[0] <= 2^63 - 1). -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : nums.val.length = 1)
    (hpos : 1 ≤ (nums.val[0]'(by omega)).val)
    (hlcL : (lcmList nums.val : ℤ) ≤ i64Max)
    (hlcG : (gcdList nums.val : ℤ) * (lcmList nums.val : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧
      r.val = (nums.val[0]'(by omega)).val * (nums.val[0]'(by omega)).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 1)
    (hpos : 1 ≤ (nums.val[0]'(by omega)).val)
    (hlcL : (lcmList nums.val : ℤ) ≤ i64Max)
    (hlcG : (gcdList nums.val : ℤ) * (lcmList nums.val : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧
      r.val = (nums.val[0]'(by omega)).val * (nums.val[0]'(by omega)).val) := by
  sorry

/-- The function returns a result r, and r = max(nums[0], nums[1]) * max(nums[0], nums[1]).
  Preconditions: len(nums) = 2; nums[0] >= 1; nums[1] >= 1; and for every array B in S (defined as in spec_1), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen : nums.val.length = 2)
    (hpos0 : 1 ≤ (nums.val[0]'(by omega)).val)
    (hpos1 : 1 ≤ (nums.val[1]'(by omega)).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧
      r.val = max (nums.val[0]'(by omega)).val (nums.val[1]'(by omega)).val *
        max (nums.val[0]'(by omega)).val (nums.val[1]'(by omega)).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 2)
    (hpos0 : 1 ≤ (nums.val[0]'(by omega)).val)
    (hpos1 : 1 ≤ (nums.val[1]'(by omega)).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧
      r.val = max (nums.val[0]'(by omega)).val (nums.val[1]'(by omega)).val *
        max (nums.val[0]'(by omega)).val (nums.val[1]'(by omega)).val) := by
  sorry

/-- For any permutation π of {0, 1, ..., len(nums)-1}, let nums' be the slice defined by nums'[k] = nums[π(k)] for 0 <= k < len(nums). If the function is called on nums' and returns r', then r' = r, where r is the result on nums.
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), nums[i] >= 1; and for every array B in S (defined as in spec_1), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. The same precondition holds for any permutation of nums. -/
theorem spec_8 (nums nums' : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max)
    (hlen' : 1 ≤ nums'.val.length)
    (hpos' : ∀ i (_ : i < nums'.val.length), 1 ≤ (nums'.val[i]).val)
    (hlc' : ∀ B ∈ cands nums'.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max)
    (hperm : nums'.val.Perm nums.val) :
    ∀ r r', Aegis.MaxScore.max_score nums = ok r → Aegis.MaxScore.max_score nums' = ok r' →
      r'.val = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max)
    (hlen' : 1 ≤ nums'.val.length)
    (hpos' : ∀ i (_ : i < nums'.val.length), 1 ≤ (nums'.val[i]).val)
    (hlc' : ∀ B ∈ cands nums'.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max)
    (hperm : nums'.val.Perm nums.val), ∀ r r', Aegis.MaxScore.max_score nums = ok r → Aegis.MaxScore.max_score nums' = ok r' →
      r'.val = r.val) := by
  sorry

/-- The function returns a result r, and r = v * v.
  Preconditions: len(nums) >= 1; there exists a value v such that for all i with 0 <= i < len(nums), nums[i] = v; v >= 1; and for every array B in S (defined as in spec_1), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1 (i.e., v <= 2^63 - 1 and v*v <= 2^63 - 1). -/
theorem spec_9 (nums : Slice Std.I64) (v : ℤ)
    (hlen : 1 ≤ nums.val.length)
    (hconst : ∀ i (_ : i < nums.val.length), (nums.val[i]).val = v)
    (hv : 1 ≤ v)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ r.val = v * v := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (v : ℤ)
    (hlen : 1 ≤ nums.val.length)
    (hconst : ∀ i (_ : i < nums.val.length), (nums.val[i]).val = v)
    (hv : 1 ≤ v)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ r.val = v * v) := by
  sorry

/-- The function returns a result r, and r <= product of all elements of nums, i.e., r <= nums[0] * nums[1] * ... * nums[len(nums)-1].
  Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), nums[i] >= 1; and for every array B in S (defined as in spec_1), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ r.val ≤ listProd nums.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ r.val ≤ listProd nums.val) := by
  sorry

/-- The function returns a result r, and r >= lcm(nums), where lcm(nums) is the least common multiple of all elements of nums.
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), nums[i] >= 1; and for every array B in S (defined as in spec_1), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ (lcmList nums.val : ℤ) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ (lcmList nums.val : ℤ) ≤ r.val) := by
  sorry

/-- The function returns a result r, and r is divisible by (gcd(nums))^2, where gcd(nums) is the greatest common divisor of all elements of nums.
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), nums[i] >= 1; and for every array B in S (defined as in spec_1), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ (gcdList nums.val : ℤ) ^ 2 ∣ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧ (gcdList nums.val : ℤ) ^ 2 ∣ r.val) := by
  sorry

/-- If the function returns r on nums and r' on nums', then r' = c * c * r.
  Preconditions: nums satisfies the precondition P: len(nums) >= 1; for every i with 0 <= i < len(nums), nums[i] >= 1; and for every array B in S, if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. Let c be a positive integer. Let nums' be the slice of the same length with nums'[i] = c * nums[i] for all i. Assume nums' also satisfies the precondition P (with S' defined analogously). -/
theorem spec_13 (nums nums' : Slice Std.I64) (c : ℤ)
    (hc : 0 < c)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max)
    (hlen' : 1 ≤ nums'.val.length)
    (hpos' : ∀ i (_ : i < nums'.val.length), 1 ≤ (nums'.val[i]).val)
    (hlc' : ∀ B ∈ cands nums'.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max)
    (hlen_eq : nums'.val.length = nums.val.length)
    (hmul : ∀ i (hi : i < nums.val.length),
      (nums'.val[i]'(by omega)).val = c * (nums.val[i]).val) :
    ∀ r r', Aegis.MaxScore.max_score nums = ok r → Aegis.MaxScore.max_score nums' = ok r' →
      r'.val = c * c * r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ)
    (hc : 0 < c)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max)
    (hlen' : 1 ≤ nums'.val.length)
    (hpos' : ∀ i (_ : i < nums'.val.length), 1 ≤ (nums'.val[i]).val)
    (hlc' : ∀ B ∈ cands nums'.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max)
    (hlen_eq : nums'.val.length = nums.val.length)
    (hmul : ∀ i (hi : i < nums.val.length),
      (nums'.val[i]'(by omega)).val = c * (nums.val[i]).val), ∀ r r', Aegis.MaxScore.max_score nums = ok r → Aegis.MaxScore.max_score nums' = ok r' →
      r'.val = c * c * r.val) := by
  sorry

/-- The function returns a result r, and r <= max(nums) * lcm(nums), where max(nums) is the maximum element of nums and lcm(nums) is the least common multiple of all elements of nums.
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), nums[i] >= 1; and for every array B in S (defined as in spec_1), if B is non-empty then lcm(B) <= 2^63 - 1 and gcd(B)*lcm(B) <= 2^63 - 1. -/
theorem spec_14 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max) :
    ∃ r, Aegis.MaxScore.max_score nums = ok r ∧
      r.val ≤ listMax nums.val * (lcmList nums.val : ℤ) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length)
    (hpos : ∀ i (_ : i < nums.val.length), 1 ≤ (nums.val[i]).val)
    (hlc : ∀ B ∈ cands nums.val, B ≠ [] →
      (lcmList B : ℤ) ≤ i64Max ∧ (gcdList B : ℤ) * (lcmList B : ℤ) ≤ i64Max), ∃ r, Aegis.MaxScore.max_score nums = ok r ∧
      r.val ≤ listMax nums.val * (lcmList nums.val : ℤ)) := by
  sorry

end AegisSpec.MaxScore
