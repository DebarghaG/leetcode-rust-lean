import Aegis.SummaryRanges.Code.Funs

/-!
# Specifications of `Aegis.SummaryRanges.summary_ranges`

LeetCode problem `summary-ranges`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.SummaryRanges

def intsOf (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def bytesOf (s : alloc.vec.Vec Std.U8) : List Nat := s.val.map (fun b => b.val)

def OccursIn (x : Int) (l : List Int) : Prop := x ∈ l

def StrictlyIncreasing : List Int → Prop
  | [] => True
  | _ :: [] => True
  | a :: b :: t => a < b ∧ StrictlyIncreasing (b :: t)

def AllowedByte (b : Nat) : Prop :=
  b ∈ [45, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 62]

def decimalDigits (n : Nat) : List Nat := (Nat.toDigits 10 n).map (fun c => c.toNat)

def decimalRepr (x : Int) : List Nat :=
  if x < 0 then 45 :: decimalDigits x.natAbs else decimalDigits x.natAbs

def arrowBytes : List Nat := [45, 62]

def ContainsArrow (s : List Nat) : Prop := ∃ p q, s = p ++ arrowBytes ++ q

def Represents (s : List Nat) (a b : Int) : Prop :=
  (a = b ∧ s = decimalRepr a ∧ ¬ ContainsArrow s) ∨
    (a < b ∧ s = decimalRepr a ++ arrowBytes ++ decimalRepr b)

def encodeRun (p : Int × Int) : List Nat :=
  if p.1 = p.2 then decimalRepr p.1
  else decimalRepr p.1 ++ arrowBytes ++ decimalRepr p.2

def InRange (x a b : Int) : Prop := a ≤ x ∧ x ≤ b

def RangeContains (s : List Nat) (x : Int) : Prop :=
  ∃ a b, Represents s a b ∧ InRange x a b

def IsMaximalRun (l : List Int) (a b : Int) : Prop :=
  a ≤ b ∧ OccursIn a l ∧ OccursIn b l ∧
    (∀ x, InRange x a b → OccursIn x l) ∧
    (l.head? = some a ∨ ¬ OccursIn (a - 1) l) ∧
    (l.getLast? = some b ∨ ¬ OccursIn (b + 1) l)

def expandRange (a b : Int) : List Int :=
  (List.range (b - a + 1).toNat).map (fun k => a + (k : Int))

/-- Whenever the function returns a result r, r is a vector of strings of length k, where k is the number of maximal consecutive runs of nums. A maximal consecutive run is a pair (a,b) with a <= b such that a and b are elements of nums, every integer x with a <= x <= b is in nums, and either a is the first element of nums or a-1 is not in nums, and either b is the last element of nums or b+1 is not in nums. The runs are ordered by increasing a. For each i in [0, k), if (a_i,b_i) is the i-th run, then r[i] is the string representation of [a_i,b_i]: if a_i = b_i, r[i] is the standard decimal representation of a_i; otherwise r[i] is the concatenation of the standard decimal representation of a_i, the two bytes '-' and '>', and the standard decimal representation of b_i. The standard decimal representation of an integer x is the standard ASCII string: '0' for 0; for positive x, the base-10 digits without leading zeros; for negative x, a '-' followed by the standard decimal representation of -x.
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∃ runs : List (Int × Int),
        runs.length = r.val.length ∧
        runs.Nodup ∧
        (∀ p ∈ runs, IsMaximalRun (intsOf nums) p.1 p.2) ∧
        (∀ a b, IsMaximalRun (intsOf nums) a b → (a, b) ∈ runs) ∧
        runs.Pairwise (fun p q => p.1 < q.1) ∧
        (∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (p : Int × Int),
          r.val[i]? = some s → runs[i]? = some p → bytesOf s = encodeRun p) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∃ runs : List (Int × Int),
        runs.length = r.val.length ∧
        runs.Nodup ∧
        (∀ p ∈ runs, IsMaximalRun (intsOf nums) p.1 p.2) ∧
        (∀ a b, IsMaximalRun (intsOf nums) a b → (a, b) ∈ runs) ∧
        runs.Pairwise (fun p q => p.1 < q.1) ∧
        (∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (p : Int × Int),
          r.val[i]? = some s → runs[i]? = some p → bytesOf s = encodeRun p)) := by
  sorry

/-- For every nums satisfying the preconditions, the function returns a result r (i.e., it does not fail).
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∃ r, Aegis.SummaryRanges.summary_ranges nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∃ r, Aegis.SummaryRanges.summary_ranges nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= len(nums).
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r → r.val.length ≤ nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r → r.val.length ≤ nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, every string in r is non-empty.
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ s ∈ r.val, s.val ≠ [] := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ s ∈ r.val, s.val ≠ []) := by
  sorry

/-- Whenever the function returns a result r, every byte in every string in r is one of the ASCII characters '0' through '9', '-', or '>'. (That is, its numeric value is in {45, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 62}.)
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ s ∈ r.val, ∀ b ∈ s.val, AllowedByte b.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ s ∈ r.val, ∀ b ∈ s.val, AllowedByte b.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer x in nums, there is exactly one index i with 0 <= i < len(r) such that the range represented by r[i] contains x. The range represented by a string s is defined as: if s is the standard decimal representation of an integer a and does not contain the two-byte sequence '-' followed by '>', then the range is [a,a]; if s is the concatenation of the standard decimal representation of some a, the bytes '-' and '>', and the standard decimal representation of some b with a < b, then the range is [a,b].
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ x, OccursIn x (intsOf nums) →
        ∃! i : Nat, ∃ s : alloc.vec.Vec Std.U8, r.val[i]? = some s ∧ RangeContains (bytesOf s) x := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ x, OccursIn x (intsOf nums) →
        ∃! i : Nat, ∃ s : alloc.vec.Vec Std.U8, r.val[i]? = some s ∧ RangeContains (bytesOf s) x) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), if r[i] represents the range [a,b] (as defined in spec_6), then every integer x with a <= x <= b is an element of nums.
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (a b : Int),
        r.val[i]? = some s → Represents (bytesOf s) a b →
        ∀ x, InRange x a b → OccursIn x (intsOf nums) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (a b : Int),
        r.val[i]? = some s → Represents (bytesOf s) a b →
        ∀ x, InRange x a b → OccursIn x (intsOf nums)) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), if r[i] represents the range [a,b], then a-1 is not an element of nums and b+1 is not an element of nums.
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (a b : Int),
        r.val[i]? = some s → Represents (bytesOf s) a b →
        ¬ OccursIn (a - 1) (intsOf nums) ∧ ¬ OccursIn (b + 1) (intsOf nums) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (a b : Int),
        r.val[i]? = some s → Represents (bytesOf s) a b →
        ¬ OccursIn (a - 1) (intsOf nums) ∧ ¬ OccursIn (b + 1) (intsOf nums)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r)-1, if r[i] represents [a_i,b_i] and r[i+1] represents [a_{i+1},b_{i+1}], then b_i + 1 < a_{i+1}.
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ (i : Nat) (s s' : alloc.vec.Vec Std.U8) (a b a' b' : Int),
        r.val[i]? = some s → r.val[i + 1]? = some s' →
        Represents (bytesOf s) a b → Represents (bytesOf s') a' b' → b + 1 < a' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ (i : Nat) (s s' : alloc.vec.Vec Std.U8) (a b a' b' : Int),
        r.val[i]? = some s → r.val[i + 1]? = some s' →
        Represents (bytesOf s) a b → Represents (bytesOf s') a' b' → b + 1 < a') := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), if r[i] represents a range [a,a] (a single element), then r[i] is exactly the standard decimal representation of a (no leading zeros, with a leading '-' if a < 0) and does not contain the two-byte sequence '-' followed by '>'.
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (a : Int),
        r.val[i]? = some s → Represents (bytesOf s) a a →
        bytesOf s = decimalRepr a ∧ ¬ ContainsArrow (bytesOf s) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (a : Int),
        r.val[i]? = some s → Represents (bytesOf s) a a →
        bytesOf s = decimalRepr a ∧ ¬ ContainsArrow (bytesOf s)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), if r[i] represents a range [a,b] with a < b, then r[i] is the concatenation of the standard decimal representation of a, the two bytes '-' and '>', and the standard decimal representation of b.
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (a b : Int),
        r.val[i]? = some s → Represents (bytesOf s) a b → a < b →
        bytesOf s = decimalRepr a ++ arrowBytes ++ decimalRepr b := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (a b : Int),
        r.val[i]? = some s → Represents (bytesOf s) a b → a < b →
        bytesOf s = decimalRepr a ++ arrowBytes ++ decimalRepr b) := by
  sorry

/-- Whenever the function returns a result r, r is nonempty, and if r[0] represents the range [a,b] and r[len(r)-1] represents the range [c,d], then a = nums[0] and d = nums[len(nums)-1].
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]; and len(nums) > 0. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums))
    (hne : 0 < nums.val.length) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      0 < r.val.length ∧
        (∀ (s : alloc.vec.Vec Std.U8) (a b : Int),
            r.val[0]? = some s → Represents (bytesOf s) a b →
            ∀ first : Std.I64, nums.val[0]? = some first → a = first.val) ∧
        (∀ (s : alloc.vec.Vec Std.U8) (c d : Int),
            r.val[r.val.length - 1]? = some s → Represents (bytesOf s) c d →
            ∀ last : Std.I64, nums.val[nums.val.length - 1]? = some last → d = last.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums))
    (hne : 0 < nums.val.length), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      0 < r.val.length ∧
        (∀ (s : alloc.vec.Vec Std.U8) (a b : Int),
            r.val[0]? = some s → Represents (bytesOf s) a b →
            ∀ first : Std.I64, nums.val[0]? = some first → a = first.val) ∧
        (∀ (s : alloc.vec.Vec Std.U8) (c d : Int),
            r.val[r.val.length - 1]? = some s → Represents (bytesOf s) c d →
            ∀ last : Std.I64, nums.val[nums.val.length - 1]? = some last → d = last.val)) := by
  sorry

/-- Whenever the function returns a result r, if we expand each range represented by r in order (i.e., replace each string by the sequence of integers in its range, from a to b inclusive), the concatenation of these sequences is exactly nums.
  Preconditions: len(nums) <= 20; for all i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1; for all i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_13 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)) :
    ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∃ ranges : List (Int × Int),
        ranges.length = r.val.length ∧
          (∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (p : Int × Int),
              r.val[i]? = some s → ranges[i]? = some p → Represents (bytesOf s) p.1 p.2) ∧
          ranges.flatMap (fun p => expandRange p.1 p.2) = intsOf nums := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 20)
    (hrange : ∀ x ∈ nums.val, -(2 ^ 31 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
    (hsorted : StrictlyIncreasing (intsOf nums)), ∀ r, Aegis.SummaryRanges.summary_ranges nums = ok r →
      ∃ ranges : List (Int × Int),
        ranges.length = r.val.length ∧
          (∀ (i : Nat) (s : alloc.vec.Vec Std.U8) (p : Int × Int),
              r.val[i]? = some s → ranges[i]? = some p → Represents (bytesOf s) p.1 p.2) ∧
          ranges.flatMap (fun p => expandRange p.1 p.2) = intsOf nums) := by
  sorry

end AegisSpec.SummaryRanges
