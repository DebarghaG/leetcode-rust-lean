import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-division-operations-to-make-array-non-decreasing`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinOperations

namespace AegisSpec.MinOperations

def elems (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def IsPrimeInt (n : Int) : Prop := Nat.Prime n.natAbs

def IsCompositeInt (n : Int) : Prop := 1 < n ∧ ¬ IsPrimeInt n

instance (n : Int) : Decidable (IsCompositeInt n) := by
  unfold IsCompositeInt IsPrimeInt; infer_instance

def smallestPrimeFactor (n : Int) : Int := (n.natAbs.minFac : Int)

def Nondecreasing (l : List Int) : Prop := l.Pairwise (· ≤ ·)

instance (l : List Int) : Decidable (Nondecreasing l) := by
  unfold Nondecreasing; infer_instance

def Step (b b' : List Int) : Prop :=
  ∃ (i : Nat) (x d : Int), b[i]? = some x ∧ 1 < x ∧ 0 < d ∧ d ∣ x ∧ d < x ∧
    (∀ e : Int, 0 < e → e ∣ x → e < x → e ≤ d) ∧ b' = b.set i (x / d)

def ReachesIn : Nat → List Int → List Int → Prop
  | 0, b, b' => b' = b
  | k + 1, b, b' => ∃ c, Step b c ∧ ReachesIn k c b'

def Reaches (b b' : List Int) : Prop := ∃ k, ReachesIn k b b'

def numDiff (a b : List Int) : Nat := (a.zip b).countP (fun p => decide (p.1 ≠ p.2))

def numComposite (l : List Int) : Nat := l.countP (fun x => decide (IsCompositeInt x))

/-- Let an operation on the current array be: choose an index i whose current value x satisfies x > 1, and replace x by x / d, where d is the greatest positive divisor of x with d < x. A sequence of operations is successful if after applying it the array b satisfies b[0] <= b[1] <= ... <= b[len(nums)-1]. The function returns a result r and: (a) if at least one successful sequence exists, r is the least possible number of operations in a successful sequence; (b) if no successful sequence exists, r = -1.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums = ok r ∧
      (((∃ (b : List Int) (k : Nat), ReachesIn k (elems nums) b ∧ Nondecreasing b) ∧
        (∃ (b : List Int) (k : Nat), ReachesIn k (elems nums) b ∧ Nondecreasing b ∧
          r.val = (k : Int) ∧
          ∀ (b' : List Int) (k' : Nat),
            ReachesIn k' (elems nums) b' → Nondecreasing b' → r.val ≤ (k' : Int)))
       ∨ ((¬ ∃ (b : List Int) (k : Nat), ReachesIn k (elems nums) b ∧ Nondecreasing b) ∧
          r.val = -1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∃ r : Std.I64, min_operations nums = ok r ∧
      (((∃ (b : List Int) (k : Nat), ReachesIn k (elems nums) b ∧ Nondecreasing b) ∧
        (∃ (b : List Int) (k : Nat), ReachesIn k (elems nums) b ∧ Nondecreasing b ∧
          r.val = (k : Int) ∧
          ∀ (b' : List Int) (k' : Nat),
            ReachesIn k' (elems nums) b' → Nondecreasing b' → r.val ≤ (k' : Int)))
       ∨ ((¬ ∃ (b : List Int) (k : Nat), ReachesIn k (elems nums) b ∧ Nondecreasing b) ∧
          r.val = -1))) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∃ r : Std.I64, min_operations nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∃ r : Std.I64, min_operations nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r <= len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r : Std.I64, min_operations nums = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r : Std.I64, min_operations nums = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int))) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, r <= C, where C is the number of indices i with 0 <= i < len(nums) such that nums[i] is composite (that is, nums[i] > 1 and nums[i] is not prime).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      r.val ≤ (numComposite (elems nums) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      r.val ≤ (numComposite (elems nums) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if nums[0] <= nums[1] <= ... <= nums[len(nums)-1].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r : Std.I64, min_operations nums = ok r →
      (r.val = 0 ↔ Nondecreasing (elems nums)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r : Std.I64, min_operations nums = ok r →
      (r.val = 0 ↔ Nondecreasing (elems nums))) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for every i with 0 <= i < len(nums) and nums[i] = 1, and every j with 0 <= j < i, we have nums[j] = 1.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      ∀ i : Nat, i < nums.val.length → (nums.val[i]!).val = 1 →
        ∀ j : Nat, j < i → (nums.val[j]!).val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      ∀ i : Nat, i < nums.val.length → (nums.val[i]!).val = 1 →
        ∀ j : Nat, j < i → (nums.val[j]!).val = 1) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there exists an array b of length len(nums) such that: (a) b[0] <= b[1] <= ... <= b[len(nums)-1]; (b) for every i, if nums[i] = 1 or nums[i] is prime, then b[i] = nums[i]; (c) for every i, if nums[i] is composite and p_i is the smallest prime divisor of nums[i], then either b[i] = nums[i] or b[i] = p_i; (d) the number of indices i with b[i] != nums[i] is exactly r.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      ∃ b : List Int, b.length = nums.val.length ∧ Nondecreasing b ∧
        (∀ i : Nat, i < nums.val.length →
          ((nums.val[i]!).val = 1 ∨ IsPrimeInt (nums.val[i]!).val) →
            b[i]! = (nums.val[i]!).val) ∧
        (∀ i : Nat, i < nums.val.length → IsCompositeInt (nums.val[i]!).val →
          b[i]! = (nums.val[i]!).val ∨
            b[i]! = smallestPrimeFactor (nums.val[i]!).val) ∧
        r.val = (numDiff (elems nums) b : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      ∃ b : List Int, b.length = nums.val.length ∧ Nondecreasing b ∧
        (∀ i : Nat, i < nums.val.length →
          ((nums.val[i]!).val = 1 ∨ IsPrimeInt (nums.val[i]!).val) →
            b[i]! = (nums.val[i]!).val) ∧
        (∀ i : Nat, i < nums.val.length → IsCompositeInt (nums.val[i]!).val →
          b[i]! = (nums.val[i]!).val ∨
            b[i]! = smallestPrimeFactor (nums.val[i]!).val) ∧
        r.val = (numDiff (elems nums) b : Int)) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for every array b obtainable from nums by zero or more applications of the operation 'choose an index with current value x > 1 and replace x by x / d, where d is the greatest positive divisor of x with d < x' and such that b is non-decreasing, the number of indices i with b[i] != nums[i] is at least r.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      ∀ b : List Int, Reaches (elems nums) b → Nondecreasing b →
        r.val ≤ (numDiff (elems nums) b : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      ∀ b : List Int, Reaches (elems nums) b → Nondecreasing b →
        r.val ≤ (numDiff (elems nums) b : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if there is no array b of length len(nums) satisfying: (a) b is non-decreasing; (b) for every i, either b[i] = nums[i], or (nums[i] is composite and b[i] equals the smallest prime divisor of nums[i]).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r : Std.I64, min_operations nums = ok r →
      (r.val = -1 ↔
        ¬ ∃ b : List Int, b.length = nums.val.length ∧ Nondecreasing b ∧
          ∀ i : Nat, i < nums.val.length →
            b[i]! = (nums.val[i]!).val ∨
              (IsCompositeInt (nums.val[i]!).val ∧
                b[i]! = smallestPrimeFactor (nums.val[i]!).val)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r : Std.I64, min_operations nums = ok r →
      (r.val = -1 ↔
        ¬ ∃ b : List Int, b.length = nums.val.length ∧ Nondecreasing b ∧
          ∀ i : Nat, i < nums.val.length →
            b[i]! = (nums.val[i]!).val ∨
              (IsCompositeInt (nums.val[i]!).val ∧
                b[i]! = smallestPrimeFactor (nums.val[i]!).val))) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for every array b obtainable from nums by zero or more applications of the operation 'choose an index with current value x > 1 and replace x by x / d, where d is the greatest positive divisor of x with d < x' and for every i with 0 <= i < len(nums), if nums[i] = 1 or nums[i] is prime, then b[i] = nums[i].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      ∀ b : List Int, Reaches (elems nums) b →
        ∀ i : Nat, i < nums.val.length →
          ((nums.val[i]!).val = 1 ∨ IsPrimeInt (nums.val[i]!).val) →
            b[i]! = (nums.val[i]!).val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      ∀ b : List Int, Reaches (elems nums) b →
        ∀ i : Nat, i < nums.val.length →
          ((nums.val[i]!).val = 1 ∨ IsPrimeInt (nums.val[i]!).val) →
            b[i]! = (nums.val[i]!).val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for every array b obtainable from nums by zero or more applications of the operation 'choose an index with current value x > 1 and replace x by x / d, where d is the greatest positive divisor of x with d < x' and for every i with 0 <= i < len(nums), if b[i] != nums[i], then nums[i] is composite and b[i] is the smallest prime divisor of nums[i].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      ∀ b : List Int, Reaches (elems nums) b →
        ∀ i : Nat, i < nums.val.length → b[i]! ≠ (nums.val[i]!).val →
          IsCompositeInt (nums.val[i]!).val ∧
            b[i]! = smallestPrimeFactor (nums.val[i]!).val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      ∀ b : List Int, Reaches (elems nums) b →
        ∀ i : Nat, i < nums.val.length → b[i]! ≠ (nums.val[i]!).val →
          IsCompositeInt (nums.val[i]!).val ∧
            b[i]! = smallestPrimeFactor (nums.val[i]!).val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0 and every nums[i] is either 1 or prime (equivalently, no nums[i] is composite), then r = 0.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      (∀ i : Nat, i < nums.val.length →
        (nums.val[i]!).val = 1 ∨ IsPrimeInt (nums.val[i]!).val) →
        r.val = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ i : Nat, i < nums.val.length →
      1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r : Std.I64, min_operations nums = ok r → 0 ≤ r.val →
      (∀ i : Nat, i < nums.val.length →
        (nums.val[i]!).val = 1 ∨ IsPrimeInt (nums.val[i]!).val) →
        r.val = 0) := by
  sorry

end AegisSpec.MinOperations
