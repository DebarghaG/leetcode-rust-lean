import Aegis.MinImpossibleOr.Code.Funs

/-!
# Specifications of `Aegis.MinImpossibleOr.min_impossible_or`

LeetCode problem `minimum-impossible-or`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinImpossibleOr

  def atIdx (nums : Slice Std.I64) (i : Nat) : Int := (nums.val[i]!).val

  def listOr (xs : List Int) : Int :=
    xs.foldr (fun a b => Int.ofNat (a.toNat ||| b.toNat)) 0

  def Occurs (nums : Slice Std.I64) (v : Int) : Prop :=
    ∃ i : Nat, i < nums.val.length ∧ atIdx nums i = v

  def Expressible (nums : Slice Std.I64) (x : Int) : Prop :=
    ∃ is : List Nat,
      is ≠ [] ∧ is.Pairwise (· < ·) ∧
        (∀ i ∈ is, i < nums.val.length) ∧ listOr (is.map (atIdx nums)) = x

  def ValidInput (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
      ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000

  /-- The function returns a result r, and r is the minimum positive integer not expressible from nums. Here an integer x is expressible from nums if there exist k ≥ 1 and indices 0 ≤ i1 < i2 < ... < ik < len(nums) such that (nums[i1] | nums[i2] | ... | nums[ik]) = x, where | denotes bitwise OR. Thus r ≥ 1; r is not expressible from nums; and every integer y with 1 ≤ y < r is expressible from nums. Equivalently, r is the least power of two 2^k (k ≥ 0) that does not occur as a value nums[i] for any i with 0 ≤ i < len(nums).
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
          1 ≤ r.val ∧ ¬ Expressible nums r.val ∧
            (∀ y : Int, 1 ≤ y → y < r.val → Expressible nums y) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
            1 ≤ r.val ∧ ¬ Expressible nums r.val ∧
              (∀ y : Int, 1 ≤ y → y < r.val → Expressible nums y)) := by
    sorry

  /-- The function returns a result r and 1 ≤ r ≤ 1073741824, where 1073741824 = 2^30.
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
          1 ≤ r.val ∧ r.val ≤ 1073741824 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
            1 ≤ r.val ∧ r.val ≤ 1073741824) := by
    sorry

  /-- The function returns a result r and there exists an integer k with 0 ≤ k ≤ 30 such that r = 2^k.
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
          ∃ k : Nat, k ≤ 30 ∧ r.val = (2 : Int) ^ k := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
            ∃ k : Nat, k ≤ 30 ∧ r.val = (2 : Int) ^ k) := by
    sorry

  /-- The function returns a result r and for every integer y with 1 ≤ y < r, there exist k ≥ 1 and indices 0 ≤ i1 < i2 < ... < ik < len(nums) such that (nums[i1] | nums[i2] | ... | nums[ik]) = y.
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
          (∀ y : Int, 1 ≤ y → y < r.val → Expressible nums y) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
            (∀ y : Int, 1 ≤ y → y < r.val → Expressible nums y)) := by
    sorry

  /-- The function returns a result r and there do not exist k ≥ 1 and indices 0 ≤ i1 < i2 < ... < ik < len(nums) such that (nums[i1] | nums[i2] | ... | nums[ik]) = r.
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧ ¬ Expressible nums r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧ ¬ Expressible nums r.val) := by
    sorry

  /-- The function returns a result r and for every integer k with 0 ≤ k ≤ 30 and 2^k < r, there exists an integer i with 0 ≤ i < len(nums) and nums[i] = 2^k.
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
          (∀ k : Nat, k ≤ 30 → (2 : Int) ^ k < r.val → Occurs nums ((2 : Int) ^ k)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
            (∀ k : Nat, k ≤ 30 → (2 : Int) ^ k < r.val → Occurs nums ((2 : Int) ^ k))) := by
    sorry

  /-- The function returns a result r, and r = 1 if and only if there is no integer i with 0 ≤ i < len(nums) and nums[i] = 1.
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧ (r.val = 1 ↔ ¬ Occurs nums 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧ (r.val = 1 ↔ ¬ Occurs nums 1)) := by
    sorry

  /-- The function returns a result r; if there exists an integer i with 0 ≤ i < len(nums) and nums[i] = 1, and there is no integer i with 0 ≤ i < len(nums) and nums[i] = 2, then r = 2.
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
          (Occurs nums 1 → ¬ Occurs nums 2 → r.val = 2) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
            (Occurs nums 1 → ¬ Occurs nums 2 → r.val = 2)) := by
    sorry

  /-- The function returns a result r and, for every integer k with 0 ≤ k ≤ 30, if there is no integer i with 0 ≤ i < len(nums) and nums[i] = 2^k, then r ≤ 2^k.
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
          (∀ k : Nat, k ≤ 30 → ¬ Occurs nums ((2 : Int) ^ k) → r.val ≤ (2 : Int) ^ k) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
            (∀ k : Nat, k ≤ 30 → ¬ Occurs nums ((2 : Int) ^ k) → r.val ≤ (2 : Int) ^ k)) := by
    sorry

  /-- The function returns a result r and, for every integer k with 0 ≤ k ≤ 30, if for every integer j with 0 ≤ j < k there exists an integer i with 0 ≤ i < len(nums) and nums[i] = 2^j, then r ≥ 2^k.
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
          (∀ k : Nat, k ≤ 30 → (∀ j : Nat, j < k → Occurs nums ((2 : Int) ^ j)) →
            (2 : Int) ^ k ≤ r.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
            (∀ k : Nat, k ≤ 30 → (∀ j : Nat, j < k → Occurs nums ((2 : Int) ^ j)) →
              (2 : Int) ^ k ≤ r.val)) := by
    sorry

  /-- The function returns a result r, and r = 1073741824 if and only if for every integer k with 0 ≤ k < 30 there exists an integer i with 0 ≤ i < len(nums) and nums[i] = 2^k.
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
          (r.val = 1073741824 ↔ ∀ k : Nat, k < 30 → Occurs nums ((2 : Int) ^ k)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
            (r.val = 1073741824 ↔ ∀ k : Nat, k < 30 → Occurs nums ((2 : Int) ^ k))) := by
    sorry

  /-- Let r be the result on nums and r' be the result on nums'. The function does not fail on nums or on nums'. If for every integer v, (there exists an integer i with 0 <= i < len(nums) and nums[i] = v) if and only if (there exists an integer j with 0 <= j < len(nums') and nums'[j] = v), then r = r'.
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(nums') <= 100000, for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and for every integer j with 0 <= j < len(nums'), 1 <= nums'[j] <= 1000000000. -/
  theorem spec_12 (nums nums' : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000)
      (hlen' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 100000)
      (hval' : ∀ j : Nat, j < nums'.val.length → 1 ≤ atIdx nums' j ∧ atIdx nums' j ≤ 1000000000) :
      ∃ r r' : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
          Aegis.MinImpossibleOr.min_impossible_or nums' = ok r' ∧
            ((∀ v : Int, Occurs nums v ↔ Occurs nums' v) → r.val = r'.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000)
        (hlen' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 100000)
        (hval' : ∀ j : Nat, j < nums'.val.length → 1 ≤ atIdx nums' j ∧ atIdx nums' j ≤ 1000000000), ∃ r r' : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
            Aegis.MinImpossibleOr.min_impossible_or nums' = ok r' ∧
              ((∀ v : Int, Occurs nums v ↔ Occurs nums' v) → r.val = r'.val)) := by
    sorry

  /-- Let r be the result on nums and r' be the result on nums'. The function does not fail on nums or on nums'. If for every integer v, (there exists an integer i with 0 <= i < len(nums) and nums[i] = v) implies (there exists an integer j with 0 <= j < len(nums') and nums'[j] = v), then r <= r'.
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(nums') <= 100000, for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and for every integer j with 0 <= j < len(nums'), 1 <= nums'[j] <= 1000000000. -/
  theorem spec_13 (nums nums' : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000)
      (hlen' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 100000)
      (hval' : ∀ j : Nat, j < nums'.val.length → 1 ≤ atIdx nums' j ∧ atIdx nums' j ≤ 1000000000) :
      ∃ r r' : Std.I64,
        Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
          Aegis.MinImpossibleOr.min_impossible_or nums' = ok r' ∧
            ((∀ v : Int, Occurs nums v → Occurs nums' v) → r.val ≤ r'.val) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000)
        (hlen' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 100000)
        (hval' : ∀ j : Nat, j < nums'.val.length → 1 ≤ atIdx nums' j ∧ atIdx nums' j ≤ 1000000000), ∃ r r' : Std.I64,
          Aegis.MinImpossibleOr.min_impossible_or nums = ok r ∧
            Aegis.MinImpossibleOr.min_impossible_or nums' = ok r' ∧
              ((∀ v : Int, Occurs nums v → Occurs nums' v) → r.val ≤ r'.val)) := by
    sorry

  /-- The function returns a result r (that is, it does not fail) for every input nums satisfying the preconditions.
    Preconditions: 1 ≤ len(nums) ≤ 100000 and for every integer i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 1000000000. -/
  theorem spec_14 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000) :
      ∃ r : Std.I64, Aegis.MinImpossibleOr.min_impossible_or nums = ok r := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 1000000000), ∃ r : Std.I64, Aegis.MinImpossibleOr.min_impossible_or nums = ok r) := by
    sorry

  end AegisSpec.MinImpossibleOr
