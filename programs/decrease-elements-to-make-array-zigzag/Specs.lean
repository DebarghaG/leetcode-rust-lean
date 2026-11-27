import Aegis.MovesToMakeZigzag.Code.Funs

/-!
# Specifications of `Aegis.MovesToMakeZigzag.moves_to_make_zigzag`

LeetCode problem `decrease-elements-to-make-array-zigzag`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MovesToMakeZigzag

  namespace AegisSpec.MovesToMakeZigzag

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def cost (nums A : List ℤ) : ℤ :=
    (Finset.range nums.length).sum (fun i => nums[i]! - A[i]!)

  def IsZigzagE (A : List ℤ) : Prop :=
    ∀ i : ℕ, i + 1 < A.length → (Even i → A[i]! > A[i+1]!) ∧ (Odd i → A[i]! < A[i+1]!)

  def IsZigzagO (A : List ℤ) : Prop :=
    ∀ i : ℕ, i + 1 < A.length → (Even i → A[i]! < A[i+1]!) ∧ (Odd i → A[i]! > A[i+1]!)

  def IsBelow (nums A : List ℤ) : Prop :=
    A.length = nums.length ∧ ∀ i, i < nums.length → A[i]! ≤ nums[i]!

  def IsCandidateE (nums A : List ℤ) : Prop := IsBelow nums A ∧ IsZigzagE A

  def IsCandidateO (nums A : List ℤ) : Prop := IsBelow nums A ∧ IsZigzagO A

  def IsCandidate (nums A : List ℤ) : Prop := IsBelow nums A ∧ (IsZigzagE A ∨ IsZigzagO A)

  def IsMinCostE (nums : List ℤ) (c : ℤ) : Prop :=
    (∃ A : List ℤ, IsCandidateE nums A ∧ cost nums A = c) ∧
      ∀ A : List ℤ, IsCandidateE nums A → c ≤ cost nums A

  def IsMinCostO (nums : List ℤ) (c : ℤ) : Prop :=
    (∃ A : List ℤ, IsCandidateO nums A ∧ cost nums A = c) ∧
      ∀ A : List ℤ, IsCandidateO nums A → c ≤ cost nums A

  def AgreesOnEven (nums A : List ℤ) : Prop :=
    ∀ i, i < nums.length → Even i → A[i]! = nums[i]!

  def AgreesOnOdd (nums A : List ℤ) : Prop :=
    ∀ i, i < nums.length → Odd i → A[i]! = nums[i]!

  /-- The function returns a result r, and r is the minimum, over all integer arrays A with len(A) = len(nums), A[i] <= nums[i] for every 0 <= i < len(nums), and A satisfying at least one of the following two conditions (all indices are 0-based): (E) for every i with 0 <= i < len(nums)-1, if i is even then A[i] > A[i+1], while if i is odd then A[i] < A[i+1]; (O) for every i with 0 <= i < len(nums)-1, if i is even then A[i] < A[i+1], while if i is odd then A[i] > A[i+1]; of sum_{i=0}^{len(nums)-1} (nums[i] - A[i]).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000) :
      ∃ r : Std.I64, moves_to_make_zigzag nums = ok r ∧
        (∃ A : List ℤ, IsCandidate (vals nums) A ∧ cost (vals nums) A = r.val) ∧
        (∀ A : List ℤ, IsCandidate (vals nums) A → r.val ≤ cost (vals nums) A) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000), ∃ r : Std.I64, moves_to_make_zigzag nums = ok r ∧
          (∃ A : List ℤ, IsCandidate (vals nums) A ∧ cost (vals nums) A = r.val) ∧
          (∀ A : List ℤ, IsCandidate (vals nums) A → r.val ≤ cost (vals nums) A)) := by
    sorry

  /-- The function returns a result r and does not fail: it does not panic, access out of bounds, or overflow a 64-bit integer.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000) :
      ∃ r : Std.I64, moves_to_make_zigzag nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000), ∃ r : Std.I64, moves_to_make_zigzag nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000) :
      ∀ r : Std.I64, moves_to_make_zigzag nums = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000), ∀ r : Std.I64, moves_to_make_zigzag nums = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= floor(len(nums)/2) * 1000.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000) :
      ∀ r : Std.I64,
        moves_to_make_zigzag nums = ok r → r.val ≤ ((nums.val.length / 2 : ℕ) : ℤ) * 1000 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000), ∀ r : Std.I64,
          moves_to_make_zigzag nums = ok r → r.val ≤ ((nums.val.length / 2 : ℕ) : ℤ) * 1000) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if nums itself satisfies at least one of the following two conditions (all indices are 0-based): (E) for every i with 0 <= i < len(nums)-1, if i is even then nums[i] > nums[i+1], while if i is odd then nums[i] < nums[i+1]; (O) for every i with 0 <= i < len(nums)-1, if i is even then nums[i] < nums[i+1], while if i is odd then nums[i] > nums[i+1].
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000) :
      ∀ r : Std.I64,
        moves_to_make_zigzag nums = ok r →
          (r.val = 0 ↔ (IsZigzagE (vals nums) ∨ IsZigzagO (vals nums))) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000), ∀ r : Std.I64,
          moves_to_make_zigzag nums = ok r →
            (r.val = 0 ↔ (IsZigzagE (vals nums) ∨ IsZigzagO (vals nums)))) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: len(nums) = 1, and 1 <= nums[0] <= 1000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : nums.val.length = 1)
      (h0 : 1 ≤ (nums.val[0]!).val ∧ (nums.val[0]!).val ≤ 1000) :
      ∃ r : Std.I64, moves_to_make_zigzag nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length = 1)
        (h0 : 1 ≤ (nums.val[0]!).val ∧ (nums.val[0]!).val ≤ 1000), ∃ r : Std.I64, moves_to_make_zigzag nums = ok r ∧ r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if nums[0] = nums[1], and r = 0 otherwise.
    Preconditions: len(nums) = 2, and 1 <= nums[0], nums[1] <= 1000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : nums.val.length = 2)
      (h0 : 1 ≤ (nums.val[0]!).val ∧ (nums.val[0]!).val ≤ 1000)
      (h1 : 1 ≤ (nums.val[1]!).val ∧ (nums.val[1]!).val ≤ 1000) :
      ∀ r : Std.I64,
        moves_to_make_zigzag nums = ok r →
          (((nums.val[0]!).val = (nums.val[1]!).val → r.val = 1) ∧
            ((nums.val[0]!).val ≠ (nums.val[1]!).val → r.val = 0)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length = 2)
        (h0 : 1 ≤ (nums.val[0]!).val ∧ (nums.val[0]!).val ≤ 1000)
        (h1 : 1 ≤ (nums.val[1]!).val ∧ (nums.val[1]!).val ≤ 1000), ∀ r : Std.I64,
          moves_to_make_zigzag nums = ok r →
            (((nums.val[0]!).val = (nums.val[1]!).val → r.val = 1) ∧
              ((nums.val[0]!).val ≠ (nums.val[1]!).val → r.val = 0))) := by
    sorry

  /-- Whenever the function returns a result r, r = floor(len(nums)/2).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 1000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000, and there exists an integer c such that nums[i] = c for every 0 <= i < len(nums). -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000)
      (hconst : ∃ c : ℤ, ∀ i, i < nums.val.length → (nums.val[i]!).val = c) :
      ∀ r : Std.I64,
        moves_to_make_zigzag nums = ok r → r.val = ((nums.val.length / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000)
        (hconst : ∃ c : ℤ, ∀ i, i < nums.val.length → (nums.val[i]!).val = c), ∀ r : Std.I64,
          moves_to_make_zigzag nums = ok r → r.val = ((nums.val.length / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r <= C_E and r <= C_O, where C_E is the minimum, over all integer arrays A with len(A) = len(nums), A[i] <= nums[i] for every 0 <= i < len(nums), and satisfying condition (E): for every i with 0 <= i < len(nums)-1, (i even implies A[i] > A[i+1]) and (i odd implies A[i] < A[i+1]), of sum_{i=0}^{len(nums)-1} (nums[i] - A[i]); and C_O is the minimum, over all integer arrays A with len(A) = len(nums), A[i] <= nums[i] for every 0 <= i < len(nums), and satisfying condition (O): for every i with 0 <= i < len(nums)-1, (i even implies A[i] < A[i+1]) and (i odd implies A[i] > A[i+1]), of the same sum.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000) :
      ∀ r : Std.I64,
        moves_to_make_zigzag nums = ok r →
          ∃ cE cO : ℤ,
            IsMinCostE (vals nums) cE ∧ IsMinCostO (vals nums) cO ∧
              r.val ≤ cE ∧ r.val ≤ cO := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000), ∀ r : Std.I64,
          moves_to_make_zigzag nums = ok r →
            ∃ cE cO : ℤ,
              IsMinCostE (vals nums) cE ∧ IsMinCostO (vals nums) cO ∧
                r.val ≤ cE ∧ r.val ≤ cO) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer array A such that len(A) = len(nums), A[i] <= nums[i] for every 0 <= i < len(nums), A satisfies at least one of (E): for every i with 0 <= i < len(nums)-1, if i is even then A[i] > A[i+1], while if i is odd then A[i] < A[i+1]; or (O): for every i with 0 <= i < len(nums)-1, if i is even then A[i] < A[i+1], while if i is odd then A[i] > A[i+1]; and sum_{i=0}^{len(nums)-1} (nums[i] - A[i]) = r.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000) :
      ∀ r : Std.I64,
        moves_to_make_zigzag nums = ok r →
          ∃ A : List ℤ, IsCandidate (vals nums) A ∧ cost (vals nums) A = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000), ∀ r : Std.I64,
          moves_to_make_zigzag nums = ok r →
            ∃ A : List ℤ, IsCandidate (vals nums) A ∧ cost (vals nums) A = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer array A with len(A) = len(nums), A[i] <= nums[i] for every 0 <= i < len(nums), and A satisfying at least one of (E): for every i with 0 <= i < len(nums)-1, if i is even then A[i] > A[i+1], while if i is odd then A[i] < A[i+1]; or (O): for every i with 0 <= i < len(nums)-1, if i is even then A[i] < A[i+1], while if i is odd then A[i] > A[i+1]; one has sum_{i=0}^{len(nums)-1} (nums[i] - A[i]) >= r.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000) :
      ∀ r : Std.I64,
        moves_to_make_zigzag nums = ok r →
          ∀ A : List ℤ, IsCandidate (vals nums) A → r.val ≤ cost (vals nums) A := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000), ∀ r : Std.I64,
          moves_to_make_zigzag nums = ok r →
            ∀ A : List ℤ, IsCandidate (vals nums) A → r.val ≤ cost (vals nums) A) := by
    sorry

  /-- Let rev be the array with len(rev) = len(nums) and rev[i] = nums[len(nums)-1-i] for every 0 <= i < len(nums). Whenever the function returns a result r on nums, applying the function to rev also returns r.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000) :
      ∀ r : Std.I64,
        moves_to_make_zigzag nums = ok r →
          ∃ rev : Slice Std.I64, rev.val = nums.val.reverse ∧ moves_to_make_zigzag rev = ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000), ∀ r : Std.I64,
          moves_to_make_zigzag nums = ok r →
            ∃ rev : Slice Std.I64, rev.val = nums.val.reverse ∧ moves_to_make_zigzag rev = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer array A with len(A) = len(nums), A[i] <= nums[i] for every 0 <= i < len(nums), and sum_{i=0}^{len(nums)-1} (nums[i] - A[i]) = r, such that either: (1) A satisfies (E): for every i with 0 <= i < len(nums)-1, if i is even then A[i] > A[i+1], while if i is odd then A[i] < A[i+1], and A[i] = nums[i] for every even i with 0 <= i < len(nums); or (2) A satisfies (O): for every i with 0 <= i < len(nums)-1, if i is even then A[i] < A[i+1], while if i is odd then A[i] > A[i+1], and A[i] = nums[i] for every odd i with 0 <= i < len(nums).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_13 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000) :
      ∀ r : Std.I64,
        moves_to_make_zigzag nums = ok r →
          ∃ A : List ℤ,
            IsBelow (vals nums) A ∧ cost (vals nums) A = r.val ∧
              ((IsZigzagE A ∧ AgreesOnEven (vals nums) A) ∨
                (IsZigzagO A ∧ AgreesOnOdd (vals nums) A)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000), ∀ r : Std.I64,
          moves_to_make_zigzag nums = ok r →
            ∃ A : List ℤ,
              IsBelow (vals nums) A ∧ cost (vals nums) A = r.val ∧
                ((IsZigzagE A ∧ AgreesOnEven (vals nums) A) ∨
                  (IsZigzagO A ∧ AgreesOnOdd (vals nums) A))) := by
    sorry

  end AegisSpec.MovesToMakeZigzag
