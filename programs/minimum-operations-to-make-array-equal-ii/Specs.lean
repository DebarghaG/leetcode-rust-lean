import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-array-equal-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperations

def nums (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

def diffAt (a b : List Int) (i : Nat) : Int := b.getD i 0 - a.getD i 0

def AllEq (a b : List Int) : Prop := ∀ i : Nat, i < a.length → a.getD i 0 = b.getD i 0

def AllDivisible (k : Int) (a b : List Int) : Prop :=
  ∀ i : Nat, i < a.length → k ∣ diffAt a b i

def posSum (k : Int) (a b : List Int) : Int :=
  ((List.range a.length).map (fun i => (max (diffAt a b i) 0) / k)).sum

def negSum (k : Int) (a b : List Int) : Int :=
  ((List.range a.length).map (fun i => (max (diffAt b a i) 0) / k)).sum

def Feasible (k : Int) (a b : List Int) : Prop :=
  AllDivisible k a b ∧ a.sum = b.sum

def step (k : Int) (a b : List Int) : Prop :=
  ∃ i j : Nat,
    i < a.length ∧ j < a.length ∧ i ≠ j ∧
      b = (a.set i (a.getD i 0 - k)).set j (a.getD j 0 + k)

def Reach (k : Int) (a : List Int) : Nat → List Int → Prop
  | 0, b => a = b
  | m + 1, b => ∃ c, Reach k a m c ∧ step k c b

/-- Whenever the function returns a result r, the following holds. If k = 0, then r = 0 exactly when nums1[i] = nums2[i] for every i with 0 ≤ i < n, and r = -1 otherwise. If k > 0, define P = Σ over i with nums2[i] > nums1[i] of (nums2[i] - nums1[i]) / k and N = Σ over i with nums1[i] > nums2[i] of (nums1[i] - nums2[i]) / k, using exact integer division in the successful case. Then r = P if (for every i with 0 ≤ i < n, nums2[i] - nums1[i] is divisible by k) and (Σ_{i=0}^{n-1} nums1[i] = Σ_{i=0}^{n-1} nums2[i]); otherwise r = -1. In the successful case P = N.
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_1 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
      ((k.val = 0 →
          (r.val = 0 ↔ AllEq (nums nums1) (nums nums2)) ∧
          (¬ AllEq (nums nums1) (nums nums2) → r.val = -1)) ∧
        (0 < k.val →
          ((Feasible k.val (nums nums1) (nums nums2) →
              r.val = posSum k.val (nums nums1) (nums nums2) ∧
              posSum k.val (nums nums1) (nums nums2) =
                negSum k.val (nums nums1) (nums nums2)) ∧
            (¬ Feasible k.val (nums nums1) (nums nums2) → r.val = -1)))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
      ((k.val = 0 →
          (r.val = 0 ↔ AllEq (nums nums1) (nums nums2)) ∧
          (¬ AllEq (nums nums1) (nums nums2) → r.val = -1)) ∧
        (0 < k.val →
          ((Feasible k.val (nums nums1) (nums nums2) →
              r.val = posSum k.val (nums nums1) (nums nums2) ∧
              posSum k.val (nums nums1) (nums nums2) =
                negSum k.val (nums nums1) (nums nums2)) ∧
            (¬ Feasible k.val (nums nums1) (nums nums2) → r.val = -1))))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow the 64-bit integer range.
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_2 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    ∃ r : Std.I64, Aegis.MinOperations.min_operations nums1 nums2 k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums1 nums2 k = ok r) := by
  sorry

/-- If k > 0, then the function returns a nonnegative result r if and only if both of the following hold: (1) for every i with 0 ≤ i < n, nums2[i] - nums1[i] is divisible by k; (2) Σ_{i=0}^{n-1} nums1[i] = Σ_{i=0}^{n-1} nums2[i]. When either condition fails, it returns -1.
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_3 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    0 < k.val →
      ((∃ r : Std.I64,
            Aegis.MinOperations.min_operations nums1 nums2 k = ok r ∧ 0 ≤ r.val) ↔
          Feasible k.val (nums nums1) (nums nums2)) ∧
        (¬ Feasible k.val (nums nums1) (nums nums2) →
          ∃ r : Std.I64,
            Aegis.MinOperations.min_operations nums1 nums2 k = ok r ∧ r.val = -1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), 0 < k.val →
      ((∃ r : Std.I64,
            Aegis.MinOperations.min_operations nums1 nums2 k = ok r ∧ 0 ≤ r.val) ↔
          Feasible k.val (nums nums1) (nums nums2)) ∧
        (¬ Feasible k.val (nums nums1) (nums nums2) →
          ∃ r : Std.I64,
            Aegis.MinOperations.min_operations nums1 nums2 k = ok r ∧ r.val = -1)) := by
  sorry

/-- If Σ_{i=0}^{n-1} nums1[i] ≠ Σ_{i=0}^{n-1} nums2[i], then the function returns -1.
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_4 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    (nums nums1).sum ≠ (nums nums2).sum →
      ∃ r : Std.I64,
        Aegis.MinOperations.min_operations nums1 nums2 k = ok r ∧ r.val = -1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), (nums nums1).sum ≠ (nums nums2).sum →
      ∃ r : Std.I64,
        Aegis.MinOperations.min_operations nums1 nums2 k = ok r ∧ r.val = -1) := by
  sorry

/-- If k > 0 and there exists an index i with 0 ≤ i < n such that k does not divide nums2[i] - nums1[i], then the function returns -1.
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_5 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    0 < k.val →
      (∃ (i : Nat) (_hi : i < nums1.val.length),
          ¬ k.val ∣ diffAt (nums nums1) (nums nums2) i) →
        ∃ r : Std.I64,
          Aegis.MinOperations.min_operations nums1 nums2 k = ok r ∧ r.val = -1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), 0 < k.val →
      (∃ (i : Nat) (_hi : i < nums1.val.length),
          ¬ k.val ∣ diffAt (nums nums1) (nums nums2) i) →
        ∃ r : Std.I64,
          Aegis.MinOperations.min_operations nums1 nums2 k = ok r ∧ r.val = -1) := by
  sorry

/-- If k > 0 and the function returns a result r with r ≥ 0, then for every i with 0 ≤ i < n, nums2[i] - nums1[i] is divisible by k.
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_6 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    0 < k.val →
      ∀ r : Std.I64,
        Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
        0 ≤ r.val → AllDivisible k.val (nums nums1) (nums nums2) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), 0 < k.val →
      ∀ r : Std.I64,
        Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
        0 ≤ r.val → AllDivisible k.val (nums nums1) (nums nums2)) := by
  sorry

/-- If the function returns a result r with r ≥ 0, then Σ_{i=0}^{n-1} nums1[i] = Σ_{i=0}^{n-1} nums2[i].
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_7 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
      0 ≤ r.val → (nums nums1).sum = (nums nums2).sum := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
      0 ≤ r.val → (nums nums1).sum = (nums nums2).sum) := by
  sorry

/-- If k > 0 and the function returns a result r with r ≥ 0, then for every i with 0 ≤ i < n: if nums2[i] > nums1[i], then r ≥ (nums2[i] - nums1[i]) / k; and if nums1[i] > nums2[i], then r ≥ (nums1[i] - nums2[i]) / k.
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_8 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    0 < k.val →
      ∀ r : Std.I64,
        Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
        0 ≤ r.val →
        ∀ (i : Nat) (_hi : i < nums1.val.length),
          (0 < diffAt (nums nums1) (nums nums2) i →
              r.val ≥ diffAt (nums nums1) (nums nums2) i / k.val) ∧
            (diffAt (nums nums1) (nums nums2) i < 0 →
              r.val ≥ (-(diffAt (nums nums1) (nums nums2) i)) / k.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), 0 < k.val →
      ∀ r : Std.I64,
        Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
        0 ≤ r.val →
        ∀ (i : Nat) (_hi : i < nums1.val.length),
          (0 < diffAt (nums nums1) (nums nums2) i →
              r.val ≥ diffAt (nums nums1) (nums nums2) i / k.val) ∧
            (diffAt (nums nums1) (nums nums2) i < 0 →
              r.val ≥ (-(diffAt (nums nums1) (nums nums2) i)) / k.val)) := by
  sorry

/-- If the function returns a result r with r ≠ -1, then 0 ≤ r ≤ 10^14.
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_9 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
      r.val ≠ -1 → 0 ≤ r.val ∧ r.val ≤ 10 ^ 14 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
      r.val ≠ -1 → 0 ≤ r.val ∧ r.val ≤ 10 ^ 14) := by
  sorry

/-- If k > 0 and the function returns a result r with r ≥ 0, then Σ over i with nums2[i] > nums1[i] of (nums2[i] - nums1[i]) / k = Σ over i with nums1[i] > nums2[i] of (nums1[i] - nums2[i]) / k.
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_10 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    0 < k.val →
      ∀ r : Std.I64,
        Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
        0 ≤ r.val →
        posSum k.val (nums nums1) (nums nums2) =
          negSum k.val (nums nums1) (nums nums2) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), 0 < k.val →
      ∀ r : Std.I64,
        Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
        0 ≤ r.val →
        posSum k.val (nums nums1) (nums nums2) =
          negSum k.val (nums nums1) (nums nums2)) := by
  sorry

/-- Whenever the function returns -1, at least one of the following holds: (a) k = 0 and there exists i with 0 ≤ i < n and nums1[i] ≠ nums2[i]; (b) k > 0 and there exists i with 0 ≤ i < n such that k does not divide nums2[i] - nums1[i]; (c) Σ_{i=0}^{n-1} nums1[i] ≠ Σ_{i=0}^{n-1} nums2[i].
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_11 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
      r.val = -1 →
      (k.val = 0 ∧
          ∃ (i : Nat) (hi : i < nums1.val.length),
            (nums1.val[i]'hi).val ≠ (nums2.val[i]'(by omega)).val) ∨
        (0 < k.val ∧
          ∃ (i : Nat) (_hi : i < nums1.val.length),
            ¬ k.val ∣ diffAt (nums nums1) (nums nums2) i) ∨
        (nums nums1).sum ≠ (nums nums2).sum := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
      r.val = -1 →
      (k.val = 0 ∧
          ∃ (i : Nat) (hi : i < nums1.val.length),
            (nums1.val[i]'hi).val ≠ (nums2.val[i]'(by omega)).val) ∨
        (0 < k.val ∧
          ∃ (i : Nat) (_hi : i < nums1.val.length),
            ¬ k.val ∣ diffAt (nums nums1) (nums nums2) i) ∨
        (nums nums1).sum ≠ (nums nums2).sum) := by
  sorry

/-- If k > 0 and the function returns a result r with r ≥ 0, then there exists a sequence of exactly r operations transforming nums1 into nums2, and every sequence of operations transforming nums1 into nums2 has length at least r.
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_12 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    0 < k.val →
      ∀ r : Std.I64,
        Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
        0 ≤ r.val →
        (∃ m : Nat,
            (m : Int) = r.val ∧
              Reach k.val (nums nums1) m (nums nums2)) ∧
          (∀ m : Nat,
            Reach k.val (nums nums1) m (nums nums2) → r.val ≤ (m : Int)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), 0 < k.val →
      ∀ r : Std.I64,
        Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
        0 ≤ r.val →
        (∃ m : Nat,
            (m : Int) = r.val ∧
              Reach k.val (nums nums1) m (nums nums2)) ∧
          (∀ m : Nat,
            Reach k.val (nums nums1) m (nums nums2) → r.val ≤ (m : Int))) := by
  sorry

/-- If the function returns -1, then there is no finite sequence of operations (with the given k) that transforms nums1 into nums2.
  Preconditions: Let n = len(nums1). len(nums1) = len(nums2) = n; 2 ≤ n ≤ 10^5; for every i with 0 ≤ i < n, 0 ≤ nums1[i] ≤ 10^9 and 0 ≤ nums2[i] ≤ 10^9; 0 ≤ k ≤ 10^5. -/
theorem spec_13 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
      r.val = -1 →
      ¬ ∃ m : Nat, Reach k.val (nums nums1) m (nums nums2) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (h_len : nums2.val.length = nums1.val.length)
    (h_ge : 2 ≤ nums1.val.length)
    (h_le : nums1.val.length ≤ 10 ^ 5)
    (h_b1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums1.val[i]'hi).val ∧ (nums1.val[i]'hi).val ≤ 10 ^ 9)
    (h_b2 : ∀ (i : Nat) (hi : i < nums1.val.length),
      0 ≤ (nums2.val[i]'(by omega)).val ∧ (nums2.val[i]'(by omega)).val ≤ 10 ^ 9)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 10 ^ 5), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations nums1 nums2 k = ok r →
      r.val = -1 →
      ¬ ∃ m : Nat, Reach k.val (nums nums1) m (nums nums2)) := by
  sorry

end AegisSpec.MinOperations
