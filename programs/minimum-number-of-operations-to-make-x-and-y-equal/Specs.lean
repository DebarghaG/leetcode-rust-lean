import Aegis.MinimumOperationsToMakeEqual.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperationsToMakeEqual.minimum_operations_to_make_equal`

LeetCode problem `minimum-number-of-operations-to-make-x-and-y-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumOperationsToMakeEqual

  open Classical

  open Aegis.MinimumOperationsToMakeEqual

  def Step (a b : Int) : Prop :=
    b = a - 1 ∨ b = a + 1 ∨ (5 ∣ a ∧ b = a / 5) ∨ (11 ∣ a ∧ b = a / 11)

  def Reach (a b : Int) (n : Nat) : Prop :=
    ∃ z : Nat → Int, z 0 = a ∧ z n = b ∧ ∀ i, i < n → Step (z i) (z (i + 1))

  theorem reach_of_le {a b : Int} (h : a ≤ b) : Reach a b (b - a).toNat := by
    refine ⟨fun i => a + (i : Int), by simp, ?_, ?_⟩
    · have hn : ((b - a).toNat : Int) = b - a := Int.toNat_of_nonneg (by omega)
      show a + ((b - a).toNat : Int) = b
      rw [hn]; ring
    · intro i _
      right; left
      push_cast
      ring

  theorem reach_of_ge {a b : Int} (h : b ≤ a) : Reach a b (a - b).toNat := by
    refine ⟨fun i => a - (i : Int), by simp, ?_, ?_⟩
    · have hn : ((a - b).toNat : Int) = a - b := Int.toNat_of_nonneg (by omega)
      show a - ((a - b).toNat : Int) = b
      rw [hn]; ring
    · intro i _
      left
      push_cast
      ring

  theorem reach_exists (a b : Int) : ∃ n, Reach a b n := by
    rcases le_total a b with h | h
    · exact ⟨_, reach_of_le h⟩
    · exact ⟨_, reach_of_ge h⟩

  noncomputable def D (a b : Int) : Nat := Nat.find (reach_exists a b)

  theorem D_spec (a b : Int) : Reach a b (D a b) := Nat.find_spec _

  theorem D_le {a b : Int} {n : Nat} (h : Reach a b n) : D a b ≤ n := Nat.find_min' _ h

  theorem D_min {a b : Int} {n : Nat} (h : n < D a b) : ¬ Reach a b n := Nat.find_min _ h

  /-- Whenever the function returns a result r, r is the least n >= 0 for which there exist integers z_0, ..., z_n with z_0 = x, z_n = y, and for every i with 0 <= i < n, one of the following holds: z_{i+1} = z_i - 1; z_{i+1} = z_i + 1; 5 divides z_i and z_{i+1} = z_i / 5; or 11 divides z_i and z_{i+1} = z_i / 11. All divisions here are exact integer quotients.
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000. -/
  theorem spec_1 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
      ∀ r, minimum_operations_to_make_equal x y = ok r →
        (0 ≤ r.val ∧ Reach x.val y.val r.val.toNat ∧
          ∀ n : Nat, Reach x.val y.val n → r.val ≤ (n : Int)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r, minimum_operations_to_make_equal x y = ok r →
          (0 ≤ r.val ∧ Reach x.val y.val r.val.toNat ∧
            ∀ n : Nat, Reach x.val y.val n → r.val ≤ (n : Int))) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or get stuck for any such x and y.
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000. -/
  theorem spec_2 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
      ∃ r, minimum_operations_to_make_equal x y = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∃ r, minimum_operations_to_make_equal x y = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000. -/
  theorem spec_3 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
      ∀ r, minimum_operations_to_make_equal x y = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r, minimum_operations_to_make_equal x y = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= |x - y|.
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000. -/
  theorem spec_4 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
      ∀ r, minimum_operations_to_make_equal x y = ok r → r.val ≤ |x.val - y.val| := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r, minimum_operations_to_make_equal x y = ok r → r.val ≤ |x.val - y.val|) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000, and x = y. -/
  theorem spec_5 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
      (hxy : x.val = y.val) :
      ∀ r, minimum_operations_to_make_equal x y = ok r → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
        (hxy : x.val = y.val), ∀ r, minimum_operations_to_make_equal x y = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r >= 1.
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000, and x != y. -/
  theorem spec_6 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
      (hxy : x.val ≠ y.val) :
      ∀ r, minimum_operations_to_make_equal x y = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
        (hxy : x.val ≠ y.val), ∀ r, minimum_operations_to_make_equal x y = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist integers z_0, ..., z_r with z_0 = x, z_r = y, and each step z_i -> z_{i+1} is one of the allowed operations: decrement by 1, increment by 1, exact division by 5 when divisible by 5, or exact division by 11 when divisible by 11.
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000. -/
  theorem spec_7 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
      ∀ r, minimum_operations_to_make_equal x y = ok r →
        (0 ≤ r.val ∧ Reach x.val y.val r.val.toNat) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r, minimum_operations_to_make_equal x y = ok r →
          (0 ≤ r.val ∧ Reach x.val y.val r.val.toNat)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 0 <= k < r, there do not exist integers z_0, ..., z_k with z_0 = x, z_k = y, and each step z_i -> z_{i+1} being one of the allowed operations: decrement by 1, increment by 1, exact division by 5 when divisible by 5, or exact division by 11 when divisible by 11.
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000. -/
  theorem spec_8 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
      ∀ r, minimum_operations_to_make_equal x y = ok r →
        ∀ k : Int, 0 ≤ k → k < r.val → ¬ Reach x.val y.val k.toNat := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r, minimum_operations_to_make_equal x y = ok r →
          ∀ k : Int, 0 ≤ k → k < r.val → ¬ Reach x.val y.val k.toNat) := by
    sorry

  /-- Whenever the function returns a result r, r <= 1 + D(x + 1, y), where D(a,b) is the minimum n >= 0 such that some sequence a = z_0, ..., z_n = b uses only allowed steps z_{i+1}=z_i-1, z_{i+1}=z_i+1, z_{i+1}=z_i/5 when 5 divides z_i, and z_{i+1}=z_i/11 when 11 divides z_i (exact quotients).
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000. -/
  theorem spec_9 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
      ∀ r, minimum_operations_to_make_equal x y = ok r →
        r.val ≤ 1 + (D (x.val + 1) y.val : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r, minimum_operations_to_make_equal x y = ok r →
          r.val ≤ 1 + (D (x.val + 1) y.val : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= 1 + D(x - 1, y), where D(a,b) is the minimum n >= 0 such that some sequence a = z_0, ..., z_n = b uses only allowed steps z_{i+1}=z_i-1, z_{i+1}=z_i+1, z_{i+1}=z_i/5 when 5 divides z_i, and z_{i+1}=z_i/11 when 11 divides z_i (exact quotients).
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000, and x > 1. -/
  theorem spec_10 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
      (hx : 1 < x.val) :
      ∀ r, minimum_operations_to_make_equal x y = ok r →
        r.val ≤ 1 + (D (x.val - 1) y.val : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
        (hx : 1 < x.val), ∀ r, minimum_operations_to_make_equal x y = ok r →
          r.val ≤ 1 + (D (x.val - 1) y.val : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= 1 + D(x / 5, y), where D(a,b) is the minimum n >= 0 such that some sequence a = z_0, ..., z_n = b uses only allowed steps z_{i+1}=z_i-1, z_{i+1}=z_i+1, z_{i+1}=z_i/5 when 5 divides z_i, and z_{i+1}=z_i/11 when 11 divides z_i (exact quotients).
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000, and 5 divides x. -/
  theorem spec_11 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
      (h5 : 5 ∣ x.val) :
      ∀ r, minimum_operations_to_make_equal x y = ok r →
        r.val ≤ 1 + (D (x.val / 5) y.val : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
        (h5 : 5 ∣ x.val), ∀ r, minimum_operations_to_make_equal x y = ok r →
          r.val ≤ 1 + (D (x.val / 5) y.val : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= 1 + D(x / 11, y), where D(a,b) is the minimum n >= 0 such that some sequence a = z_0, ..., z_n = b uses only allowed steps z_{i+1}=z_i-1, z_{i+1}=z_i+1, z_{i+1}=z_i/5 when 5 divides z_i, and z_{i+1}=z_i/11 when 11 divides z_i (exact quotients).
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000, and 11 divides x. -/
  theorem spec_12 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
      (h11 : 11 ∣ x.val) :
      ∀ r, minimum_operations_to_make_equal x y = ok r →
        r.val ≤ 1 + (D (x.val / 11) y.val : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
        (h11 : 11 ∣ x.val), ∀ r, minimum_operations_to_make_equal x y = ok r →
          r.val ≤ 1 + (D (x.val / 11) y.val : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer z, r <= D(x, z) + D(z, y), where D(a,b) is the minimum n >= 0 such that some sequence a = z_0, ..., z_n = b uses only allowed steps z_{i+1}=z_i-1, z_{i+1}=z_i+1, z_{i+1}=z_i/5 when 5 divides z_i, and z_{i+1}=z_i/11 when 11 divides z_i (exact quotients).
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000. -/
  theorem spec_13 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
      ∀ r, minimum_operations_to_make_equal x y = ok r →
        ∀ z : Int, r.val ≤ (D x.val z : Int) + (D z y.val : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r, minimum_operations_to_make_equal x y = ok r →
          ∀ z : Int, r.val ≤ (D x.val z : Int) + (D z y.val : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000, and x = 5*y. -/
  theorem spec_14 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
      (hxy : x.val = 5 * y.val) :
      ∀ r, minimum_operations_to_make_equal x y = ok r → r.val = 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
        (hxy : x.val = 5 * y.val), ∀ r, minimum_operations_to_make_equal x y = ok r → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r = y - x.
    Preconditions: The I64 arguments x and y, interpreted as mathematical integers, satisfy 1 <= x <= 10000 and 1 <= y <= 10000, and x < y. -/
  theorem spec_15 (x y : I64)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
      (hxy : x.val < y.val) :
      ∀ r, minimum_operations_to_make_equal x y = ok r → r.val = y.val - x.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (x y : I64)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
        (hxy : x.val < y.val), ∀ r, minimum_operations_to_make_equal x y = ok r → r.val = y.val - x.val) := by
    sorry

  end AegisSpec.MinimumOperationsToMakeEqual
