import Aegis.MaximumNumberOfOnes.Code.Funs

/-!
# Specifications of `Aegis.MaximumNumberOfOnes.maximum_number_of_ones`

LeetCode problem `maximum-number-of-ones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumNumberOfOnes

  namespace AegisSpec.MaximumNumberOfOnes

  def BlockSum (M : ℕ → ℕ → ℕ) (u v s : ℕ) : ℕ :=
    ∑ i ∈ Finset.range s, ∑ j ∈ Finset.range s, M (u + i) (v + j)

  def TotalOnes (M : ℕ → ℕ → ℕ) (height width : ℕ) : ℕ :=
    ∑ i ∈ Finset.range height, ∑ j ∈ Finset.range width, M i j

  def Feasible (M : ℕ → ℕ → ℕ) (height width sideLength maxOnes : ℕ) : Prop :=
    (∀ i, i < height → ∀ j, j < width → (M i j = 0 ∨ M i j = 1)) ∧
      ∀ u v, u + sideLength ≤ height → v + sideLength ≤ width →
        BlockSum M u v sideLength ≤ maxOnes

  def modCount (n s a : ℕ) : ℕ := ((List.range n).filter (fun i => i % s = a)).length

  def productCounts (width height sideLength : ℕ) : List ℕ :=
    (List.range sideLength).flatMap fun a =>
      (List.range sideLength).map fun b =>
        modCount height sideLength a * modCount width sideLength b

  def insertDesc (a : ℕ) : List ℕ → List ℕ
    | [] => [a]
    | b :: rest => if b ≤ a then a :: b :: rest else b :: insertDesc a rest

  def sortDesc : List ℕ → List ℕ
    | [] => []
    | a :: rest => insertDesc a (sortDesc rest)

  def sumLargest (k : ℕ) (l : List ℕ) : ℕ := ((sortDesc l).take k).sum

  def listMin : List ℕ → ℕ
    | [] => 0
    | a :: rest => rest.foldr min a

  /-- Whenever the function returns a result r, r is the maximum possible number of ones in a binary matrix M with height rows and width columns (M[i][j] is 0 or 1 for every 0 <= i < height and 0 <= j < width) such that for every row start u with 0 <= u <= height - sideLength and every column start v with 0 <= v <= width - sideLength, the sum of M[i][j] over u <= i < u + sideLength and v <= j < v + sideLength is at most maxOnes. Equivalently, r is the largest integer t for which there exists such a matrix M with exactly t ones.
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength. -/
  theorem spec_1 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      (∃ M : ℕ → ℕ → ℕ,
          Feasible M height.val.toNat width.val.toNat sideLength.val.toNat maxOnes.val.toNat ∧
            (TotalOnes M height.val.toNat width.val.toNat : ℤ) = r.val) ∧
        ∀ t : ℤ,
          (∃ M : ℕ → ℕ → ℕ,
              Feasible M height.val.toNat width.val.toNat sideLength.val.toNat maxOnes.val.toNat ∧
                (TotalOnes M height.val.toNat width.val.toNat : ℤ) = t) → t ≤ r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), (∃ M : ℕ → ℕ → ℕ,
            Feasible M height.val.toNat width.val.toNat sideLength.val.toNat maxOnes.val.toNat ∧
              (TotalOnes M height.val.toNat width.val.toNat : ℤ) = r.val) ∧
          ∀ t : ℤ,
            (∃ M : ℕ → ℕ → ℕ,
                Feasible M height.val.toNat width.val.toNat sideLength.val.toNat maxOnes.val.toNat ∧
                  (TotalOnes M height.val.toNat width.val.toNat : ℤ) = t) → t ≤ r.val) := by
    sorry

  /-- The function returns a result r and does not fail: no arithmetic overflow, out-of-bounds access, or panic occurs.
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength. -/
  theorem spec_2 (width height sideLength maxOnes : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val) :
      ∃ r : Aeneas.Std.I64, maximum_number_of_ones width height sideLength maxOnes = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (width height sideLength maxOnes : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val), ∃ r : Aeneas.Std.I64, maximum_number_of_ones width height sideLength maxOnes = ok r) := by
    sorry

  /-- Whenever the function returns r, 0 <= r <= width*height.
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength. -/
  theorem spec_3 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      0 ≤ r.val ∧ r.val ≤ width.val * height.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), 0 ≤ r.val ∧ r.val ≤ width.val * height.val) := by
    sorry

  /-- Whenever the function returns r, r >= maxOnes * (width div sideLength) * (height div sideLength).
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength. -/
  theorem spec_4 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      maxOnes.val * (width.val / sideLength.val) * (height.val / sideLength.val) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), maxOnes.val * (width.val / sideLength.val) * (height.val / sideLength.val) ≤ r.val) := by
    sorry

  /-- Whenever the function returns r, r <= maxOnes * ((width + sideLength - 1) div sideLength) * ((height + sideLength - 1) div sideLength).
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength. -/
  theorem spec_5 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      r.val ≤
        maxOnes.val * ((width.val + sideLength.val - 1) / sideLength.val) *
          ((height.val + sideLength.val - 1) / sideLength.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), r.val ≤
          maxOnes.val * ((width.val + sideLength.val - 1) / sideLength.val) *
            ((height.val + sideLength.val - 1) / sideLength.val)) := by
    sorry

  /-- Whenever the function returns r, r = 0.
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength; and maxOnes = 0. -/
  theorem spec_6 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hm_zero : maxOnes.val = 0)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hm_zero : maxOnes.val = 0)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), r.val = 0) := by
    sorry

  /-- Whenever the function returns r, r = width*height.
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength; and maxOnes = sideLength*sideLength. -/
  theorem spec_7 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hm_full : maxOnes.val = sideLength.val * sideLength.val)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      r.val = width.val * height.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hm_full : maxOnes.val = sideLength.val * sideLength.val)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), r.val = width.val * height.val) := by
    sorry

  /-- Whenever the function returns r, r = ((width + sideLength - 1) div sideLength) * ((height + sideLength - 1) div sideLength).
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength; and maxOnes = 1. -/
  theorem spec_8 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hm_one : maxOnes.val = 1)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      r.val =
        ((width.val + sideLength.val - 1) / sideLength.val) *
          ((height.val + sideLength.val - 1) / sideLength.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hm_one : maxOnes.val = 1)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), r.val =
          ((width.val + sideLength.val - 1) / sideLength.val) *
            ((height.val + sideLength.val - 1) / sideLength.val)) := by
    sorry

  /-- Whenever the function returns r, r = (height div sideLength)*maxOnes + min((height mod sideLength)*width, maxOnes).
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength; and width = sideLength. -/
  theorem spec_9 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hw_eq : width.val = sideLength.val)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      r.val = (height.val / sideLength.val) * maxOnes.val +
        min ((height.val % sideLength.val) * width.val) maxOnes.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hw_eq : width.val = sideLength.val)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), r.val = (height.val / sideLength.val) * maxOnes.val +
          min ((height.val % sideLength.val) * width.val) maxOnes.val) := by
    sorry

  /-- Whenever the function returns r, r = (width div sideLength)*maxOnes + min((width mod sideLength)*height, maxOnes).
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength; and height = sideLength. -/
  theorem spec_10 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hh_eq : height.val = sideLength.val)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      r.val = (width.val / sideLength.val) * maxOnes.val +
        min ((width.val % sideLength.val) * height.val) maxOnes.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hh_eq : height.val = sideLength.val)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), r.val = (width.val / sideLength.val) * maxOnes.val +
          min ((width.val % sideLength.val) * height.val) maxOnes.val) := by
    sorry

  /-- For 0 <= a < sideLength, let rowCount(a) be the number of integers i with 0 <= i < height and i mod sideLength = a, and for 0 <= b < sideLength, let colCount(b) be the number of integers j with 0 <= j < width and j mod sideLength = b. Whenever the function returns r, r = width*height - min{ rowCount(a)*colCount(b) | 0 <= a < sideLength and 0 <= b < sideLength }.
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength; and maxOnes = sideLength*sideLength - 1. -/
  theorem spec_11 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hm_last : maxOnes.val = sideLength.val * sideLength.val - 1)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      r.val = width.val * height.val -
        (listMin (productCounts width.val.toNat height.val.toNat sideLength.val.toNat) : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hm_last : maxOnes.val = sideLength.val * sideLength.val - 1)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), r.val = width.val * height.val -
          (listMin (productCounts width.val.toNat height.val.toNat sideLength.val.toNat) : ℤ)) := by
    sorry

  /-- For every integer k with maxOnes <= k <= sideLength*sideLength, if the function returns r for parameter maxOnes and returns r' for parameter k with all other parameters unchanged, then r <= r'.
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength. -/
  theorem spec_12 (width height sideLength maxOnes k r r' : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hk_lo : maxOnes.val ≤ k.val)
      (hk_hi : k.val ≤ sideLength.val * sideLength.val)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r)
      (hr' : maximum_number_of_ones width height sideLength k = ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (width height sideLength maxOnes k r r' : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hk_lo : maxOnes.val ≤ k.val)
        (hk_hi : k.val ≤ sideLength.val * sideLength.val)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r)
        (hr' : maximum_number_of_ones width height sideLength k = ok r'), r.val ≤ r'.val) := by
    sorry

  /-- Whenever the call with (width, height, sideLength, maxOnes) returns r, the call with (height, width, sideLength, maxOnes) also returns r.
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength. -/
  theorem spec_13 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      maximum_number_of_ones height width sideLength maxOnes = ok r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), maximum_number_of_ones height width sideLength maxOnes = ok r) := by
    sorry

  /-- Whenever the function returns r, there exists a binary matrix M with height rows and width columns such that every contiguous sideLength x sideLength submatrix of M has sum at most maxOnes and M has exactly r ones.
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength. -/
  theorem spec_14 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      ∃ M : ℕ → ℕ → ℕ,
        Feasible M height.val.toNat width.val.toNat sideLength.val.toNat maxOnes.val.toNat ∧
          (TotalOnes M height.val.toNat width.val.toNat : ℤ) = r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), ∃ M : ℕ → ℕ → ℕ,
          Feasible M height.val.toNat width.val.toNat sideLength.val.toNat maxOnes.val.toNat ∧
            (TotalOnes M height.val.toNat width.val.toNat : ℤ) = r.val) := by
    sorry

  /-- For 0 <= a < sideLength let rowCount(a) be the number of integers i with 0 <= i < height and i mod sideLength = a, and for 0 <= b < sideLength let colCount(b) be the number of integers j with 0 <= j < width and j mod sideLength = b. Whenever the function returns r, r equals the sum of the maxOnes largest elements, counted with multiplicity, of the multiset { rowCount(a)*colCount(b) | 0 <= a < sideLength and 0 <= b < sideLength }; the sum of zero elements is 0.
    Preconditions: width, height, sideLength, maxOnes are integers satisfying 1 <= width, height <= 100; 1 <= sideLength <= width and sideLength <= height; 0 <= maxOnes <= sideLength*sideLength. -/
  theorem spec_15 (width height sideLength maxOnes r : Aeneas.Std.I64)
      (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
      (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
      (hs_pos : 1 ≤ sideLength.val)
      (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
      (hm_lo : 0 ≤ maxOnes.val)
      (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
      (hr : maximum_number_of_ones width height sideLength maxOnes = ok r) :
      r.val =
        (sumLargest maxOnes.val.toNat
          (productCounts width.val.toNat height.val.toNat sideLength.val.toNat) : ℤ) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (width height sideLength maxOnes r : Aeneas.Std.I64)
        (hw_lo : 1 ≤ width.val) (hw_hi : width.val ≤ 100)
        (hh_lo : 1 ≤ height.val) (hh_hi : height.val ≤ 100)
        (hs_pos : 1 ≤ sideLength.val)
        (hs_width : sideLength.val ≤ width.val) (hs_height : sideLength.val ≤ height.val)
        (hm_lo : 0 ≤ maxOnes.val)
        (hm_hi : maxOnes.val ≤ sideLength.val * sideLength.val)
        (hr : maximum_number_of_ones width height sideLength maxOnes = ok r), r.val =
          (sumLargest maxOnes.val.toNat
            (productCounts width.val.toNat height.val.toNat sideLength.val.toNat) : ℤ)) := by
    sorry

  end AegisSpec.MaximumNumberOfOnes
