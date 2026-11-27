import Aegis.LargestOverlap.Code.Funs

/-!
# Specifications of `Aegis.LargestOverlap.largest_overlap`

LeetCode problem `image-overlap`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open Aeneas.Std.Result

namespace AegisSpec.LargestOverlap

def row (img : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
  match img.val[i]? with
  | none => []
  | some r => r.slice.val.map (fun x => x.val)

def rowLen (img : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℕ :=
  (row img i).length

def cell (img : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
  ((row img i)[j]?).getD 0

def ones (img : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n).filter (fun p => cell img p.1 p.2 = 1)).card

def coincides (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (dr dc : ℤ)
    (p : ℕ × ℕ) : Prop :=
  0 ≤ (p.1 : ℤ) + dr ∧ (p.1 : ℤ) + dr < (n : ℤ) ∧
    0 ≤ (p.2 : ℤ) + dc ∧ (p.2 : ℤ) + dc < (n : ℤ) ∧
    cell img1 p.1 p.2 = 1 ∧ cell img2 ((p.1 : ℤ) + dr).toNat ((p.2 : ℤ) + dc).toNat = 1

instance coincides.instDecidablePred (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (dr dc : ℤ) : DecidablePred (coincides img1 img2 n dr dc) :=
  fun p => by unfold coincides; infer_instance

def overlap (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (dr dc : ℤ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n).filter (coincides img1 img2 n dr dc)).card

/-- For integers dr and dc, let overlap(dr, dc) be the number of pairs (i, j) with 0 <= i < n, 0 <= j < n, 0 <= i+dr < n, 0 <= j+dc < n, img1[i][j] = 1 and img2[i+dr][j+dc] = 1; this is the number of positions where a 1 of img1, translated down by dr rows and right by dc columns, coincides with a 1 of img2 (1s moved outside the n x n board are erased). The function returns a result r and r = max over all integers dr and dc of overlap(dr, dc): the largest achievable number of coinciding 1s over all translations of img1 relative to img2.
  Preconditions: n = len(img1) = len(img2) with 1 <= n <= 30; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; for every i, j with 0 <= i < n and 0 <= j < n, img1[i][j] is 0 or 1 and img2[i][j] is 0 or 1. -/
theorem spec_1
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∃ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r ∧
        (∀ dr dc : ℤ, (overlap img1 img2 n dr dc : ℤ) ≤ r.val) ∧
        (∃ dr dc : ℤ, r.val = (overlap img1 img2 n dr dc : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∃ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r ∧
        (∀ dr dc : ℤ, (overlap img1 img2 n dr dc : ℤ) ≤ r.val) ∧
        (∃ dr dc : ℤ, r.val = (overlap img1 img2 n dr dc : ℤ))) := by
  sorry

/-- The function returns a result r; it never overflows, indexes out of bounds, or panics on any input satisfying the preconditions.
  Preconditions: n = len(img1) = len(img2) with 1 <= n <= 30; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; for every i, j with 0 <= i < n and 0 <= j < n, img1[i][j] is 0 or 1 and img2[i][j] is 0 or 1. -/
theorem spec_2
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∃ r : Std.I64, Aegis.LargestOverlap.largest_overlap img1 img2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∃ r : Std.I64, Aegis.LargestOverlap.largest_overlap img1 img2 = ok r) := by
  sorry

/-- Let ones1 = the number of pairs (i, j) with 0 <= i < n, 0 <= j < n and img1[i][j] = 1, and ones2 = the number of pairs (i, j) with 0 <= i < n, 0 <= j < n and img2[i][j] = 1. Whenever the function returns a result r, 0 <= r <= min(ones1, ones2).
  Preconditions: n = len(img1) = len(img2) with n >= 1; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; entries are 0 or 1. -/
theorem spec_3
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        0 ≤ r.val ∧ r.val ≤ ((min (ones img1 n) (ones img2 n) : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        0 ≤ r.val ∧ r.val ≤ ((min (ones img1 n) (ones img2 n) : ℕ) : ℤ)) := by
  sorry

/-- With overlap(dr, dc) defined as in spec_1, whenever the function returns a result r there exist integers dr and dc with -(n-1) <= dr <= n-1 and -(n-1) <= dc <= n-1 such that r = overlap(dr, dc).
  Preconditions: n = len(img1) = len(img2) with n >= 1; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; entries are 0 or 1. -/
theorem spec_4
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        ∃ dr dc : ℤ,
          -((n : ℤ) - 1) ≤ dr ∧ dr ≤ (n : ℤ) - 1 ∧
            -((n : ℤ) - 1) ≤ dc ∧ dc ≤ (n : ℤ) - 1 ∧
            r.val = (overlap img1 img2 n dr dc : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        ∃ dr dc : ℤ,
          -((n : ℤ) - 1) ≤ dr ∧ dr ≤ (n : ℤ) - 1 ∧
            -((n : ℤ) - 1) ≤ dc ∧ dc ≤ (n : ℤ) - 1 ∧
            r.val = (overlap img1 img2 n dr dc : ℤ)) := by
  sorry

/-- Whenever the function returns a result r: r = 0 if and only if every entry of img1 is 0 or every entry of img2 is 0 (equivalently, img1 contains no 1 or img2 contains no 1).
  Preconditions: n = len(img1) = len(img2) with n >= 1; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; entries are 0 or 1. -/
theorem spec_5
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        (r.val = 0 ↔
          (∀ i j, i < n → j < n → cell img1 i j = 0) ∨
            (∀ i j, i < n → j < n → cell img2 i j = 0)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        (r.val = 0 ↔
          (∀ i j, i < n → j < n → cell img1 i j = 0) ∨
            (∀ i j, i < n → j < n → cell img2 i j = 0))) := by
  sorry

/-- Whenever the function returns a result r and n = 1, r = img1[0][0] * img2[0][0]; that is, r = 1 if both single entries are 1 and r = 0 otherwise.
  Preconditions: n = len(img1) = len(img2) with n >= 1; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; entries are 0 or 1. -/
theorem spec_6
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        n = 1 → r.val = cell img1 0 0 * cell img2 0 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        n = 1 → r.val = cell img1 0 0 * cell img2 0 0) := by
  sorry

/-- Whenever the function returns a result r, r >= the number of pairs (i, j) with 0 <= i < n, 0 <= j < n, img1[i][j] = 1 and img2[i][j] = 1 (the overlap produced by the zero translation, i.e. placing the images on top of each other without shifting).
  Preconditions: n = len(img1) = len(img2) with n >= 1; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; entries are 0 or 1. -/
theorem spec_7
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        (overlap img1 img2 n 0 0 : ℤ) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        (overlap img1 img2 n 0 0 : ℤ) ≤ r.val) := by
  sorry

/-- Let ones1 = the number of pairs (i, j) with 0 <= i < n, 0 <= j < n and img1[i][j] = 1. Whenever the function returns a result r and img1[i][j] = img2[i][j] for every 0 <= i < n and 0 <= j < n, r = ones1.
  Preconditions: n = len(img1) = len(img2) with n >= 1; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; entries are 0 or 1. -/
theorem spec_8
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        (∀ i j, i < n → j < n → cell img1 i j = cell img2 i j) →
          r.val = (ones img1 n : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        (∀ i j, i < n → j < n → cell img1 i j = cell img2 i j) →
          r.val = (ones img1 n : ℤ)) := by
  sorry

/-- Let ones1 = the number of pairs (i, j) with 0 <= i < n, 0 <= j < n and img1[i][j] = 1, and ones2 likewise for img2. Whenever the function returns a result r, if ones1 = 1 and ones2 >= 1, then r = 1.
  Preconditions: n = len(img1) = len(img2) with n >= 1; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; entries are 0 or 1. -/
theorem spec_9
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        ones img1 n = 1 → 1 ≤ ones img2 n → r.val = 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        ones img1 n = 1 → 1 ≤ ones img2 n → r.val = 1) := by
  sorry

/-- Let ones1 = the number of pairs (i, j) with 0 <= i < n, 0 <= j < n and img1[i][j] = 1, and ones2 likewise for img2. Whenever the function returns a result r, r * (2*n - 1) * (2*n - 1) >= ones1 * ones2.
  Preconditions: n = len(img1) = len(img2) with n >= 1; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; entries are 0 or 1. -/
theorem spec_10
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        (ones img1 n : ℤ) * (ones img2 n : ℤ) ≤
          r.val * (((2 : ℤ) * n - 1) * ((2 : ℤ) * n - 1)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        (ones img1 n : ℤ) * (ones img2 n : ℤ) ≤
          r.val * (((2 : ℤ) * n - 1) * ((2 : ℤ) * n - 1))) := by
  sorry

/-- With overlap(dr, dc) defined as in spec_1, whenever the function returns a result r with r > 0, there exist indices i, j, i', j' with 0 <= i, j, i', j' < n, img1[i][j] = 1 and img2[i'][j'] = 1 such that r = overlap(i' - i, j' - j); that is, some optimal translation makes a particular 1 of img1 land exactly on a particular 1 of img2.
  Preconditions: n = len(img1) = len(img2) with n >= 1; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; entries are 0 or 1. -/
theorem spec_11
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        0 < r.val →
          ∃ i j i' j' : ℕ,
            i < n ∧ j < n ∧ i' < n ∧ j' < n ∧
              cell img1 i j = 1 ∧ cell img2 i' j' = 1 ∧
              r.val = (overlap img1 img2 n ((i' : ℤ) - i) ((j' : ℤ) - j) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        0 < r.val →
          ∃ i j i' j' : ℕ,
            i < n ∧ j < n ∧ i' < n ∧ j' < n ∧
              cell img1 i j = 1 ∧ cell img2 i' j' = 1 ∧
              r.val = (overlap img1 img2 n ((i' : ℤ) - i) ((j' : ℤ) - j) : ℤ)) := by
  sorry

/-- Let ones2 = the number of pairs (i, j) with 0 <= i < n, 0 <= j < n and img2[i][j] = 1. Whenever the function returns a result r and img1[i][j] = 1 for every 0 <= i < n and 0 <= j < n, r = ones2.
  Preconditions: n = len(img1) = len(img2) with n >= 1; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; entries are 0 or 1. -/
theorem spec_12
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        (∀ i j, i < n → j < n → cell img1 i j = 1) →
          r.val = (ones img2 n : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : 1 ≤ n)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        (∀ i j, i < n → j < n → cell img1 i j = 1) →
          r.val = (ones img2 n : ℤ)) := by
  sorry

/-- Whenever the function returns result r on (img1, img2) and result r' on (img2, img1), r = r'; equivalently, largest_overlap is symmetric in its two image arguments.
  Preconditions: n = len(img1) = len(img2) with 1 <= n <= 30; for every i with 0 <= i < n, len(img1[i]) = n and len(img2[i]) = n; for every i, j with 0 <= i < n and 0 <= j < n, img1[i][j] is 0 or 1 and img2[i][j] is 0 or 1. -/
theorem spec_13
    (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r r' : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        Aegis.LargestOverlap.largest_overlap img2 img1 = ok r' → r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (img1 img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
    (hlen1 : img1.val.length = n) (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r r' : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        Aegis.LargestOverlap.largest_overlap img2 img1 = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever largest_overlap(img1, img2) returns r and largest_overlap(img1', img2) returns r', then r <= r'. More generally, changing any 0 entries of either image to 1 cannot decrease the maximum overlap.
  Preconditions: n = len(img1) = len(img1') = len(img2) with 1 <= n <= 30; all four matrices are n x n with 0/1 entries; for every i, j with 0 <= i < n and 0 <= j < n, img1[i][j] <= img1'[i][j]. -/
theorem spec_14
    (img1 img1' img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
    (hlen1 : img1.val.length = n) (hlen1' : img1'.val.length = n)
    (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows1' : ∀ i, i < n → rowLen img1' i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin1' : ∀ i j, i < n → j < n → cell img1' i j = 0 ∨ cell img1' i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1) :
    ∀ r r' : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        Aegis.LargestOverlap.largest_overlap img1' img2 = ok r' →
          (∀ i j, i < n → j < n → cell img1 i j ≤ cell img1' i j) → r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (img1 img1' img2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
    (hlen1 : img1.val.length = n) (hlen1' : img1'.val.length = n)
    (hlen2 : img2.val.length = n)
    (hrows1 : ∀ i, i < n → rowLen img1 i = n)
    (hrows1' : ∀ i, i < n → rowLen img1' i = n)
    (hrows2 : ∀ i, i < n → rowLen img2 i = n)
    (hbin1 : ∀ i j, i < n → j < n → cell img1 i j = 0 ∨ cell img1 i j = 1)
    (hbin1' : ∀ i j, i < n → j < n → cell img1' i j = 0 ∨ cell img1' i j = 1)
    (hbin2 : ∀ i j, i < n → j < n → cell img2 i j = 0 ∨ cell img2 i j = 1), ∀ r r' : Std.I64,
      Aegis.LargestOverlap.largest_overlap img1 img2 = ok r →
        Aegis.LargestOverlap.largest_overlap img1' img2 = ok r' →
          (∀ i j, i < n → j < n → cell img1 i j ≤ cell img1' i j) → r.val ≤ r'.val) := by
  sorry

end AegisSpec.LargestOverlap
