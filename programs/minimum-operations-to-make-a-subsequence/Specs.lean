import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-a-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Classical

namespace AegisSpec.MinOperations

def vals (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

def InRange (xs : List ℤ) : Prop := ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 1000000000

def NoDupVals (xs : List ℤ) : Prop :=
  ∀ (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length), i ≠ j →
    xs.get ⟨i, hi⟩ ≠ xs.get ⟨j, hj⟩

def IsSubseq (xs ys : List ℤ) : Prop :=
  ∃ t : Fin xs.length → Fin ys.length,
    StrictMono t ∧ ∀ a : Fin xs.length, ys.get (t a) = xs.get a

def IsCommonSubseq (xs ys : List ℤ) (k : ℕ) : Prop :=
  ∃ (i : Fin k → Fin xs.length) (j : Fin k → Fin ys.length),
    StrictMono i ∧ StrictMono j ∧ ∀ a : Fin k, xs.get (i a) = ys.get (j a)

noncomputable def lcsLen (xs ys : List ℤ) : ℕ :=
  Nat.findGreatest (fun k => IsCommonSubseq xs ys k) xs.length

def missingCount (xs ys : List ℤ) : ℕ :=
  (xs.filter (fun x => decide (x ∈ ys))).length

def firstVal (xs : List ℤ) : ℤ := xs.headD 0

def IsIncrSubseq (p : List ℕ) (k : ℕ) : Prop :=
  ∃ t : Fin k → Fin p.length,
    StrictMono t ∧ ∀ a b : Fin k, a < b → p.get (t a) < p.get (t b)

noncomputable def lisLen (p : List ℕ) : ℕ :=
  Nat.findGreatest (fun k => IsIncrSubseq p k) p.length

def Pseq (xs ys : List ℤ) : List ℕ :=
  (ys.filter (fun y => decide (y ∈ xs))).map (fun y => xs.idxOf y)

/-- Let n = len(target) and m = len(arr). Let L be the largest integer k with 0 <= k <= n for which there exist indices 0 <= i_0 < ... < i_{k-1} < n and 0 <= j_0 < ... < j_{k-1} < m such that target[i_t] = arr[j_t] for every 0 <= t < k. Empty choices are allowed when k = 0. The function returns a result r and r = n - L; equivalently, r = len(target) - (length of a longest common subsequence of target and arr).
  Preconditions: target and arr satisfy the problem constraints: 1 <= len(target) <= 100000, 1 <= len(arr) <= 100000, every target[i] and arr[j] lies in [1, 1000000000], and target has no duplicate values (for all i != j, target[i] != target[j]). -/
theorem spec_1 (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)) :
    ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      r.val = ((target.val.length : ℕ) : ℤ) - ((lcsLen (vals target) (vals arr) : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)), ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      r.val = ((target.val.length : ℕ) : ℤ) - ((lcsLen (vals target) (vals arr) : ℕ) : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail by panic, out-of-bounds access, or arithmetic overflow.
  Preconditions: target and arr satisfy the problem constraints: 1 <= len(target) <= 100000, 1 <= len(arr) <= 100000, every target[i] and arr[j] lies in [1, 1000000000], and target has no duplicate values. -/
theorem spec_2 (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)) :
    ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)), ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= len(target).
  Preconditions: target and arr satisfy the problem constraints: 1 <= len(target) <= 100000, 1 <= len(arr) <= 100000, every target[i] and arr[j] lies in [1, 1000000000], and target has no duplicate values. -/
theorem spec_3 (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)) :
    ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      0 ≤ r.val ∧ r.val ≤ ((target.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)), ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      0 ≤ r.val ∧ r.val ≤ ((target.val.length : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result r and r >= missing, where missing is the number of indices i with 0 <= i < len(target) such that target[i] != arr[j] for every j with 0 <= j < len(arr).
  Preconditions: target and arr satisfy the problem constraints: 1 <= len(target) <= 100000, 1 <= len(arr) <= 100000, every target[i] and arr[j] lies in [1, 1000000000], and target has no duplicate values. -/
theorem spec_4 (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)) :
    ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      ((missingCount (vals target) (vals arr) : ℕ) : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)), ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      ((missingCount (vals target) (vals arr) : ℕ) : ℤ) ≤ r.val) := by
  sorry

/-- Let n = len(target). The function returns a result r and r = 0 if and only if target is a subsequence of arr, i.e., if and only if there exist indices 0 <= j_0 < ... < j_{n-1} < len(arr) with arr[j_t] = target[t] for every 0 <= t < n.
  Preconditions: target and arr satisfy the problem constraints: 1 <= len(target) <= 100000, 1 <= len(arr) <= 100000, every target[i] and arr[j] lies in [1, 1000000000], and target has no duplicate values. -/
theorem spec_5 (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)) :
    ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      (r.val = 0 ↔ IsSubseq (vals target) (vals arr)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)), ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      (r.val = 0 ↔ IsSubseq (vals target) (vals arr))) := by
  sorry

/-- Let n = len(target). The function returns a result r and r = n if and only if no value of target occurs in arr: for every i with 0 <= i < n and every j with 0 <= j < len(arr), target[i] != arr[j].
  Preconditions: target and arr satisfy the problem constraints: 1 <= len(target) <= 100000, 1 <= len(arr) <= 100000, every target[i] and arr[j] lies in [1, 1000000000], and target has no duplicate values. -/
theorem spec_6 (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)) :
    ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      (r.val = ((target.val.length : ℕ) : ℤ) ↔
        ∀ (i : ℕ) (hi : i < target.val.length)
          (j : ℕ) (hj : j < arr.val.length),
          (target.val.get ⟨i, hi⟩).val ≠ (arr.val.get ⟨j, hj⟩).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)), ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      (r.val = ((target.val.length : ℕ) : ℤ) ↔
        ∀ (i : ℕ) (hi : i < target.val.length)
          (j : ℕ) (hj : j < arr.val.length),
          (target.val.get ⟨i, hi⟩).val ≠ (arr.val.get ⟨j, hj⟩).val)) := by
  sorry

/-- The function returns a result r and r = 0 if target[0] = arr[j] for some j with 0 <= j < len(arr), and r = 1 otherwise.
  Preconditions: target and arr satisfy the problem constraints: 1 <= len(target) <= 100000, 1 <= len(arr) <= 100000, every target[i] and arr[j] lies in [1, 1000000000], target has no duplicate values, and len(target) = 1. -/
theorem spec_7 (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target))
    (h_len_one : target.val.length = 1) :
    ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      (r.val = 0 ↔
        ∃ (j : ℕ) (hj : j < arr.val.length),
          (arr.val.get ⟨j, hj⟩).val = firstVal (vals target)) ∧
      (r.val = 1 ↔
        ∀ (j : ℕ) (hj : j < arr.val.length),
          (arr.val.get ⟨j, hj⟩).val ≠ firstVal (vals target)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target))
    (h_len_one : target.val.length = 1), ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      (r.val = 0 ↔
        ∃ (j : ℕ) (hj : j < arr.val.length),
          (arr.val.get ⟨j, hj⟩).val = firstVal (vals target)) ∧
      (r.val = 1 ↔
        ∀ (j : ℕ) (hj : j < arr.val.length),
          (arr.val.get ⟨j, hj⟩).val ≠ firstVal (vals target))) := by
  sorry

/-- The function returns a result r and there exists an array a' of integers with len(a') = len(arr) + r such that arr is a subsequence of a' and target is a subsequence of a'.
  Preconditions: target and arr satisfy the problem constraints: 1 <= len(target) <= 100000, 1 <= len(arr) <= 100000, every target[i] and arr[j] lies in [1, 1000000000], and target has no duplicate values. -/
theorem spec_8 (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)) :
    ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      ∃ a' : List ℤ,
        ((a'.length : ℕ) : ℤ) = ((arr.val.length : ℕ) : ℤ) + r.val ∧
        IsSubseq (vals arr) a' ∧ IsSubseq (vals target) a' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)), ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      ∃ a' : List ℤ,
        ((a'.length : ℕ) : ℤ) = ((arr.val.length : ℕ) : ℤ) + r.val ∧
        IsSubseq (vals arr) a' ∧ IsSubseq (vals target) a') := by
  sorry

/-- The function returns a result r and for every integer k with 0 <= k < r there is no array a' of integers with len(a') = len(arr) + k such that both arr is a subsequence of a' and target is a subsequence of a'.
  Preconditions: target and arr satisfy the problem constraints: 1 <= len(target) <= 100000, 1 <= len(arr) <= 100000, every target[i] and arr[j] lies in [1, 1000000000], and target has no duplicate values. -/
theorem spec_9 (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)) :
    ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      ∀ k : ℕ, 0 ≤ k → ((k : ℕ) : ℤ) < r.val →
        ¬ ∃ a' : List ℤ,
          ((a'.length : ℕ) : ℤ) = ((arr.val.length : ℕ) : ℤ) + ((k : ℕ) : ℤ) ∧
          IsSubseq (vals arr) a' ∧ IsSubseq (vals target) a' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)), ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      ∀ k : ℕ, 0 ≤ k → ((k : ℕ) : ℤ) < r.val →
        ¬ ∃ a' : List ℤ,
          ((a'.length : ℕ) : ℤ) = ((arr.val.length : ℕ) : ℤ) + ((k : ℕ) : ℤ) ∧
          IsSubseq (vals arr) a' ∧ IsSubseq (vals target) a') := by
  sorry

/-- The function returns a result r and for every k >= 0 and every choice of indices 0 <= i_0 < ... < i_{k-1} < len(target) and 0 <= j_0 < ... < j_{k-1} < len(arr) satisfying target[i_t] = arr[j_t] for all 0 <= t < k, one has r <= len(target) - k.
  Preconditions: target and arr satisfy the problem constraints: 1 <= len(target) <= 100000, 1 <= len(arr) <= 100000, every target[i] and arr[j] lies in [1, 1000000000], and target has no duplicate values. -/
theorem spec_10 (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)) :
    ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      ∀ k : ℕ, IsCommonSubseq (vals target) (vals arr) k →
        r.val ≤ ((target.val.length : ℕ) : ℤ) - ((k : ℕ) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)), ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      ∀ k : ℕ, IsCommonSubseq (vals target) (vals arr) k →
        r.val ≤ ((target.val.length : ℕ) : ℤ) - ((k : ℕ) : ℤ)) := by
  sorry

/-- The function returns r1 on input (target, arr1) and r2 on input (target, arr2), and r2 <= r1.
  Preconditions: target, arr1, and arr2 satisfy the problem constraints: each array has length in [1, 100000] and all elements in [1, 1000000000], target has no duplicate values, and arr1 is a subsequence of arr2 (there exist 0 <= q_0 < ... < q_{len(arr1)-1} < len(arr2) with arr2[q_t] = arr1[t] for all 0 <= t < len(arr1)). -/
theorem spec_11 (target arr1 arr2 : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m1_pos : 1 ≤ arr1.val.length) (h_m1_le : arr1.val.length ≤ 100000)
    (h_m2_pos : 1 ≤ arr2.val.length) (h_m2_le : arr2.val.length ≤ 100000)
    (h_target_range : InRange (vals target))
    (h_arr1_range : InRange (vals arr1)) (h_arr2_range : InRange (vals arr2))
    (h_target_nodup : NoDupVals (vals target))
    (h_sub : IsSubseq (vals arr1) (vals arr2)) :
    ∃ r1 r2 : I64, Aegis.MinOperations.min_operations target arr1 = ok r1 ∧
      Aegis.MinOperations.min_operations target arr2 = ok r2 ∧ r2.val ≤ r1.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (target arr1 arr2 : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m1_pos : 1 ≤ arr1.val.length) (h_m1_le : arr1.val.length ≤ 100000)
    (h_m2_pos : 1 ≤ arr2.val.length) (h_m2_le : arr2.val.length ≤ 100000)
    (h_target_range : InRange (vals target))
    (h_arr1_range : InRange (vals arr1)) (h_arr2_range : InRange (vals arr2))
    (h_target_nodup : NoDupVals (vals target))
    (h_sub : IsSubseq (vals arr1) (vals arr2)), ∃ r1 r2 : I64, Aegis.MinOperations.min_operations target arr1 = ok r1 ∧
      Aegis.MinOperations.min_operations target arr2 = ok r2 ∧ r2.val ≤ r1.val) := by
  sorry

/-- The function returns r on input (target, arr) and r' on input (target, arr'), and r' = r.
  Preconditions: target and arr satisfy the problem constraints. Let v be an integer with 1 <= v <= 1000000000 such that v != target[i] for every i with 0 <= i < len(target). Let arr' = arr ++ [v], and assume len(arr) < 100000 so that len(arr') <= 100000. -/
theorem spec_12 (target arr arr' : Slice I64) (v : ℤ)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_lt : arr.val.length < 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target))
    (h_v_range : 1 ≤ v ∧ v ≤ 1000000000)
    (h_v_absent : ∀ (i : ℕ) (hi : i < target.val.length),
      (target.val.get ⟨i, hi⟩).val ≠ v)
    (h_arr' : vals arr' = vals arr ++ [v]) :
    ∃ r r' : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      Aegis.MinOperations.min_operations target arr' = ok r' ∧ r'.val = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (target arr arr' : Slice I64) (v : ℤ)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_lt : arr.val.length < 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target))
    (h_v_range : 1 ≤ v ∧ v ≤ 1000000000)
    (h_v_absent : ∀ (i : ℕ) (hi : i < target.val.length),
      (target.val.get ⟨i, hi⟩).val ≠ v)
    (h_arr' : vals arr' = vals arr ++ [v]), ∃ r r' : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      Aegis.MinOperations.min_operations target arr' = ok r' ∧ r'.val = r.val) := by
  sorry

/-- The function returns r on input (target, arr) and r' on input (target', arr'), and r' = r.
  Preconditions: target and arr satisfy the problem constraints. Let U be the set of all values appearing in target or arr. Let f be an injective function from U into [1, 1000000000]. Define target'[i] = f(target[i]) for 0 <= i < len(target) and arr'[j] = f(arr[j]) for 0 <= j < len(arr). -/
theorem spec_13 (target arr target' arr' : Slice I64) (f : ℤ → ℤ)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target))
    (h_f_inj : ∀ x ∈ vals target ++ vals arr, ∀ y ∈ vals target ++ vals arr,
      f x = f y → x = y)
    (h_f_range : ∀ x ∈ vals target ++ vals arr, 1 ≤ f x ∧ f x ≤ 1000000000)
    (h_target' : vals target' = (vals target).map f)
    (h_arr' : vals arr' = (vals arr).map f) :
    ∃ r r' : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      Aegis.MinOperations.min_operations target' arr' = ok r' ∧ r'.val = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (target arr target' arr' : Slice I64) (f : ℤ → ℤ)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target))
    (h_f_inj : ∀ x ∈ vals target ++ vals arr, ∀ y ∈ vals target ++ vals arr,
      f x = f y → x = y)
    (h_f_range : ∀ x ∈ vals target ++ vals arr, 1 ≤ f x ∧ f x ≤ 1000000000)
    (h_target' : vals target' = (vals target).map f)
    (h_arr' : vals arr' = (vals arr).map f), ∃ r r' : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      Aegis.MinOperations.min_operations target' arr' = ok r' ∧ r'.val = r.val) := by
  sorry

/-- Let P be the sequence obtained by scanning arr from left to right and appending i whenever arr[j] = target[i]; elements arr[j] not equal to any target value are skipped. Let I(P) be the length of a longest strictly increasing subsequence of P, with I(P) = 0 when P is empty. The function returns a result r and r = len(target) - I(P).
  Preconditions: target and arr satisfy the problem constraints: 1 <= len(target), len(arr) <= 100000, every target[i] and arr[j] lies in [1, 1000000000], and target has no duplicate values. -/
theorem spec_14 (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)) :
    ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      r.val = ((target.val.length : ℕ) : ℤ) -
        ((lisLen (Pseq (vals target) (vals arr)) : ℕ) : ℤ) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_n_pos : 1 ≤ target.val.length) (h_n_le : target.val.length ≤ 100000)
    (h_m_pos : 1 ≤ arr.val.length) (h_m_le : arr.val.length ≤ 100000)
    (h_target_range : InRange (vals target)) (h_arr_range : InRange (vals arr))
    (h_target_nodup : NoDupVals (vals target)), ∃ r : I64, Aegis.MinOperations.min_operations target arr = ok r ∧
      r.val = ((target.val.length : ℕ) : ℤ) -
        ((lisLen (Pseq (vals target) (vals arr)) : ℕ) : ℤ)) := by
  sorry

end AegisSpec.MinOperations
