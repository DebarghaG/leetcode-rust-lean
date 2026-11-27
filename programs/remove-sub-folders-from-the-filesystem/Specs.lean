import Aegis.RemoveSubfolders.Code.Funs

/-!
# Specifications of `Aegis.RemoveSubfolders.remove_subfolders`

LeetCode problem `remove-sub-folders-from-the-filesystem`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RemoveSubfolders

def slash : Std.U8 := 47#u8

def AtSlash (p : List Std.U8) (n : Nat) : Prop := p[n]? = some slash

def AtLower (p : List Std.U8) (n : Nat) : Prop := ∃ b, p[n]? = some b ∧ 97 ≤ b.val ∧ b.val ≤ 122

def IsValidPath (p : List Std.U8) : Prop :=
  2 ≤ p.length ∧ p.length ≤ 100 ∧
    AtSlash p 0 ∧
    (∀ n, n < p.length → AtSlash p n ∨ AtLower p n) ∧
    (∀ n, ¬ (AtSlash p n ∧ AtSlash p (n + 1))) ∧
    ¬ AtSlash p (p.length - 1)

def PairwiseDistinct (l : List (List Std.U8)) : Prop := l.Pairwise (fun a b => a ≠ b)

def Subfolder (p q : List Std.U8) : Prop :=
  q.length < p.length ∧ p.take q.length = q ∧ p[q.length]? = some slash

def pathAt (folder : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : List Std.U8 :=
  match folder.val[i]? with
  | some v => v.val
  | none => []

def resAt (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (k : Nat) : List Std.U8 :=
  match r.val[k]? with
  | some v => v.val
  | none => []

def pathList (folder : Slice (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
  folder.val.map (fun v => v.val)

def resultList (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
  r.val.map (fun v => v.val)

def countOcc (p : List Std.U8) : List (List Std.U8) → Nat
  | [] => 0
  | q :: qs => (if q = p then 1 else 0) + countOcc p qs

open Classical in

noncomputable def countIdx (n : Nat) (P : Nat → Prop) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => (if P k then 1 else 0) + countIdx k P

def NotUnderAny (folder : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : Prop :=
  ∀ j, j < folder.val.length → ¬ Subfolder (pathAt folder i) (pathAt folder j)

/-- Whenever the function returns a result r, define p ≺ q to mean that p is a sub-folder of q: len(q) < len(p), p[0..len(q)] = q, and p[len(q)] = '/' (the byte immediately after the prefix q is a slash). Then for every byte string p, the number of indices k with 0 <= k < len(r) and r[k] = p is 1 exactly when there exists i with 0 <= i < len(folder) such that p = folder[i] and for every j with 0 <= j < len(folder) it is not the case that folder[i] ≺ folder[j]; for all other p that number is 0.
  Preconditions: 1 <= len(folder) <= 40000. For every i with 0 <= i < len(folder), folder[i] is a valid path in the sense of the statement: 2 <= len(folder[i]) <= 100, the first byte of folder[i] is '/', and folder[i] has the form '/' followed by one or more lowercase English letters, then zero or more repetitions of '/' followed by one or more lowercase English letters; equivalently, every byte is '/' or a lowercase letter, no two '/' bytes are adjacent, and the last byte is not '/'. The paths folder[i] are pairwise distinct. -/
theorem spec_1
    (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)) :
    ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ p : List Std.U8,
        (countOcc p (resultList r) = 1 ↔
            ∃ i, i < folder.val.length ∧ p = pathAt folder i ∧ NotUnderAny folder i) ∧
        (¬ (∃ i, i < folder.val.length ∧ p = pathAt folder i ∧ NotUnderAny folder i) →
          countOcc p (resultList r) = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)), ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ p : List Std.U8,
        (countOcc p (resultList r) = 1 ↔
            ∃ i, i < folder.val.length ∧ p = pathAt folder i ∧ NotUnderAny folder i) ∧
        (¬ (∃ i, i < folder.val.length ∧ p = pathAt folder i ∧ NotUnderAny folder i) →
          countOcc p (resultList r) = 0)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: 1 <= len(folder) <= 40000. For every i with 0 <= i < len(folder), folder[i] is a valid path in the sense of the statement: 2 <= len(folder[i]) <= 100, the first byte of folder[i] is '/', and folder[i] has the form '/' followed by one or more lowercase English letters, then zero or more repetitions of '/' followed by one or more lowercase English letters; equivalently, every byte is '/' or a lowercase letter, no two '/' bytes are adjacent, and the last byte is not '/'. The paths folder[i] are pairwise distinct. -/
theorem spec_2
    (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)) :
    ∃ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)), ∃ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r) := by
  sorry

/-- Whenever the function returns r, for every k with 0 <= k < len(r), there exists i with 0 <= i < len(folder) such that r[k] = folder[i], comparing byte vectors elementwise.
  Preconditions: 1 <= len(folder) <= 40000. For every i with 0 <= i < len(folder), folder[i] is a valid path in the sense of the statement: 2 <= len(folder[i]) <= 100, the first byte of folder[i] is '/', and folder[i] has the form '/' followed by one or more lowercase English letters, then zero or more repetitions of '/' followed by one or more lowercase English letters; equivalently, every byte is '/' or a lowercase letter, no two '/' bytes are adjacent, and the last byte is not '/'. The paths folder[i] are pairwise distinct. -/
theorem spec_3
    (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)) :
    ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ k, k < r.val.length → ∃ i, i < folder.val.length ∧ resAt r k = pathAt folder i := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)), ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ k, k < r.val.length → ∃ i, i < folder.val.length ∧ resAt r k = pathAt folder i) := by
  sorry

/-- Whenever the function returns r, for every a and b with 0 <= a < b < len(r), r[a] ≠ r[b].
  Preconditions: 1 <= len(folder) <= 40000. For every i with 0 <= i < len(folder), folder[i] is a valid path in the sense of the statement: 2 <= len(folder[i]) <= 100, the first byte of folder[i] is '/', and folder[i] has the form '/' followed by one or more lowercase English letters, then zero or more repetitions of '/' followed by one or more lowercase English letters; equivalently, every byte is '/' or a lowercase letter, no two '/' bytes are adjacent, and the last byte is not '/'. The paths folder[i] are pairwise distinct. -/
theorem spec_4
    (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)) :
    ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ a b, a < b → b < r.val.length → resAt r a ≠ resAt r b := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)), ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ a b, a < b → b < r.val.length → resAt r a ≠ resAt r b) := by
  sorry

/-- Whenever the function returns r, define p ≺ q as len(q) < len(p), p[0..len(q)] = q, and p[len(q)] = '/'. For every k with 0 <= k < len(r) and every j with 0 <= j < len(folder), it is not the case that r[k] ≺ folder[j].
  Preconditions: 1 <= len(folder) <= 40000. For every i with 0 <= i < len(folder), folder[i] is a valid path in the sense of the statement: 2 <= len(folder[i]) <= 100, the first byte of folder[i] is '/', and folder[i] has the form '/' followed by one or more lowercase English letters, then zero or more repetitions of '/' followed by one or more lowercase English letters; equivalently, every byte is '/' or a lowercase letter, no two '/' bytes are adjacent, and the last byte is not '/'. The paths folder[i] are pairwise distinct. -/
theorem spec_5
    (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)) :
    ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ k, k < r.val.length → ∀ j, j < folder.val.length →
        ¬ Subfolder (resAt r k) (pathAt folder j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)), ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ k, k < r.val.length → ∀ j, j < folder.val.length →
        ¬ Subfolder (resAt r k) (pathAt folder j)) := by
  sorry

/-- Whenever the function returns r, define p ≺ q as len(q) < len(p), p[0..len(q)] = q, and p[len(q)] = '/'. For every i with 0 <= i < len(folder), if for every j with 0 <= j < len(folder) it is not the case that folder[i] ≺ folder[j], then there exists k with 0 <= k < len(r) such that r[k] = folder[i].
  Preconditions: 1 <= len(folder) <= 40000. For every i with 0 <= i < len(folder), folder[i] is a valid path in the sense of the statement: 2 <= len(folder[i]) <= 100, the first byte of folder[i] is '/', and folder[i] has the form '/' followed by one or more lowercase English letters, then zero or more repetitions of '/' followed by one or more lowercase English letters; equivalently, every byte is '/' or a lowercase letter, no two '/' bytes are adjacent, and the last byte is not '/'. The paths folder[i] are pairwise distinct. -/
theorem spec_6
    (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)) :
    ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ i, i < folder.val.length → NotUnderAny folder i →
        ∃ k, k < r.val.length ∧ resAt r k = pathAt folder i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)), ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ i, i < folder.val.length → NotUnderAny folder i →
        ∃ k, k < r.val.length ∧ resAt r k = pathAt folder i) := by
  sorry

/-- Whenever the function returns r, define p ≺ q as len(q) < len(p), p[0..len(q)] = q, and p[len(q)] = '/'. Then len(r) equals the number of indices i with 0 <= i < len(folder) such that for every j with 0 <= j < len(folder) it is not the case that folder[i] ≺ folder[j].
  Preconditions: 1 <= len(folder) <= 40000. For every i with 0 <= i < len(folder), folder[i] is a valid path in the sense of the statement: 2 <= len(folder[i]) <= 100, the first byte of folder[i] is '/', and folder[i] has the form '/' followed by one or more lowercase English letters, then zero or more repetitions of '/' followed by one or more lowercase English letters; equivalently, every byte is '/' or a lowercase letter, no two '/' bytes are adjacent, and the last byte is not '/'. The paths folder[i] are pairwise distinct. -/
theorem spec_7
    (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)) :
    ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      r.val.length = countIdx folder.val.length (NotUnderAny folder) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)), ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      r.val.length = countIdx folder.val.length (NotUnderAny folder)) := by
  sorry

/-- Whenever the function returns r, 1 <= len(r) <= len(folder).
  Preconditions: 1 <= len(folder) <= 40000. For every i with 0 <= i < len(folder), folder[i] is a valid path in the sense of the statement: 2 <= len(folder[i]) <= 100, the first byte of folder[i] is '/', and folder[i] has the form '/' followed by one or more lowercase English letters, then zero or more repetitions of '/' followed by one or more lowercase English letters; equivalently, every byte is '/' or a lowercase letter, no two '/' bytes are adjacent, and the last byte is not '/'. The paths folder[i] are pairwise distinct. -/
theorem spec_8
    (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)) :
    ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      1 ≤ r.val.length ∧ r.val.length ≤ folder.val.length := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)), ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      1 ≤ r.val.length ∧ r.val.length ≤ folder.val.length) := by
  sorry

/-- Whenever the function returns r, define p ≺ q as len(q) < len(p), p[0..len(q)] = q, and p[len(q)] = '/'. If for every i and j with 0 <= i < len(folder) and 0 <= j < len(folder) it is not the case that folder[i] ≺ folder[j], then r is a permutation of folder: len(r) = len(folder), and for every i with 0 <= i < len(folder) there is exactly one k with 0 <= k < len(r) and r[k] = folder[i].
  Preconditions: 1 <= len(folder) <= 40000. For every i with 0 <= i < len(folder), folder[i] is a valid path in the sense of the statement: 2 <= len(folder[i]) <= 100, the first byte of folder[i] is '/', and folder[i] has the form '/' followed by one or more lowercase English letters, then zero or more repetitions of '/' followed by one or more lowercase English letters; equivalently, every byte is '/' or a lowercase letter, no two '/' bytes are adjacent, and the last byte is not '/'. The paths folder[i] are pairwise distinct. -/
theorem spec_9
    (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)) :
    ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      (∀ i j, i < folder.val.length → j < folder.val.length →
          ¬ Subfolder (pathAt folder i) (pathAt folder j)) →
        r.val.length = folder.val.length ∧
          ∀ i, i < folder.val.length → ∃! k, k < r.val.length ∧ resAt r k = pathAt folder i := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)), ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      (∀ i j, i < folder.val.length → j < folder.val.length →
          ¬ Subfolder (pathAt folder i) (pathAt folder j)) →
        r.val.length = folder.val.length ∧
          ∀ i, i < folder.val.length → ∃! k, k < r.val.length ∧ resAt r k = pathAt folder i) := by
  sorry

/-- Whenever the function returns r, define p ≺ q as len(q) < len(p), p[0..len(q)] = q, and p[len(q)] = '/'. If there exists j with 0 <= j < len(folder) such that for every i with 0 <= i < len(folder) and i ≠ j, folder[i] ≺ folder[j], then len(r) = 1 and r[0] = folder[j].
  Preconditions: 1 <= len(folder) <= 40000. For every i with 0 <= i < len(folder), folder[i] is a valid path in the sense of the statement: 2 <= len(folder[i]) <= 100, the first byte of folder[i] is '/', and folder[i] has the form '/' followed by one or more lowercase English letters, then zero or more repetitions of '/' followed by one or more lowercase English letters; equivalently, every byte is '/' or a lowercase letter, no two '/' bytes are adjacent, and the last byte is not '/'. The paths folder[i] are pairwise distinct. -/
theorem spec_10
    (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)) :
    ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ j, j < folder.val.length →
        (∀ i, i < folder.val.length → i ≠ j → Subfolder (pathAt folder i) (pathAt folder j)) →
          r.val.length = 1 ∧ ∀ k, k < r.val.length → resAt r k = pathAt folder j := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)), ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ j, j < folder.val.length →
        (∀ i, i < folder.val.length → i ≠ j → Subfolder (pathAt folder i) (pathAt folder j)) →
          r.val.length = 1 ∧ ∀ k, k < r.val.length → resAt r k = pathAt folder j) := by
  sorry

/-- Whenever the function returns r, define p ≺ q as len(q) < len(p), p[0..len(q)] = q, and p[len(q)] = '/'. For every i with 0 <= i < len(folder), if there is no k with 0 <= k < len(r) such that r[k] = folder[i], then there exists k with 0 <= k < len(r) such that folder[i] ≺ r[k].
  Preconditions: 1 <= len(folder) <= 40000. For every i with 0 <= i < len(folder), folder[i] is a valid path in the sense of the statement: 2 <= len(folder[i]) <= 100, the first byte of folder[i] is '/', and folder[i] has the form '/' followed by one or more lowercase English letters, then zero or more repetitions of '/' followed by one or more lowercase English letters; equivalently, every byte is '/' or a lowercase letter, no two '/' bytes are adjacent, and the last byte is not '/'. The paths folder[i] are pairwise distinct. -/
theorem spec_11
    (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)) :
    ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ i, i < folder.val.length →
        (∀ k, k < r.val.length → resAt r k ≠ pathAt folder i) →
          ∃ k, k < r.val.length ∧ Subfolder (pathAt folder i) (resAt r k) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (folder : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder)), ∀ r, Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      ∀ i, i < folder.val.length →
        (∀ k, k < r.val.length → resAt r k ≠ pathAt folder i) →
          ∃ k, k < r.val.length ∧ Subfolder (pathAt folder i) (resAt r k)) := by
  sorry

/-- Whenever the function returns r on input folder and returns r' on input folder', for every byte string p, the number of indices k with 0 <= k < len(r) and r[k] = p equals the number of indices k with 0 <= k < len(r') and r'[k] = p.
  Preconditions: Both folder and folder' satisfy the input constraints: 1 <= len <= 40000, every path is a valid path of length 2..100 as in the problem statement, and paths within each list are pairwise distinct. Moreover, folder' is a permutation of folder: for every byte string p, the number of indices i with 0 <= i < len(folder) and folder[i] = p equals the number of indices i with 0 <= i < len(folder') and folder'[i] = p. -/
theorem spec_12
    (folder folder' : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder))
    (h_len_pos' : 1 ≤ folder'.val.length)
    (h_len_le' : folder'.val.length ≤ 40000)
    (h_valid' : ∀ i, i < folder'.val.length → IsValidPath (pathAt folder' i))
    (h_distinct' : PairwiseDistinct (pathList folder'))
    (h_perm : ∀ p : List Std.U8, countOcc p (pathList folder) = countOcc p (pathList folder')) :
    ∀ r r', Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      Aegis.RemoveSubfolders.remove_subfolders folder' = ok r' →
        ∀ p : List Std.U8, countOcc p (resultList r) = countOcc p (resultList r') := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (folder folder' : Slice (alloc.vec.Vec Std.U8))
    (h_len_pos : 1 ≤ folder.val.length)
    (h_len_le : folder.val.length ≤ 40000)
    (h_valid : ∀ i, i < folder.val.length → IsValidPath (pathAt folder i))
    (h_distinct : PairwiseDistinct (pathList folder))
    (h_len_pos' : 1 ≤ folder'.val.length)
    (h_len_le' : folder'.val.length ≤ 40000)
    (h_valid' : ∀ i, i < folder'.val.length → IsValidPath (pathAt folder' i))
    (h_distinct' : PairwiseDistinct (pathList folder'))
    (h_perm : ∀ p : List Std.U8, countOcc p (pathList folder) = countOcc p (pathList folder')), ∀ r r', Aegis.RemoveSubfolders.remove_subfolders folder = ok r →
      Aegis.RemoveSubfolders.remove_subfolders folder' = ok r' →
        ∀ p : List Std.U8, countOcc p (resultList r) = countOcc p (resultList r')) := by
  sorry

end AegisSpec.RemoveSubfolders
