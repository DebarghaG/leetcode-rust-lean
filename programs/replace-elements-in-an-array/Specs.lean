import Aegis.ArrayChange.Code.Funs

/-!
# Specifications of `Aegis.ArrayChange.array_change`

LeetCode problem `replace-elements-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ArrayChange

  abbrev SliceI64 := Aeneas.Std.Slice Aeneas.Std.I64

  abbrev SliceOps := Aeneas.Std.Slice (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

  abbrev VecI64 := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

  def sliceContents (s : SliceI64) : List Int := s.val.map (fun x => x.val)

  def vecContents (v : VecI64) : List Int := v.val.map (fun x => x.val)

  def opList (operations : SliceOps) (k : Nat) : List Int :=
    (operations.val.map vecContents).getD k []

  def opKey (operations : SliceOps) (k : Nat) : Int := (opList operations k).getD 0 0

  def opVal (operations : SliceOps) (k : Nat) : Int := (opList operations k).getD 1 0

  def applyOp (a b : Int) (l : List Int) : List Int := l.map (fun v => if v = a then b else v)

  def arrAt (nums : SliceI64) (operations : SliceOps) : Nat → List Int
    | 0 => sliceContents nums
    | k + 1 => applyOp (opKey operations k) (opVal operations k) (arrAt nums operations k)

  def countOcc (x : Int) (l : List Int) : Nat := (l.filter (fun v => decide (v = x))).length

  def Occurs (x : Int) (l : List Int) : Prop := ∃ j, j < l.length ∧ l.getD j 0 = x

  def numDiff (a b : List Int) (n : Nat) : Nat :=
    ((List.range n).filter (fun i => decide (a.getD i 0 ≠ b.getD i 0))).length

  /-- Whenever array_change returns a result r, r is exactly the array A_m defined in the preconditions: len(r) = len(nums) and for every i with 0 <= i < len(nums), r[i] = A_m[i].
    Preconditions: Let m = len(operations). Define A_0 = nums and, for 0 <= k < m, define A_{k+1} by: for every 0 <= i < len(nums), A_{k+1}[i] = operations[k][1] if A_k[i] = operations[k][0], and A_{k+1}[i] = A_k[i] otherwise. Assume 1 <= len(nums) <= 10^5; 1 <= m <= 10^5; all entries of nums are distinct and satisfy 1 <= nums[i] <= 10^6; each operations[k] has length exactly 2 and 1 <= operations[k][0] <= 10^6 and 1 <= operations[k][1] <= 10^6; and for every 0 <= k < m, operations[k][0] occurs exactly once in A_k while operations[k][1] occurs zero times in A_k. -/
  theorem spec_1
      (nums : SliceI64) (operations : SliceOps)
      (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
      (hnodup : (sliceContents nums).Nodup)
      (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hkeyocc : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums operations k) = 1)
      (hvalocc : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums operations k) = 0) :
      ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
        (vecContents r).length = (sliceContents nums).length ∧
          ∀ i, i < (sliceContents nums).length →
            (vecContents r).getD i 0
              = (arrAt nums operations operations.val.length).getD i 0 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : SliceI64) (operations : SliceOps)
        (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
        (hnodup : (sliceContents nums).Nodup)
        (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hkeyocc : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums operations k) = 1)
        (hvalocc : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums operations k) = 0), ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
          (vecContents r).length = (sliceContents nums).length ∧
            ∀ i, i < (sliceContents nums).length →
              (vecContents r).getD i 0
                = (arrAt nums operations operations.val.length).getD i 0) := by
    sorry

  /-- array_change returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
    Preconditions: Let m = len(operations). Define A_0 = nums and, for 0 <= k < m, define A_{k+1} by: for every 0 <= i < len(nums), A_{k+1}[i] = operations[k][1] if A_k[i] = operations[k][0], and A_{k+1}[i] = A_k[i] otherwise. Assume 1 <= len(nums) <= 10^5; 1 <= m <= 10^5; all entries of nums are distinct and satisfy 1 <= nums[i] <= 10^6; each operations[k] has length exactly 2 and 1 <= operations[k][0] <= 10^6 and 1 <= operations[k][1] <= 10^6; and for every 0 <= k < m, operations[k][0] occurs exactly once in A_k while operations[k][1] occurs zero times in A_k. -/
  theorem spec_2
      (nums : SliceI64) (operations : SliceOps)
      (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
      (hnodup : (sliceContents nums).Nodup)
      (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hkeyocc : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums operations k) = 1)
      (hvalocc : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums operations k) = 0) :
      ∃ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : SliceI64) (operations : SliceOps)
        (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
        (hnodup : (sliceContents nums).Nodup)
        (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hkeyocc : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums operations k) = 1)
        (hvalocc : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums operations k) = 0), ∃ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r) := by
    sorry

  /-- Whenever array_change returns a result r, for every i with 0 <= i < len(r), 1 <= r[i] <= 10^6.
    Preconditions: Let m = len(operations). Define A_0 = nums and, for 0 <= k < m, define A_{k+1} by: for every 0 <= i < len(nums), A_{k+1}[i] = operations[k][1] if A_k[i] = operations[k][0], and A_{k+1}[i] = A_k[i] otherwise. Assume 1 <= len(nums) <= 10^5; 1 <= m <= 10^5; all entries of nums are distinct and satisfy 1 <= nums[i] <= 10^6; each operations[k] has length exactly 2 and 1 <= operations[k][0] <= 10^6 and 1 <= operations[k][1] <= 10^6; and for every 0 <= k < m, operations[k][0] occurs exactly once in A_k while operations[k][1] occurs zero times in A_k. -/
  theorem spec_3
      (nums : SliceI64) (operations : SliceOps)
      (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
      (hnodup : (sliceContents nums).Nodup)
      (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hkeyocc : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums operations k) = 1)
      (hvalocc : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums operations k) = 0) :
      ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
        ∀ i, i < (vecContents r).length →
          1 ≤ (vecContents r).getD i 0 ∧ (vecContents r).getD i 0 ≤ 1000000 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : SliceI64) (operations : SliceOps)
        (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
        (hnodup : (sliceContents nums).Nodup)
        (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hkeyocc : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums operations k) = 1)
        (hvalocc : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums operations k) = 0), ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
          ∀ i, i < (vecContents r).length →
            1 ≤ (vecContents r).getD i 0 ∧ (vecContents r).getD i 0 ≤ 1000000) := by
    sorry

  /-- Whenever array_change returns a result r, its entries are pairwise distinct: for all i and j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: Let m = len(operations). Define A_0 = nums and, for 0 <= k < m, define A_{k+1} by: for every 0 <= i < len(nums), A_{k+1}[i] = operations[k][1] if A_k[i] = operations[k][0], and A_{k+1}[i] = A_k[i] otherwise. Assume 1 <= len(nums) <= 10^5; 1 <= m <= 10^5; all entries of nums are distinct and satisfy 1 <= nums[i] <= 10^6; each operations[k] has length exactly 2 and 1 <= operations[k][0] <= 10^6 and 1 <= operations[k][1] <= 10^6; and for every 0 <= k < m, operations[k][0] occurs exactly once in A_k while operations[k][1] occurs zero times in A_k. -/
  theorem spec_4
      (nums : SliceI64) (operations : SliceOps)
      (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
      (hnodup : (sliceContents nums).Nodup)
      (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hkeyocc : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums operations k) = 1)
      (hvalocc : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums operations k) = 0) :
      ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
        ∀ i j, i < j → j < (vecContents r).length →
          (vecContents r).getD i 0 ≠ (vecContents r).getD j 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : SliceI64) (operations : SliceOps)
        (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
        (hnodup : (sliceContents nums).Nodup)
        (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hkeyocc : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums operations k) = 1)
        (hvalocc : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums operations k) = 0), ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
          ∀ i j, i < j → j < (vecContents r).length →
            (vecContents r).getD i 0 ≠ (vecContents r).getD j 0) := by
    sorry

  /-- Whenever array_change returns a result r, for every i with 0 <= i < len(nums), if nums[i] is not equal to operations[k][0] for every k with 0 <= k < len(operations), then r[i] = nums[i].
    Preconditions: Let m = len(operations). Define A_0 = nums and, for 0 <= k < m, define A_{k+1} by: for every 0 <= i < len(nums), A_{k+1}[i] = operations[k][1] if A_k[i] = operations[k][0], and A_{k+1}[i] = A_k[i] otherwise. Assume 1 <= len(nums) <= 10^5; 1 <= m <= 10^5; all entries of nums are distinct and satisfy 1 <= nums[i] <= 10^6; each operations[k] has length exactly 2 and 1 <= operations[k][0] <= 10^6 and 1 <= operations[k][1] <= 10^6; and for every 0 <= k < m, operations[k][0] occurs exactly once in A_k while operations[k][1] occurs zero times in A_k. -/
  theorem spec_5
      (nums : SliceI64) (operations : SliceOps)
      (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
      (hnodup : (sliceContents nums).Nodup)
      (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hkeyocc : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums operations k) = 1)
      (hvalocc : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums operations k) = 0) :
      ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
        ∀ i, i < (sliceContents nums).length →
          (∀ k, k < operations.val.length → (sliceContents nums).getD i 0 ≠ opKey operations k) →
            (vecContents r).getD i 0 = (sliceContents nums).getD i 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : SliceI64) (operations : SliceOps)
        (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
        (hnodup : (sliceContents nums).Nodup)
        (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hkeyocc : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums operations k) = 1)
        (hvalocc : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums operations k) = 0), ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
          ∀ i, i < (sliceContents nums).length →
            (∀ k, k < operations.val.length → (sliceContents nums).getD i 0 ≠ opKey operations k) →
              (vecContents r).getD i 0 = (sliceContents nums).getD i 0) := by
    sorry

  /-- Whenever array_change returns a result r, for every k with 0 <= k < len(operations), if operations[k][1] is not equal to operations[j][0] for every j with k < j < len(operations), then the value operations[k][1] occurs exactly once in r.
    Preconditions: Let m = len(operations). Define A_0 = nums and, for 0 <= k < m, define A_{k+1} by: for every 0 <= i < len(nums), A_{k+1}[i] = operations[k][1] if A_k[i] = operations[k][0], and A_{k+1}[i] = A_k[i] otherwise. Assume 1 <= len(nums) <= 10^5; 1 <= m <= 10^5; all entries of nums are distinct and satisfy 1 <= nums[i] <= 10^6; each operations[k] has length exactly 2 and 1 <= operations[k][0] <= 10^6 and 1 <= operations[k][1] <= 10^6; and for every 0 <= k < m, operations[k][0] occurs exactly once in A_k while operations[k][1] occurs zero times in A_k. -/
  theorem spec_6
      (nums : SliceI64) (operations : SliceOps)
      (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
      (hnodup : (sliceContents nums).Nodup)
      (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hkeyocc : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums operations k) = 1)
      (hvalocc : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums operations k) = 0) :
      ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
        ∀ k, k < operations.val.length →
          (∀ j, k < j → j < operations.val.length → opVal operations k ≠ opKey operations j) →
            countOcc (opVal operations k) (vecContents r) = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : SliceI64) (operations : SliceOps)
        (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
        (hnodup : (sliceContents nums).Nodup)
        (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hkeyocc : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums operations k) = 1)
        (hvalocc : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums operations k) = 0), ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
          ∀ k, k < operations.val.length →
            (∀ j, k < j → j < operations.val.length → opVal operations k ≠ opKey operations j) →
              countOcc (opVal operations k) (vecContents r) = 1) := by
    sorry

  /-- Whenever array_change returns a result r, for every k with 0 <= k < len(operations), if operations[k][0] is not equal to operations[j][1] for every j with k < j < len(operations), then the value operations[k][0] does not occur in r.
    Preconditions: Let m = len(operations). Define A_0 = nums and, for 0 <= k < m, define A_{k+1} by: for every 0 <= i < len(nums), A_{k+1}[i] = operations[k][1] if A_k[i] = operations[k][0], and A_{k+1}[i] = A_k[i] otherwise. Assume 1 <= len(nums) <= 10^5; 1 <= m <= 10^5; all entries of nums are distinct and satisfy 1 <= nums[i] <= 10^6; each operations[k] has length exactly 2 and 1 <= operations[k][0] <= 10^6 and 1 <= operations[k][1] <= 10^6; and for every 0 <= k < m, operations[k][0] occurs exactly once in A_k while operations[k][1] occurs zero times in A_k. -/
  theorem spec_7
      (nums : SliceI64) (operations : SliceOps)
      (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
      (hnodup : (sliceContents nums).Nodup)
      (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hkeyocc : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums operations k) = 1)
      (hvalocc : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums operations k) = 0) :
      ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
        ∀ k, k < operations.val.length →
          (∀ j, k < j → j < operations.val.length → opKey operations k ≠ opVal operations j) →
            countOcc (opKey operations k) (vecContents r) = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : SliceI64) (operations : SliceOps)
        (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
        (hnodup : (sliceContents nums).Nodup)
        (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hkeyocc : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums operations k) = 1)
        (hvalocc : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums operations k) = 0), ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
          ∀ k, k < operations.val.length →
            (∀ j, k < j → j < operations.val.length → opKey operations k ≠ opVal operations j) →
              countOcc (opKey operations k) (vecContents r) = 0) := by
    sorry

  /-- Whenever array_change returns a result r, the number of indices i with 0 <= i < len(nums) and r[i] != nums[i] is at most len(operations).
    Preconditions: Let m = len(operations). Define A_0 = nums and, for 0 <= k < m, define A_{k+1} by: for every 0 <= i < len(nums), A_{k+1}[i] = operations[k][1] if A_k[i] = operations[k][0], and A_{k+1}[i] = A_k[i] otherwise. Assume 1 <= len(nums) <= 10^5; 1 <= m <= 10^5; all entries of nums are distinct and satisfy 1 <= nums[i] <= 10^6; each operations[k] has length exactly 2 and 1 <= operations[k][0] <= 10^6 and 1 <= operations[k][1] <= 10^6; and for every 0 <= k < m, operations[k][0] occurs exactly once in A_k while operations[k][1] occurs zero times in A_k. -/
  theorem spec_8
      (nums : SliceI64) (operations : SliceOps)
      (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
      (hnodup : (sliceContents nums).Nodup)
      (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hkeyocc : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums operations k) = 1)
      (hvalocc : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums operations k) = 0) :
      ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
        numDiff (vecContents r) (sliceContents nums) (sliceContents nums).length
          ≤ operations.val.length := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : SliceI64) (operations : SliceOps)
        (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
        (hnodup : (sliceContents nums).Nodup)
        (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hkeyocc : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums operations k) = 1)
        (hvalocc : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums operations k) = 0), ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
          numDiff (vecContents r) (sliceContents nums) (sliceContents nums).length
            ≤ operations.val.length) := by
    sorry

  /-- Whenever array_change returns a result r, for every i with 0 <= i < len(nums), either r[i] = nums[i], or there exists k with 0 <= k < len(operations) such that r[i] = operations[k][1].
    Preconditions: Let m = len(operations). Define A_0 = nums and, for 0 <= k < m, define A_{k+1} by: for every 0 <= i < len(nums), A_{k+1}[i] = operations[k][1] if A_k[i] = operations[k][0], and A_{k+1}[i] = A_k[i] otherwise. Assume 1 <= len(nums) <= 10^5; 1 <= m <= 10^5; all entries of nums are distinct and satisfy 1 <= nums[i] <= 10^6; each operations[k] has length exactly 2 and 1 <= operations[k][0] <= 10^6 and 1 <= operations[k][1] <= 10^6; and for every 0 <= k < m, operations[k][0] occurs exactly once in A_k while operations[k][1] occurs zero times in A_k. -/
  theorem spec_9
      (nums : SliceI64) (operations : SliceOps)
      (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
      (hnodup : (sliceContents nums).Nodup)
      (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hkeyocc : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums operations k) = 1)
      (hvalocc : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums operations k) = 0) :
      ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
        ∀ i, i < (sliceContents nums).length →
          (vecContents r).getD i 0 = (sliceContents nums).getD i 0 ∨
            ∃ k, k < operations.val.length ∧ (vecContents r).getD i 0 = opVal operations k := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : SliceI64) (operations : SliceOps)
        (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
        (hnodup : (sliceContents nums).Nodup)
        (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hkeyocc : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums operations k) = 1)
        (hvalocc : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums operations k) = 0), ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
          ∀ i, i < (sliceContents nums).length →
            (vecContents r).getD i 0 = (sliceContents nums).getD i 0 ∨
              ∃ k, k < operations.val.length ∧ (vecContents r).getD i 0 = opVal operations k) := by
    sorry

  /-- Whenever array_change returns a result r, if len(nums) = 1, then len(r) = 1 and r[0] = operations[len(operations)-1][1].
    Preconditions: Let m = len(operations). Define A_0 = nums and, for 0 <= k < m, define A_{k+1} by: for every 0 <= i < len(nums), A_{k+1}[i] = operations[k][1] if A_k[i] = operations[k][0], and A_{k+1}[i] = A_k[i] otherwise. Assume 1 <= len(nums) <= 10^5; 1 <= m <= 10^5; all entries of nums are distinct and satisfy 1 <= nums[i] <= 10^6; each operations[k] has length exactly 2 and 1 <= operations[k][0] <= 10^6 and 1 <= operations[k][1] <= 10^6; and for every 0 <= k < m, operations[k][0] occurs exactly once in A_k while operations[k][1] occurs zero times in A_k. -/
  theorem spec_10
      (nums : SliceI64) (operations : SliceOps)
      (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
      (hnodup : (sliceContents nums).Nodup)
      (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hkeyocc : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums operations k) = 1)
      (hvalocc : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums operations k) = 0) :
      ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
        (sliceContents nums).length = 1 →
          (vecContents r).length = 1 ∧
            (vecContents r).getD 0 0 = opVal operations (operations.val.length - 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : SliceI64) (operations : SliceOps)
        (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
        (hnodup : (sliceContents nums).Nodup)
        (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hkeyocc : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums operations k) = 1)
        (hvalocc : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums operations k) = 0), ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
          (sliceContents nums).length = 1 →
            (vecContents r).length = 1 ∧
              (vecContents r).getD 0 0 = opVal operations (operations.val.length - 1)) := by
    sorry

  /-- Whenever array_change returns a result r, for every value x such that nums[i] = x for some 0 <= i < len(nums), the following holds, where x occurs in r means there exists j with 0 <= j < len(r) and r[j] = x: x occurs in r if and only if either (a) x != operations[k][0] for every k with 0 <= k < len(operations), or (b) there exists k with 0 <= k < len(operations) such that operations[k][1] = x and x != operations[j][0] for every j with k < j < len(operations).
    Preconditions: Let m = len(operations). Define A_0 = nums and, for 0 <= k < m, define A_{k+1} by: for every 0 <= i < len(nums), A_{k+1}[i] = operations[k][1] if A_k[i] = operations[k][0], and A_{k+1}[i] = A_k[i] otherwise. Assume 1 <= len(nums) <= 10^5; 1 <= m <= 10^5; all entries of nums are distinct and satisfy 1 <= nums[i] <= 10^6; each operations[k] has length exactly 2 and 1 <= operations[k][0] <= 10^6 and 1 <= operations[k][1] <= 10^6; and for every 0 <= k < m, operations[k][0] occurs exactly once in A_k while operations[k][1] occurs zero times in A_k. -/
  theorem spec_11
      (nums : SliceI64) (operations : SliceOps)
      (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
      (hnodup : (sliceContents nums).Nodup)
      (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hkeyocc : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums operations k) = 1)
      (hvalocc : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums operations k) = 0) :
      ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
        ∀ x, x ∈ sliceContents nums →
          (Occurs x (vecContents r) ↔
            ((∀ k, k < operations.val.length → x ≠ opKey operations k) ∨
              ∃ k, k < operations.val.length ∧ opVal operations k = x ∧
                (∀ j, k < j → j < operations.val.length → x ≠ opKey operations j))) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : SliceI64) (operations : SliceOps)
        (hnum : 1 ≤ (sliceContents nums).length ∧ (sliceContents nums).length ≤ 100000)
        (hnodup : (sliceContents nums).Nodup)
        (hrange : ∀ x, x ∈ sliceContents nums → 1 ≤ x ∧ x ≤ 1000000)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hkeyocc : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums operations k) = 1)
        (hvalocc : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums operations k) = 0), ∀ r, Aegis.ArrayChange.array_change nums operations = Aeneas.Std.Result.ok r →
          ∀ x, x ∈ sliceContents nums →
            (Occurs x (vecContents r) ↔
              ((∀ k, k < operations.val.length → x ≠ opKey operations k) ∨
                ∃ k, k < operations.val.length ∧ opVal operations k = x ∧
                  (∀ j, k < j → j < operations.val.length → x ≠ opKey operations j)))) := by
    sorry

  /-- Whenever array_change(nums1, operations) returns a result r1 and array_change(nums2, operations) returns a result r2, for every i with 0 <= i < len(nums1) and every j with 0 <= j < len(nums2), if nums1[i] = nums2[j], then r1[i] = r2[j].
    Preconditions: Let m = len(operations). For s = 1 and s = 2, define A^s_0 = nums_s and, for 0 <= k < m, define A^s_{k+1} by: for every 0 <= i < len(nums_s), A^s_{k+1}[i] = operations[k][1] if A^s_k[i] = operations[k][0], and A^s_{k+1}[i] = A^s_k[i] otherwise. Assume 1 <= m <= 10^5; each operations[k] has length exactly 2 and both entries are in [1,10^6]; and for s = 1 and s = 2: 1 <= len(nums_s) <= 10^5, all entries of nums_s are distinct and in [1,10^6], and for every 0 <= k < m, operations[k][0] occurs exactly once in A^s_k while operations[k][1] occurs zero times in A^s_k. -/
  theorem spec_12
      (nums1 nums2 : SliceI64) (operations : SliceOps)
      (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
      (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
      (hkey : ∀ k, k < operations.val.length →
        1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
      (hval : ∀ k, k < operations.val.length →
        1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
      (hnum1 : 1 ≤ (sliceContents nums1).length ∧ (sliceContents nums1).length ≤ 100000)
      (hnodup1 : (sliceContents nums1).Nodup)
      (hrange1 : ∀ x, x ∈ sliceContents nums1 → 1 ≤ x ∧ x ≤ 1000000)
      (hkeyocc1 : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums1 operations k) = 1)
      (hvalocc1 : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums1 operations k) = 0)
      (hnum2 : 1 ≤ (sliceContents nums2).length ∧ (sliceContents nums2).length ≤ 100000)
      (hnodup2 : (sliceContents nums2).Nodup)
      (hrange2 : ∀ x, x ∈ sliceContents nums2 → 1 ≤ x ∧ x ≤ 1000000)
      (hkeyocc2 : ∀ k, k < operations.val.length →
        countOcc (opKey operations k) (arrAt nums2 operations k) = 1)
      (hvalocc2 : ∀ k, k < operations.val.length →
        countOcc (opVal operations k) (arrAt nums2 operations k) = 0) :
      ∀ r1 r2, Aegis.ArrayChange.array_change nums1 operations = Aeneas.Std.Result.ok r1 →
        Aegis.ArrayChange.array_change nums2 operations = Aeneas.Std.Result.ok r2 →
          ∀ i j, i < (sliceContents nums1).length → j < (sliceContents nums2).length →
            (sliceContents nums1).getD i 0 = (sliceContents nums2).getD j 0 →
              (vecContents r1).getD i 0 = (vecContents r2).getD j 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums1 nums2 : SliceI64) (operations : SliceOps)
        (hm : 1 ≤ operations.val.length ∧ operations.val.length ≤ 100000)
        (hlen : ∀ k, k < operations.val.length → (opList operations k).length = 2)
        (hkey : ∀ k, k < operations.val.length →
          1 ≤ opKey operations k ∧ opKey operations k ≤ 1000000)
        (hval : ∀ k, k < operations.val.length →
          1 ≤ opVal operations k ∧ opVal operations k ≤ 1000000)
        (hnum1 : 1 ≤ (sliceContents nums1).length ∧ (sliceContents nums1).length ≤ 100000)
        (hnodup1 : (sliceContents nums1).Nodup)
        (hrange1 : ∀ x, x ∈ sliceContents nums1 → 1 ≤ x ∧ x ≤ 1000000)
        (hkeyocc1 : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums1 operations k) = 1)
        (hvalocc1 : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums1 operations k) = 0)
        (hnum2 : 1 ≤ (sliceContents nums2).length ∧ (sliceContents nums2).length ≤ 100000)
        (hnodup2 : (sliceContents nums2).Nodup)
        (hrange2 : ∀ x, x ∈ sliceContents nums2 → 1 ≤ x ∧ x ≤ 1000000)
        (hkeyocc2 : ∀ k, k < operations.val.length →
          countOcc (opKey operations k) (arrAt nums2 operations k) = 1)
        (hvalocc2 : ∀ k, k < operations.val.length →
          countOcc (opVal operations k) (arrAt nums2 operations k) = 0), ∀ r1 r2, Aegis.ArrayChange.array_change nums1 operations = Aeneas.Std.Result.ok r1 →
          Aegis.ArrayChange.array_change nums2 operations = Aeneas.Std.Result.ok r2 →
            ∀ i j, i < (sliceContents nums1).length → j < (sliceContents nums2).length →
              (sliceContents nums1).getD i 0 = (sliceContents nums2).getD j 0 →
                (vecContents r1).getD i 0 = (vecContents r2).getD j 0) := by
    sorry

  end AegisSpec.ArrayChange
