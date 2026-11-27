import Aegis.LongestMountain.Code.Funs

/-!
# Specifications of `Aegis.LongestMountain.longest_mountain`

LeetCode problem `longest-mountain-in-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestMountain

  def vals (arr : Slice Std.I64) : List Int := arr.list.toList.map (fun x => x.val)

  def elem (arr : Slice Std.I64) (i : Nat) : Int := ((vals arr)[i]?).getD 0

  def BoundedValues (arr : Slice Std.I64) : Prop :=
    ∀ i, i < arr.leng → ∃ x : Int, (vals arr)[i]? = some x ∧ 0 ≤ x ∧ x ≤ 10000

  def sub (a : List Int) (l r : Nat) : List Int := (a.drop l).take (r + 1 - l)

  def StrictIncr : List Int → Prop
    | [] => True
    | [_] => True
    | a :: b :: t => a < b ∧ StrictIncr (b :: t)

  def StrictDecr : List Int → Prop
    | [] => True
    | [_] => True
    | a :: b :: t => a > b ∧ StrictDecr (b :: t)

  def IsMountainSubarray (arr : Slice Std.I64) (l p r : Nat) : Prop :=
    l < p ∧ p < r ∧ r < arr.leng ∧
      StrictIncr (sub (vals arr) l p) ∧ StrictDecr (sub (vals arr) p r)

  def HasMountain (arr : Slice Std.I64) : Prop := ∃ l p r, IsMountainSubarray arr l p r

  def IsMountainArray (arr : Slice Std.I64) : Prop :=
    ∃ p, IsMountainSubarray arr 0 p (arr.leng - 1)

  /-- Call a contiguous subarray arr[l..r] (with 0 <= l <= r < len(arr)) a mountain subarray iff there exists an index p with l < p < r such that arr[l] < arr[l+1] < ... < arr[p] and arr[p] > arr[p+1] > ... > arr[r] (strictly increasing from l up to p and strictly decreasing from p down to r; this forces r-l+1 >= 3). The function returns a result res such that: if no mountain subarray exists then res = 0; otherwise res is the length of some mountain subarray (there are indices l, p, r with r-l+1 = res satisfying the mountain condition above) and every mountain subarray has length at most res.
    Preconditions: 1 <= len(arr) <= 10000 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000. -/
  theorem spec_1 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr) :
      ∃ res : Std.I64,
        Aegis.LongestMountain.longest_mountain arr = ok res ∧
        (¬ HasMountain arr → res.val = 0) ∧
        (HasMountain arr →
          (∃ l p r, IsMountainSubarray arr l p r ∧ ((r - l + 1 : Nat) : Int) = res.val) ∧
          (∀ l p r, IsMountainSubarray arr l p r → ((r - l + 1 : Nat) : Int) ≤ res.val)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr), ∃ res : Std.I64,
          Aegis.LongestMountain.longest_mountain arr = ok res ∧
          (¬ HasMountain arr → res.val = 0) ∧
          (HasMountain arr →
            (∃ l p r, IsMountainSubarray arr l p r ∧ ((r - l + 1 : Nat) : Int) = res.val) ∧
            (∀ l p r, IsMountainSubarray arr l p r → ((r - l + 1 : Nat) : Int) ≤ res.val))) := by
    sorry

  /-- Whenever the function returns a result res, 0 <= res <= len(arr).
    Preconditions: 1 <= len(arr) <= 10000 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000. -/
  theorem spec_2 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr)
      (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res) :
      0 ≤ res.val ∧ res.val ≤ (arr.leng : Int) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr)
        (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res), 0 ≤ res.val ∧ res.val ≤ (arr.leng : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result res (it never panics, fails, or overflows).
    Preconditions: 1 <= len(arr) <= 10000 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000. -/
  theorem spec_3 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr) :
      ∃ res : Std.I64, Aegis.LongestMountain.longest_mountain arr = ok res := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr), ∃ res : Std.I64, Aegis.LongestMountain.longest_mountain arr = ok res) := by
    sorry

  /-- The function returns a result res with res = 0.
    Preconditions: 1 <= len(arr) <= 10000, for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000, and len(arr) <= 2. -/
  theorem spec_4 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr)
      (hshort : arr.leng ≤ 2) :
      ∃ res : Std.I64, Aegis.LongestMountain.longest_mountain arr = ok res ∧ res.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr)
        (hshort : arr.leng ≤ 2), ∃ res : Std.I64, Aegis.LongestMountain.longest_mountain arr = ok res ∧ res.val = 0) := by
    sorry

  /-- The function returns a result res with res = 3 if arr[0] < arr[1] and arr[1] > arr[2], and res = 0 otherwise.
    Preconditions: 1 <= len(arr) <= 10000, for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000, and len(arr) = 3. -/
  theorem spec_5 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr)
      (h3 : arr.leng = 3) :
      ∃ res : Std.I64,
        Aegis.LongestMountain.longest_mountain arr = ok res ∧
        ((elem arr 0 < elem arr 1 ∧ elem arr 1 > elem arr 2) ∧ res.val = 3 ∨
          ¬ (elem arr 0 < elem arr 1 ∧ elem arr 1 > elem arr 2) ∧ res.val = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr)
        (h3 : arr.leng = 3), ∃ res : Std.I64,
          Aegis.LongestMountain.longest_mountain arr = ok res ∧
          ((elem arr 0 < elem arr 1 ∧ elem arr 1 > elem arr 2) ∧ res.val = 3 ∨
            ¬ (elem arr 0 < elem arr 1 ∧ elem arr 1 > elem arr 2) ∧ res.val = 0)) := by
    sorry

  /-- The function returns a result res with res = len(arr).
    Preconditions: 1 <= len(arr) <= 10000, for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000, and the whole array is a mountain: len(arr) >= 3 and there exists p with 0 < p < len(arr)-1 such that arr[0] < arr[1] < ... < arr[p] and arr[p] > arr[p+1] > ... > arr[len(arr)-1]. -/
  theorem spec_6 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr)
      (hmtn : 3 ≤ arr.leng ∧ IsMountainArray arr) :
      ∃ res : Std.I64,
        Aegis.LongestMountain.longest_mountain arr = ok res ∧ res.val = (arr.leng : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr)
        (hmtn : 3 ≤ arr.leng ∧ IsMountainArray arr), ∃ res : Std.I64,
          Aegis.LongestMountain.longest_mountain arr = ok res ∧ res.val = (arr.leng : Int)) := by
    sorry

  /-- Whenever the function returns a result res with res = len(arr), the whole array is a mountain subarray: len(arr) >= 3 and there exists p with 0 < p < len(arr)-1 such that arr[0] < arr[1] < ... < arr[p] and arr[p] > arr[p+1] > ... > arr[len(arr)-1].
    Preconditions: 1 <= len(arr) <= 10000 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000. -/
  theorem spec_7 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr)
      (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res)
      (hfull : res.val = (arr.leng : Int)) :
      3 ≤ arr.leng ∧ IsMountainArray arr := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr)
        (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res)
        (hfull : res.val = (arr.leng : Int)), 3 ≤ arr.leng ∧ IsMountainArray arr) := by
    sorry

  /-- Whenever the function returns a result res with res > 0, there exist indices l and r with 0 <= l <= r < len(arr) such that arr[l..r] is a mountain subarray (there is p with l < p < r, arr[l] < ... < arr[p] and arr[p] > ... > arr[r]) and r-l+1 = res.
    Preconditions: 1 <= len(arr) <= 10000 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000. -/
  theorem spec_8 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr)
      (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res)
      (hpos : 0 < res.val) :
      ∃ l p r, IsMountainSubarray arr l p r ∧ ((r - l + 1 : Nat) : Int) = res.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr)
        (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res)
        (hpos : 0 < res.val), ∃ l p r, IsMountainSubarray arr l p r ∧ ((r - l + 1 : Nat) : Int) = res.val) := by
    sorry

  /-- Whenever the function returns a result res, for every l and r with 0 <= l <= r < len(arr), if arr[l..r] is a mountain subarray then r-l+1 <= res.
    Preconditions: 1 <= len(arr) <= 10000 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000. -/
  theorem spec_9 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr)
      (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res) :
      ∀ l p r, IsMountainSubarray arr l p r → ((r - l + 1 : Nat) : Int) ≤ res.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr)
        (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res), ∀ l p r, IsMountainSubarray arr l p r → ((r - l + 1 : Nat) : Int) ≤ res.val) := by
    sorry

  /-- Whenever the function returns a result res, res = 0 if and only if there is no mountain subarray in arr, i.e. there do not exist indices l, p, r with 0 <= l < p < r < len(arr), arr[l] < arr[l+1] < ... < arr[p], and arr[p] > arr[p+1] > ... > arr[r].
    Preconditions: 1 <= len(arr) <= 10000 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000. -/
  theorem spec_10 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr)
      (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res) :
      (res.val = 0 ↔ ¬ HasMountain arr) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr)
        (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res), (res.val = 0 ↔ ¬ HasMountain arr)) := by
    sorry

  /-- Whenever the function returns a result res, either res = 0 or res >= 3.
    Preconditions: 1 <= len(arr) <= 10000 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000. -/
  theorem spec_11 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr)
      (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res) :
      res.val = 0 ∨ 3 ≤ res.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr)
        (res : Std.I64) (hres : Aegis.LongestMountain.longest_mountain arr = ok res), res.val = 0 ∨ 3 ≤ res.val) := by
    sorry

  /-- The result returned on arr equals the result returned on brr.
    Preconditions: 1 <= len(arr) <= 10000 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10000; let brr be the reversal of arr with brr[i] = arr[len(arr)-1-i] for 0 <= i < len(arr). -/
  theorem spec_12 (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
      (hrange : BoundedValues arr)
      (brr : Slice Std.I64) (hrev : vals brr = (vals arr).reverse) :
      Aegis.LongestMountain.longest_mountain arr = Aegis.LongestMountain.longest_mountain brr := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.leng) (hlenle : arr.leng ≤ 10000)
        (hrange : BoundedValues arr)
        (brr : Slice Std.I64) (hrev : vals brr = (vals arr).reverse), Aegis.LongestMountain.longest_mountain arr = Aegis.LongestMountain.longest_mountain brr) := by
    sorry

  end AegisSpec.LongestMountain
