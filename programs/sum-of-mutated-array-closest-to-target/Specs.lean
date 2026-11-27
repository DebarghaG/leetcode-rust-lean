import Aegis.FindBestValue.Code.Funs

/-!
# Specifications of `Aegis.FindBestValue.find_best_value`

LeetCode problem `sum-of-mutated-array-closest-to-target`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindBestValue

  namespace AegisSpec.FindBestValue

  def lenI (arr : Slice Std.I64) : ℤ := ((arr.val.length : ℕ) : ℤ)

  def M (arr : Slice Std.I64) (v : ℤ) : ℤ := (arr.val.map (fun x => min x.val v)).sum

  def total (arr : Slice Std.I64) : ℤ := (arr.val.map (fun x => x.val)).sum

  def maxArr (arr : Slice Std.I64) : ℤ := arr.val.foldr (fun x acc => max x.val acc) 0

  def absI (x : ℤ) : ℤ := if x < 0 then -x else x

  def IsMaxV (arr : Slice Std.I64) (target : Std.I64) (v0 : ℤ) : Prop :=
    0 ≤ v0 ∧ v0 ≤ maxArr arr ∧ M arr v0 ≤ target.val ∧
      ∀ v : ℤ, 0 ≤ v → v ≤ maxArr arr → M arr v ≤ target.val → v ≤ v0

  def IsPermOf (arr arr2 : Slice Std.I64) : Prop :=
    ∃ (hlen : arr2.val.length = arr.val.length) (π : Fin arr.val.length → Fin arr.val.length),
      Function.Bijective π ∧
        ∀ i : Fin arr.val.length,
          (arr2.val.get ⟨i.1, hlen.symm ▸ i.2⟩).val = (arr.val.get (π i)).val

  /-- Let n = len(arr) and define M(v) = sum_{i=0}^{n-1} min(arr[i], v) for an integer v, where min is the ordinary integer minimum. The function returns a result r (an integer) such that: (a) r >= 0; (b) for every integer v with 0 <= v, |M(r) - target| <= |M(v) - target|; (c) for every integer v with 0 <= v and |M(v) - target| = |M(r) - target|, r <= v.
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_1
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        0 ≤ r.val ∧
        (∀ v : ℤ, 0 ≤ v →
          absI (M arr r.val - target.val) ≤ absI (M arr v - target.val)) ∧
        (∀ v : ℤ, 0 ≤ v →
          absI (M arr v - target.val) = absI (M arr r.val - target.val) → r.val ≤ v) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          0 ≤ r.val ∧
          (∀ v : ℤ, 0 ≤ v →
            absI (M arr r.val - target.val) ≤ absI (M arr v - target.val)) ∧
          (∀ v : ℤ, 0 ≤ v →
            absI (M arr v - target.val) = absI (M arr r.val - target.val) → r.val ≤ v)) := by
    sorry

  /-- The function returns a result r; it does not fail on any input satisfying the preconditions (no panic, no out-of-bounds access, and no arithmetic overflow).
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_2
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∃ r : Std.I64, find_best_value arr target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∃ r : Std.I64, find_best_value arr target = ok r) := by
    sorry

  /-- Let maxarr = max_{0 <= i < len(arr)} arr[i]. The returned value r satisfies 0 <= r <= min(target, maxarr).
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_3
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        0 ≤ r.val ∧ r.val ≤ min target.val (maxArr arr) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          0 ≤ r.val ∧ r.val ≤ min target.val (maxArr arr)) := by
    sorry

  /-- Suppose there is an integer c such that arr[i] = c for every i with 0 <= i < len(arr) (so 1 <= c <= 100000). Let n = len(arr), q = floor(target / n) (integer division), and rem = target - q*n. If target >= n*c then r = c; if target < n*c then r = q when 2*rem <= n, and r = q + 1 when 2*rem > n.
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_4
      (arr : Slice Std.I64) (target : Std.I64) (c : ℤ)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000)
      (hc : ∀ i : Fin arr.val.length, (arr.val.get i).val = c)
      (hc1 : 1 ≤ c) (hc2 : c ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        let n : ℤ := lenI arr
        let q : ℤ := target.val / n
        let rem : ℤ := target.val - q * n
        (n * c ≤ target.val → r.val = c) ∧
        (target.val < n * c →
          (2 * rem ≤ n → r.val = q) ∧ (2 * rem > n → r.val = q + 1)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64) (c : ℤ)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000)
        (hc : ∀ i : Fin arr.val.length, (arr.val.get i).val = c)
        (hc1 : 1 ≤ c) (hc2 : c ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          let n : ℤ := lenI arr
          let q : ℤ := target.val / n
          let rem : ℤ := target.val - q * n
          (n * c ≤ target.val → r.val = c) ∧
          (target.val < n * c →
            (2 * rem ≤ n → r.val = q) ∧ (2 * rem > n → r.val = q + 1))) := by
    sorry

  /-- If target <= len(arr), then r = 0 when 2*target <= len(arr), and r = 1 when 2*target > len(arr).
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_5
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        target.val ≤ lenI arr →
          (2 * target.val ≤ lenI arr → r.val = 0) ∧
          (2 * target.val > lenI arr → r.val = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          target.val ≤ lenI arr →
            (2 * target.val ≤ lenI arr → r.val = 0) ∧
            (2 * target.val > lenI arr → r.val = 1)) := by
    sorry

  /-- Let total = sum_{i=0}^{len(arr)-1} arr[i] and maxarr = max_{0 <= i < len(arr)} arr[i]. If total <= target, then r = maxarr.
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_6
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        total arr ≤ target.val → r.val = maxArr arr := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          total arr ≤ target.val → r.val = maxArr arr) := by
    sorry

  /-- Let maxarr = max_{0 <= i < len(arr)} arr[i] and M(v) = sum_{i=0}^{len(arr)-1} min(arr[i], v) for an integer v. If r < maxarr, then M(r + 1) > target.
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_7
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        r.val < maxArr arr → M arr (r.val + 1) > target.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          r.val < maxArr arr → M arr (r.val + 1) > target.val) := by
    sorry

  /-- Let M(v) = sum_{i=0}^{len(arr)-1} min(arr[i], v) for an integer v. If r > 0, then M(r - 1) < target.
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_8
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        0 < r.val → M arr (r.val - 1) < target.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          0 < r.val → M arr (r.val - 1) < target.val) := by
    sorry

  /-- Let maxarr = max_{0 <= i < len(arr)} arr[i] and M(v) = sum_{i=0}^{len(arr)-1} min(arr[i], v) for an integer v. If there exists an integer v with 0 <= v <= maxarr and M(v) = target, then M(r) = target, and for every integer v with 0 <= v <= maxarr and v != r it holds that M(v) != target.
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_9
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        (∃ v : ℤ, 0 ≤ v ∧ v ≤ maxArr arr ∧ M arr v = target.val) →
          M arr r.val = target.val ∧
          (∀ v : ℤ, 0 ≤ v → v ≤ maxArr arr → v ≠ r.val → M arr v ≠ target.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          (∃ v : ℤ, 0 ≤ v ∧ v ≤ maxArr arr ∧ M arr v = target.val) →
            M arr r.val = target.val ∧
            (∀ v : ℤ, 0 ≤ v → v ≤ maxArr arr → v ≠ r.val → M arr v ≠ target.val)) := by
    sorry

  /-- For every slice arr2 with len(arr2) = len(arr) for which there exists a permutation pi of {0, 1, ..., len(arr)-1} such that arr2[i] = arr[pi(i)] for every i with 0 <= i < len(arr), the value returned by find_best_value on (arr2, target) equals the value returned by find_best_value on (arr, target).
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_10
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ (arr2 : Slice Std.I64) (r r2 : Std.I64),
        IsPermOf arr arr2 →
        find_best_value arr target = ok r →
        find_best_value arr2 target = ok r2 → r = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ (arr2 : Slice Std.I64) (r r2 : Std.I64),
          IsPermOf arr arr2 →
          find_best_value arr target = ok r →
          find_best_value arr2 target = ok r2 → r = r2) := by
    sorry

  /-- Let maxarr = max_{0 <= i < len(arr)} arr[i] and M(v) = sum_{i=0}^{len(arr)-1} min(arr[i], v) for an integer v. Let v0 be the largest integer v with 0 <= v <= maxarr and M(v) <= target (it exists because M(0) = 0 <= target). Then either (v0 = maxarr and r = v0), or (v0 < maxarr and (r = v0 or r = v0 + 1)).
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_11
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        ∃ v0 : ℤ, IsMaxV arr target v0 ∧
          ((v0 = maxArr arr ∧ r.val = v0) ∨
           (v0 < maxArr arr ∧ (r.val = v0 ∨ r.val = v0 + 1))) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          ∃ v0 : ℤ, IsMaxV arr target v0 ∧
            ((v0 = maxArr arr ∧ r.val = v0) ∨
             (v0 < maxArr arr ∧ (r.val = v0 ∨ r.val = v0 + 1)))) := by
    sorry

  /-- Let M(v) = sum_{i=0}^{len(arr)-1} min(arr[i], v) for an integer v and let total = sum_{i=0}^{len(arr)-1} arr[i]. If target <= total, then 2 * |M(r) - target| <= len(arr).
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_12
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        target.val ≤ total arr → 2 * absI (M arr r.val - target.val) ≤ lenI arr := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          target.val ≤ total arr → 2 * absI (M arr r.val - target.val) ≤ lenI arr) := by
    sorry

  /-- Let M(v) = sum_{i=0}^{len(arr)-1} min(arr[i], v) for an integer v. If M(r) >= target, then for every integer v with 0 <= v < r, M(v) < target; equivalently, r is the smallest integer v with 0 <= v and M(v) >= target.
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_13
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        M arr r.val ≥ target.val →
          ∀ v : ℤ, 0 ≤ v → v < r.val → M arr v < target.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          M arr r.val ≥ target.val →
            ∀ v : ℤ, 0 ≤ v → v < r.val → M arr v < target.val) := by
    sorry

  /-- Let M(v) = sum_{i=0}^{len(arr)-1} min(arr[i], v) for an integer v. If M(r) > target, then target - M(r - 1) > M(r) - target.
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_14
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        M arr r.val > target.val →
          target.val - M arr (r.val - 1) > M arr r.val - target.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          M arr r.val > target.val →
            target.val - M arr (r.val - 1) > M arr r.val - target.val) := by
    sorry

  /-- Let r be the returned value. Then r = 0 if and only if 2 * target <= len(arr).
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_15
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        (r.val = 0 ↔ 2 * target.val ≤ lenI arr) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          (r.val = 0 ↔ 2 * target.val ≤ lenI arr)) := by
    sorry

  /-- Let maxarr = max_{0 <= i < len(arr)} arr[i], M(v) = sum_{i=0}^{len(arr)-1} min(arr[i], v), and let v0 be the largest integer v with 0 <= v <= maxarr and M(v) <= target. Then v0 exists. If v0 = maxarr, r = v0. If v0 < maxarr, put a = target - M(v0) and b = M(v0+1) - target; then a >= 0, b > 0, and r = v0 when a <= b, while r = v0+1 when a > b.
    Preconditions: 1 <= len(arr) <= 10000 and, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and 1 <= target <= 100000. -/
  theorem spec_16
      (arr : Slice Std.I64) (target : Std.I64)
      (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
      (harr : ∀ i : Fin arr.val.length,
        1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000) :
      ∀ r : Std.I64, find_best_value arr target = ok r →
        ∃ v0 : ℤ, IsMaxV arr target v0 ∧
          (v0 = maxArr arr → r.val = v0) ∧
          (v0 < maxArr arr →
            0 ≤ target.val - M arr v0 ∧
            0 < M arr (v0 + 1) - target.val ∧
            ((target.val - M arr v0 ≤ M arr (v0 + 1) - target.val → r.val = v0) ∧
             (target.val - M arr v0 > M arr (v0 + 1) - target.val → r.val = v0 + 1))) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
        (hlen1 : 1 ≤ lenI arr) (hlen2 : lenI arr ≤ 10000)
        (harr : ∀ i : Fin arr.val.length,
          1 ≤ (arr.val.get i).val ∧ (arr.val.get i).val ≤ 100000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 100000), ∀ r : Std.I64, find_best_value arr target = ok r →
          ∃ v0 : ℤ, IsMaxV arr target v0 ∧
            (v0 = maxArr arr → r.val = v0) ∧
            (v0 < maxArr arr →
              0 ≤ target.val - M arr v0 ∧
              0 < M arr (v0 + 1) - target.val ∧
              ((target.val - M arr v0 ≤ M arr (v0 + 1) - target.val → r.val = v0) ∧
               (target.val - M arr v0 > M arr (v0 + 1) - target.val → r.val = v0 + 1)))) := by
    sorry

  end AegisSpec.FindBestValue
