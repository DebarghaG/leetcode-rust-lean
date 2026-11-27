import Aegis.MakeSubKSumEqual.Code.Funs

/-!
# Specifications of `Aegis.MakeSubKSumEqual.make_sub_k_sum_equal`

LeetCode problem `make-k-subarray-sums-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MakeSubKSumEqual

  def entry (arr : Slice Std.I64) (i : Nat) : Int := (arr.val.getD i 0#i64).val

  def absDiff (a b : Int) : Int := if a ≤ b then b - a else a - b

  def getInt (b : List Int) (i : Nat) : Int := b.getD i 0

  def classIdx (n g c : Nat) : Finset Nat := (Finset.range n).filter (fun i => i % g = c)

  def classSum (arr : Slice Std.I64) (g c : Nat) (y : Int) : Int :=
    ∑ i ∈ classIdx arr.val.length g c, absDiff (entry arr i) y

  def IsClassMin (arr : Slice Std.I64) (g c : Nat) (m : Int) : Prop :=
    (∃ y : Int, m = classSum arr g c y) ∧ ∀ y : Int, m ≤ classSum arr g c y

  def arrDist (arr : Slice Std.I64) (b : Nat → Int) : Int :=
    ∑ i ∈ Finset.range arr.val.length, absDiff (entry arr i) (b i)

  def windowSum (b : List Int) (kk n s : Nat) : Int :=
    ∑ j ∈ Finset.range kk, getInt b ((s + j) % n)

  def gcdNK (arr : Slice Std.I64) (k : Std.I64) : Nat := Nat.gcd arr.val.length k.val.toNat

  def RotatedBy (arr arr' : Slice Std.I64) (t : Nat) : Prop :=
    arr'.val.length = arr.val.length ∧
      ∀ i, i < arr.val.length → entry arr' i = entry arr ((i + t) % arr.val.length)

  def ScaledBy (arr arr' : Slice Std.I64) (c : Int) : Prop :=
    arr'.val.length = arr.val.length ∧
      ∀ i, i < arr.val.length → entry arr' i = c * entry arr i

  /-- The function returns a result r, and r = sum_{c=0}^{g-1} ( min over integers y of sum over all i with 0 <= i < n and i mod g = c of abs(y - arr[i]) ), where abs is absolute value. Equivalently, the minimum total number of unit increments/decrements needed so that all circular contiguous subarrays of length k have the same sum is obtained by, for each residue class c modulo g, replacing all entries arr[i] with i mod g = c by one common integer y_c, independently minimizing the sum of absolute changes in that class.
    Preconditions: Let n = len(arr). The input satisfies 1 <= k <= n, n <= 100000, and 1 <= arr[i] <= 1000000000 for every i with 0 <= i < n. Here k is treated as the positive integer represented by the I64 parameter. Let g = gcd(n, k). -/
  theorem spec_1 (arr : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val)
      (hklen : k.val ≤ (arr.val.length : Int))
      (hnlen : arr.val.length ≤ 100000)
      (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000) :
      ∃ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r ∧
        ∃ y : Nat → Int,
          (∀ c, c < gcdNK arr k → IsClassMin arr (gcdNK arr k) c (y c)) ∧
          r.val = ∑ c ∈ Finset.range (gcdNK arr k), y c := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val)
        (hklen : k.val ≤ (arr.val.length : Int))
        (hnlen : arr.val.length ≤ 100000)
        (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000), ∃ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r ∧
          ∃ y : Nat → Int,
            (∀ c, c < gcdNK arr k → IsClassMin arr (gcdNK arr k) c (y c)) ∧
            r.val = ∑ c ∈ Finset.range (gcdNK arr k), y c) := by
    sorry

  /-- The function returns a result r: it does not fail, panic, overflow, or index out of bounds.
    Preconditions: Let n = len(arr). The input satisfies 1 <= k <= n, n <= 100000, and 1 <= arr[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_2 (arr : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val)
      (hklen : k.val ≤ (arr.val.length : Int))
      (hnlen : arr.val.length ≤ 100000)
      (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000) :
      ∃ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val)
        (hklen : k.val ≤ (arr.val.length : Int))
        (hnlen : arr.val.length ≤ 100000)
        (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000), ∃ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: Let n = len(arr). The input satisfies 1 <= k <= n, n <= 100000, and 1 <= arr[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_3 (arr : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val)
      (hklen : k.val ≤ (arr.val.length : Int))
      (hnlen : arr.val.length ≤ 100000)
      (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000) :
      ∀ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val)
        (hklen : k.val ≤ (arr.val.length : Int))
        (hnlen : arr.val.length ≤ 100000)
        (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000), ∀ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer c with 1 <= c <= 1000000000, r <= sum_{i=0}^{n-1} abs(arr[i] - c).
    Preconditions: Let n = len(arr). The input satisfies 1 <= k <= n, n <= 100000, and 1 <= arr[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_4 (arr : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val)
      (hklen : k.val ≤ (arr.val.length : Int))
      (hnlen : arr.val.length ≤ 100000)
      (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000) :
      ∀ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
        ∀ c : Int, 1 ≤ c → c ≤ 1000000000 → r.val ≤ arrDist arr (fun _ => c) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val)
        (hklen : k.val ≤ (arr.val.length : Int))
        (hnlen : arr.val.length ≤ 100000)
        (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000), ∀ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
          ∀ c : Int, 1 ≤ c → c ≤ 1000000000 → r.val ≤ arrDist arr (fun _ => c)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i and j with 0 <= i < n, 0 <= j < n, and i mod g = j mod g, arr[i] = arr[j].
    Preconditions: Let n = len(arr). The input satisfies 1 <= k <= n, n <= 100000, and 1 <= arr[i] <= 1000000000 for every i with 0 <= i < n. Let g = gcd(n, k). -/
  theorem spec_5 (arr : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val)
      (hklen : k.val ≤ (arr.val.length : Int))
      (hnlen : arr.val.length ≤ 100000)
      (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000) :
      ∀ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
        (r.val = 0 ↔ ∀ i j, i < arr.val.length → j < arr.val.length →
          i % gcdNK arr k = j % gcdNK arr k → entry arr i = entry arr j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val)
        (hklen : k.val ≤ (arr.val.length : Int))
        (hnlen : arr.val.length ≤ 100000)
        (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000), ∀ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
          (r.val = 0 ↔ ∀ i j, i < arr.val.length → j < arr.val.length →
            i % gcdNK arr k = j % gcdNK arr k → entry arr i = entry arr j)) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer array b of length n such that: (1) 1 <= b[i] <= 1000000000 for every i with 0 <= i < n; (2) sum_{i=0}^{n-1} abs(b[i] - arr[i]) = r; and (3) for every start s with 0 <= s < n, the sum sum_{j=0}^{k-1} b[(s+j) mod n] is independent of s.
    Preconditions: Let n = len(arr). The input satisfies 1 <= k <= n, n <= 100000, and 1 <= arr[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_6 (arr : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val)
      (hklen : k.val ≤ (arr.val.length : Int))
      (hnlen : arr.val.length ≤ 100000)
      (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000) :
      ∀ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
        ∃ b : List Int, b.length = arr.val.length ∧
          (∀ i, i < arr.val.length → 1 ≤ getInt b i ∧ getInt b i ≤ 1000000000) ∧
          arrDist arr (fun i => getInt b i) = r.val ∧
          (∀ s1 s2, s1 < arr.val.length → s2 < arr.val.length →
            windowSum b k.val.toNat arr.val.length s1 =
              windowSum b k.val.toNat arr.val.length s2) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val)
        (hklen : k.val ≤ (arr.val.length : Int))
        (hnlen : arr.val.length ≤ 100000)
        (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000), ∀ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
          ∃ b : List Int, b.length = arr.val.length ∧
            (∀ i, i < arr.val.length → 1 ≤ getInt b i ∧ getInt b i ≤ 1000000000) ∧
            arrDist arr (fun i => getInt b i) = r.val ∧
            (∀ s1 s2, s1 < arr.val.length → s2 < arr.val.length →
              windowSum b k.val.toNat arr.val.length s1 =
                windowSum b k.val.toNat arr.val.length s2)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer array b of length n for which the sums sum_{j=0}^{k-1} b[(s+j) mod n] are the same for all s with 0 <= s < n, one has sum_{i=0}^{n-1} abs(b[i] - arr[i]) >= r.
    Preconditions: Let n = len(arr). The input satisfies 1 <= k <= n, n <= 100000, and 1 <= arr[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_7 (arr : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val)
      (hklen : k.val ≤ (arr.val.length : Int))
      (hnlen : arr.val.length ≤ 100000)
      (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000) :
      ∀ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
        ∀ b : List Int, b.length = arr.val.length →
          (∀ s1 s2, s1 < arr.val.length → s2 < arr.val.length →
            windowSum b k.val.toNat arr.val.length s1 =
              windowSum b k.val.toNat arr.val.length s2) →
          r.val ≤ arrDist arr (fun i => getInt b i) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val)
        (hklen : k.val ≤ (arr.val.length : Int))
        (hnlen : arr.val.length ≤ 100000)
        (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000), ∀ r, Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
          ∀ b : List Int, b.length = arr.val.length →
            (∀ s1 s2, s1 < arr.val.length → s2 < arr.val.length →
              windowSum b k.val.toNat arr.val.length s1 =
                windowSum b k.val.toNat arr.val.length s2) →
            r.val ≤ arrDist arr (fun i => getInt b i)) := by
    sorry

  /-- Whenever the function returns r on input (arr, k) and returns r' on input (arr', k), r = r'.
    Preconditions: Let n = len(arr). The input satisfies 1 <= k <= n, n <= 100000, and 1 <= arr[i] <= 1000000000 for every i with 0 <= i < n. Let t be an integer with 0 <= t < n, and define arr'[i] = arr[(i+t) mod n] for 0 <= i < n; then arr' also satisfies the same constraints. -/
  theorem spec_8 (arr arr' : Slice Std.I64) (k : Std.I64) (t : Nat)
      (hk1 : 1 ≤ k.val)
      (hklen : k.val ≤ (arr.val.length : Int))
      (hnlen : arr.val.length ≤ 100000)
      (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000)
      (ht : t < arr.val.length)
      (hrot : RotatedBy arr arr' t) :
      ∀ r r', Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
        Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr' k = ok r' → r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr arr' : Slice Std.I64) (k : Std.I64) (t : Nat)
        (hk1 : 1 ≤ k.val)
        (hklen : k.val ≤ (arr.val.length : Int))
        (hnlen : arr.val.length ≤ 100000)
        (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000)
        (ht : t < arr.val.length)
        (hrot : RotatedBy arr arr' t), ∀ r r', Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
          Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr' k = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on input (arr, k) and returns r' on input (arr', k), r' = c * r.
    Preconditions: Let n = len(arr). The input satisfies 1 <= k <= n, n <= 100000, and 1 <= arr[i] <= 1000000000 for every i with 0 <= i < n. Let c be a positive integer such that 1 <= c*arr[i] <= 1000000000 for every i with 0 <= i < n, and define arr'[i] = c*arr[i]; then arr' also satisfies the same constraints. -/
  theorem spec_9 (arr arr' : Slice Std.I64) (k : Std.I64) (c : Int)
      (hk1 : 1 ≤ k.val)
      (hklen : k.val ≤ (arr.val.length : Int))
      (hnlen : arr.val.length ≤ 100000)
      (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000)
      (hc1 : 1 ≤ c)
      (hcval : ∀ i, i < arr.val.length →
        1 ≤ c * entry arr i ∧ c * entry arr i ≤ 1000000000)
      (hscale : ScaledBy arr arr' c) :
      ∀ r r', Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
        Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr' k = ok r' → r'.val = c * r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr arr' : Slice Std.I64) (k : Std.I64) (c : Int)
        (hk1 : 1 ≤ k.val)
        (hklen : k.val ≤ (arr.val.length : Int))
        (hnlen : arr.val.length ≤ 100000)
        (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000)
        (hc1 : 1 ≤ c)
        (hcval : ∀ i, i < arr.val.length →
          1 ≤ c * entry arr i ∧ c * entry arr i ≤ 1000000000)
        (hscale : ScaledBy arr arr' c), ∀ r r', Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
          Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr' k = ok r' → r'.val = c * r.val) := by
    sorry

  /-- Whenever the function returns r on input (arr, k) and returns r' on input (arr, k'), r = r'.
    Preconditions: Let n = len(arr). The input satisfies 1 <= k <= n, n <= 100000, and 1 <= arr[i] <= 1000000000 for every i with 0 <= i < n. Let k' be an integer with 1 <= k' <= n and gcd(n,k') = gcd(n,k). -/
  theorem spec_10 (arr : Slice Std.I64) (k k' : Std.I64)
      (hk1 : 1 ≤ k.val)
      (hklen : k.val ≤ (arr.val.length : Int))
      (hnlen : arr.val.length ≤ 100000)
      (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000)
      (hk'1 : 1 ≤ k'.val)
      (hk'len : k'.val ≤ (arr.val.length : Int))
      (hgcd : gcdNK arr k' = gcdNK arr k) :
      ∀ r r', Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
        Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64) (k k' : Std.I64)
        (hk1 : 1 ≤ k.val)
        (hklen : k.val ≤ (arr.val.length : Int))
        (hnlen : arr.val.length ≤ 100000)
        (hval : ∀ i, i < arr.val.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000000000)
        (hk'1 : 1 ≤ k'.val)
        (hk'len : k'.val ≤ (arr.val.length : Int))
        (hgcd : gcdNK arr k' = gcdNK arr k), ∀ r r', Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k = ok r →
          Aegis.MakeSubKSumEqual.make_sub_k_sum_equal arr k' = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.MakeSubKSumEqual
