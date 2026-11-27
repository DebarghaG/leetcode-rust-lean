import Aegis.MaxSumAfterPartitioning.Code.Funs

/-!
# Specifications of `Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning`

LeetCode problem `partition-array-for-maximum-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSumAfterPartitioning

def vals (arr : Slice Std.I64) : List Int := arr.val.map (fun (x : Std.I64) => x.val)

def maxD (l : List Int) : Int := l.foldr max 0

def blockMax (l : List Int) (s b : Nat) : Int := maxD ((l.drop s).take b)

def startsAux : List Nat → Nat → List Nat
  | [], _ => []
  | b :: bs, off => off :: startsAux bs (off + b)

def starts (bs : List Nat) : List Nat := startsAux bs 0

def partVal (l : List Int) (bs : List Nat) : Int :=
  ((bs.zip (starts bs)).map (fun (p : Nat × Nat) => (p.1 : Int) * blockMax l p.2 p.1)).sum

def IsPartition (n k : Nat) (bs : List Nat) : Prop :=
  (∀ b ∈ bs, 1 ≤ b ∧ b ≤ k) ∧ bs.sum = n

def tuplesOfLen (k : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | (m + 1) =>
    (List.range k).flatMap (fun i => (tuplesOfLen k m).map (fun t => (i + 1) :: t))

def partitions (n k : Nat) : List (List Nat) :=
  List.filter (fun bs => bs.sum == n)
    ((List.range (n + 1)).flatMap (fun m => tuplesOfLen k m))

def bestOf (l : List Int) (k : Nat) : Int := maxD ((partitions l.length k).map (partVal l))

def EntriesBounded (arr : Slice Std.I64) (lo hi : Int) : Prop :=
  ∀ x ∈ vals arr, lo ≤ x ∧ x ≤ hi

/-- The function returns a result r, and r equals the maximum of S(P) over all valid partitions P of arr into contiguous blocks of length at most k. A valid partition P is a sequence of positive block lengths b_1, ..., b_m (m >= 1) such that 1 <= b_j <= k for all j and sum_{j=1}^m b_j = len(arr). For such a partition, let start_1 = 0 and start_{j+1} = start_j + b_j for 1 <= j < m. Define M_j = max { arr[t] | start_j <= t < start_j + b_j } (the maximum over the j-th block). Then S(P) = sum_{j=1}^m b_j * M_j.
  Preconditions: len(arr) >= 1; 1 <= k <= len(arr); for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
theorem spec_1 (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∃ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r ∧
        r.val = bestOf (vals arr) k.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∃ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r ∧
        r.val = bestOf (vals arr) k.val.toNat) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, overflow, or panic).
  Preconditions: len(arr) >= 1; 1 <= k <= len(arr); for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
theorem spec_2 (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∃ r : Std.I64, Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∃ r : Std.I64, Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= sum_{i=0}^{len(arr)-1} arr[i].
  Preconditions: len(arr) >= 1; 1 <= k <= len(arr); for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
theorem spec_3 (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        (vals arr).sum ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        (vals arr).sum ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= len(arr) * max { arr[i] | 0 <= i < len(arr) }.
  Preconditions: len(arr) >= 1; 1 <= k <= len(arr); for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
theorem spec_4 (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        r.val ≤ (arr.val.length : Int) * maxD (vals arr) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        r.val ≤ (arr.val.length : Int) * maxD (vals arr)) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i=0}^{len(arr)-1} arr[i].
  Preconditions: len(arr) >= 1; k = 1; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
theorem spec_5 (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k : k.val = 1)
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        r.val = (vals arr).sum := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k : k.val = 1)
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        r.val = (vals arr).sum) := by
  sorry

/-- Whenever the function returns a result r, r = len(arr) * max { arr[i] | 0 <= i < len(arr) }.
  Preconditions: len(arr) >= 1; k = len(arr); for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
theorem spec_6 (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k : k.val = (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        r.val = (arr.val.length : Int) * maxD (vals arr) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k : k.val = (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        r.val = (arr.val.length : Int) * maxD (vals arr)) := by
  sorry

/-- Whenever the function returns a result r, r = len(arr) * c.
  Preconditions: len(arr) >= 1; 1 <= k <= len(arr); there exists an integer c such that for every i with 0 <= i < len(arr), arr[i] = c, and 0 <= c <= 10^9. -/
theorem spec_7 (arr : Slice Std.I64) (k : Std.I64) (c : Int)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_const : ∀ x ∈ vals arr, x = c)
    (h_c : 0 ≤ c ∧ c ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        r.val = (arr.val.length : Int) * c := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64) (c : Int)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_const : ∀ x ∈ vals arr, x = c)
    (h_c : 0 ≤ c ∧ c ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        r.val = (arr.val.length : Int) * c) := by
  sorry

/-- Let r1 be the result of max_sum_after_partitioning(arr, k1) and r2 be the result of max_sum_after_partitioning(arr, k2). Whenever both calls return results, r1 <= r2.
  Preconditions: len(arr) >= 1; 1 <= k1 <= k2 <= len(arr); for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
theorem spec_8 (arr : Slice Std.I64) (k1 k2 : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k1_lo : 1 ≤ k1.val) (h_k12 : k1.val ≤ k2.val)
    (h_k2_hi : k2.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∀ r1 r2 : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k1 = ok r1 →
        Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k2 = ok r2 →
          r1.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64) (k1 k2 : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k1_lo : 1 ≤ k1.val) (h_k12 : k1.val ≤ k2.val)
    (h_k2_hi : k2.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∀ r1 r2 : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k1 = ok r1 →
        Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k2 = ok r2 →
          r1.val ≤ r2.val) := by
  sorry

/-- Let r be the result of max_sum_after_partitioning(arr, k) and r' be the result of max_sum_after_partitioning(arr', k). Whenever both calls return results, r <= r'.
  Preconditions: len(arr) = len(arr') = n >= 1; 1 <= k <= n; for every i with 0 <= i < n, 0 <= arr[i] <= arr'[i] <= 10^9. -/
theorem spec_9 (arr arr' : Slice Std.I64) (k : Std.I64) (n : Nat)
    (h_n : arr.val.length = n) (h_n' : arr'.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_le : List.Forall₂ (fun (x y : Std.I64) => 0 ≤ x.val ∧ x.val ≤ y.val ∧ y.val ≤ 10 ^ 9)
      arr.val arr') :
    ∀ r r' : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr' k = ok r' →
          r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr arr' : Slice Std.I64) (k : Std.I64) (n : Nat)
    (h_n : arr.val.length = n) (h_n' : arr'.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_le : List.Forall₂ (fun (x y : Std.I64) => 0 ≤ x.val ∧ x.val ≤ y.val ∧ y.val ≤ 10 ^ 9)
      arr.val arr'), ∀ r r' : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr' k = ok r' →
          r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r, and there exists a valid partition P of arr into contiguous blocks of length at most k such that S(P) = r, where valid partition and S are defined as in the main specification.
  Preconditions: len(arr) >= 1; 1 <= k <= len(arr); for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
theorem spec_10 (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∃ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r ∧
        ∃ bs : List Nat,
          IsPartition arr.val.length k.val.toNat bs ∧ partVal (vals arr) bs = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∃ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r ∧
        ∃ bs : List Nat,
          IsPartition arr.val.length k.val.toNat bs ∧ partVal (vals arr) bs = r.val) := by
  sorry

/-- The function returns a result r, and for every valid partition P of arr into contiguous blocks of length at most k, S(P) <= r, where valid partition and S are defined as in the main specification.
  Preconditions: len(arr) >= 1; 1 <= k <= len(arr); for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
theorem spec_11 (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∃ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r ∧
        ∀ bs : List Nat,
          IsPartition arr.val.length k.val.toNat bs → partVal (vals arr) bs ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (h_len : 1 ≤ arr.val.length)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (arr.val.length : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∃ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r ∧
        ∀ bs : List Nat,
          IsPartition arr.val.length k.val.toNat bs → partVal (vals arr) bs ≤ r.val) := by
  sorry

/-- Let r be the result of max_sum_after_partitioning(arr, k) and r' be the result of max_sum_after_partitioning(arr', k), where arr'[i] = arr[i] + c for all i. Whenever both calls return results, r' = r + c * n.
  Preconditions: len(arr) = n >= 1; 1 <= k <= n; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9; let c be an integer such that for every i with 0 <= i < n, 0 <= arr[i] + c <= 10^9. -/
theorem spec_12 (arr arr' : Slice Std.I64) (k : Std.I64) (n : Nat) (c : Int)
    (h_n : arr.val.length = n) (h_n' : arr'.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9))
    (h_shift : ∀ (i : Nat) (x x' : Std.I64),
      arr.val[i]? = some x → arr'.val[i]? = some x' → x'.val = x.val + c)
    (h_range : ∀ (i : Nat) (x : Std.I64),
      arr.val[i]? = some x → 0 ≤ x.val + c ∧ x.val + c ≤ 10 ^ 9) :
    ∀ r r' : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr' k = ok r' →
          r'.val = r.val + c * (n : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr arr' : Slice Std.I64) (k : Std.I64) (n : Nat) (c : Int)
    (h_n : arr.val.length = n) (h_n' : arr'.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9))
    (h_shift : ∀ (i : Nat) (x x' : Std.I64),
      arr.val[i]? = some x → arr'.val[i]? = some x' → x'.val = x.val + c)
    (h_range : ∀ (i : Nat) (x : Std.I64),
      arr.val[i]? = some x → 0 ≤ x.val + c ∧ x.val + c ≤ 10 ^ 9), ∀ r r' : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr' k = ok r' →
          r'.val = r.val + c * (n : Int)) := by
  sorry

/-- Let r be the result of max_sum_after_partitioning(arr, k). Whenever the function returns a result r, r >= rA + rB.
  Preconditions: len(arr) = n >= 2; 1 <= k <= n; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9; let s be an integer with 1 <= s < n. Let A = arr[0..s-1] and B = arr[s..n-1]. Let rA be the maximum sum for A with block size at most k (defined as in the main specification), and rB be the maximum sum for B with block size at most k. -/
theorem spec_13 (arr : Slice Std.I64) (k : Std.I64) (n s : Nat)
    (h_n : arr.val.length = n) (h_n_ge : 2 ≤ n)
    (h_s_lo : 1 ≤ s) (h_s_hi : s < n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        bestOf ((vals arr).take s) k.val.toNat +
          bestOf ((vals arr).drop s) k.val.toNat ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64) (n s : Nat)
    (h_n : arr.val.length = n) (h_n_ge : 2 ≤ n)
    (h_s_lo : 1 ≤ s) (h_s_hi : s < n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        bestOf ((vals arr).take s) k.val.toNat +
          bestOf ((vals arr).drop s) k.val.toNat ≤ r.val) := by
  sorry

/-- Let r be the result of max_sum_after_partitioning(arr, k) and r' be the result of max_sum_after_partitioning(arr_rev, k), where arr_rev[i] = arr[n-1-i] for all i. Whenever both calls return results, r = r'.
  Preconditions: len(arr) = n >= 1; 1 <= k <= n; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9. -/
theorem spec_14 (arr arr_rev : Slice Std.I64) (k : Std.I64) (n : Nat)
    (h_n : arr.val.length = n) (h_n_rev : arr_rev.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9))
    (h_rev : ∀ (i : Nat) (x y : Std.I64),
      arr.val[i]? = some x → arr_rev.val[n - 1 - i]? = some y → y.val = x.val) :
    ∀ r r' : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr_rev k = ok r' →
          r.val = r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (arr arr_rev : Slice Std.I64) (k : Std.I64) (n : Nat)
    (h_n : arr.val.length = n) (h_n_rev : arr_rev.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9))
    (h_rev : ∀ (i : Nat) (x y : Std.I64),
      arr.val[i]? = some x → arr_rev.val[n - 1 - i]? = some y → y.val = x.val), ∀ r r' : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr_rev k = ok r' →
          r.val = r'.val) := by
  sorry

/-- Let F(A,q) be the maximum of S(P) over all partitions P of A into contiguous blocks of length at most q, with F(empty,q)=0, where S(P) is defined as in the main specification. The function returns a result r, and r = max_{1<=b<=min(k,n)} ( b * max{arr[t] | 0<=t<b} + F(arr[b..n-1], k) ).
  Preconditions: len(arr)=n>=1; 1<=k<=n; for every i with 0<=i<n, 0<=arr[i]<=10^9. -/
theorem spec_15 (arr : Slice Std.I64) (k : Std.I64) (n : Nat)
    (h_n : arr.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∃ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r ∧
        r.val = maxD ((List.range (min k.val.toNat n)).map (fun i =>
          let b : Nat := i + 1
          (b : Int) * blockMax (vals arr) 0 b + bestOf ((vals arr).drop b) k.val.toNat)) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64) (n : Nat)
    (h_n : arr.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∃ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r ∧
        r.val = maxD ((List.range (min k.val.toNat n)).map (fun i =>
          let b : Nat := i + 1
          (b : Int) * blockMax (vals arr) 0 b + bestOf ((vals arr).drop b) k.val.toNat))) := by
  sorry

/-- Whenever the function returns a result r, r >= k * max { arr[i] | 0 <= i < len(arr) }.
  Preconditions: len(arr)=n>=1; 1<=k<=n; for every i with 0<=i<n, 0<=arr[i]<=10^9. -/
theorem spec_16 (arr : Slice Std.I64) (k : Std.I64) (n : Nat)
    (h_n : arr.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)) :
    ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        k.val * maxD (vals arr) ≤ r.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64) (n : Nat)
    (h_n : arr.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_arr : EntriesBounded arr 0 (10 ^ 9)), ∀ r : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        k.val * maxD (vals arr) ≤ r.val) := by
  sorry

/-- Let r be the result of max_sum_after_partitioning(arr, k) and r' be the result of max_sum_after_partitioning(arr_scaled, k), where arr_scaled[i]=alpha*arr[i] for all i. Whenever both calls return results, r' = alpha * r.
  Preconditions: len(arr)=n>=1; 1<=k<=n; for every i with 0<=i<n, 0<=arr[i]<=10^9; let alpha be an integer with alpha>=0 and 0<=alpha*arr[i]<=10^9 for every i. -/
theorem spec_17 (arr arr_scaled : Slice Std.I64) (k : Std.I64) (n : Nat) (alpha : Int)
    (h_n : arr.val.length = n) (h_n' : arr_scaled.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_alpha : 0 ≤ alpha)
    (h_arr : EntriesBounded arr 0 (10 ^ 9))
    (h_scale : ∀ (i : Nat) (x y : Std.I64),
      arr.val[i]? = some x → arr_scaled.val[i]? = some y → y.val = alpha * x.val)
    (h_range : ∀ (i : Nat) (x : Std.I64),
      arr.val[i]? = some x → 0 ≤ alpha * x.val ∧ alpha * x.val ≤ 10 ^ 9) :
    ∀ r r' : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr_scaled k = ok r' →
          r'.val = alpha * r.val := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (arr arr_scaled : Slice Std.I64) (k : Std.I64) (n : Nat) (alpha : Int)
    (h_n : arr.val.length = n) (h_n' : arr_scaled.val.length = n) (h_n_ge : 1 ≤ n)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ (n : Int))
    (h_alpha : 0 ≤ alpha)
    (h_arr : EntriesBounded arr 0 (10 ^ 9))
    (h_scale : ∀ (i : Nat) (x y : Std.I64),
      arr.val[i]? = some x → arr_scaled.val[i]? = some y → y.val = alpha * x.val)
    (h_range : ∀ (i : Nat) (x : Std.I64),
      arr.val[i]? = some x → 0 ≤ alpha * x.val ∧ alpha * x.val ≤ 10 ^ 9), ∀ r r' : Std.I64,
      Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr k = ok r →
        Aegis.MaxSumAfterPartitioning.max_sum_after_partitioning arr_scaled k = ok r' →
          r'.val = alpha * r.val) := by
  sorry

end AegisSpec.MaxSumAfterPartitioning
