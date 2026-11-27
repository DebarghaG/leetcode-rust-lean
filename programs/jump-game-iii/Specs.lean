import Aegis.CanReach.Code.Funs

/-!
# Specifications of `Aegis.CanReach.can_reach`

LeetCode problem `jump-game-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanReach

  def arrVals (arr : Slice Std.I64) : List Int := arr.val.map (fun v : Std.I64 => v.val)

  def arrAt? (arr : Slice Std.I64) (i : Int) : Option Int :=
    if 0 ≤ i then (arrVals arr)[i.toNat]? else none

  def arrSize (arr : Slice Std.I64) : Int := (arr.val.length : Int)

  def Jump (arr : Slice Std.I64) (i j : Int) : Prop :=
    ∃ a : Int, arrAt? arr i = some a ∧ (j = i + a ∨ j = i - a)

  def JumpPath (arr : Slice Std.I64) : List Int → Prop
    | [] => True
    | [_] => True
    | i :: j :: rest => Jump arr i j ∧ JumpPath arr (j :: rest)

  def IsZeroPath (arr : Slice Std.I64) (start : Int) (p : List Int) : Prop :=
    p.head? = some start ∧
    (∀ i ∈ p, 0 ≤ i ∧ i < arrSize arr) ∧
    JumpPath arr p ∧
    ∃ z : Int, p.getLast? = some z ∧ arrAt? arr z = some 0

  def Reachable (arr : Slice Std.I64) (start j : Int) : Prop :=
    ∃ p : List Int,
      p.head? = some start ∧ p.getLast? = some j ∧
        (∀ i ∈ p, 0 ≤ i ∧ i < arrSize arr) ∧ JumpPath arr p

  def reverseSlice (arr : Slice Std.I64) : Slice Std.I64 :=
    ⟨arr.val.reverse.length,
      Aeneas.Data.ListN.ListN.fromList arr.val.reverse,
      by
        rw [List.length_reverse]
        rw [show arr.val.length = arr.leng from Aeneas.Data.ListN.ListN_length arr.list]
        exact arr.bound⟩

  theorem arrVals_reverseSlice (arr : Slice Std.I64) :
      arrVals (reverseSlice arr) = (arrVals arr).reverse := by
    simp only [arrVals, reverseSlice, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse,
      List.map_reverse]

  theorem arrSize_reverseSlice (arr : Slice Std.I64) : arrSize (reverseSlice arr) = arrSize arr := by
    simp [arrSize, reverseSlice, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse,
      List.length_reverse]

  /-- The function returns a result r and, for that r, r = true if and only if there exists a finite sequence of indices p_0, ..., p_k with k >= 0 such that p_0 = start, for every t with 0 <= t <= k we have 0 <= p_t < n, for every t with 0 <= t < k we have p_{t+1} = p_t + arr[p_t] or p_{t+1} = p_t - arr[p_t], and arr[p_k] = 0. Equivalently, start can reach a zero-valued index by zero or more legal jumps.
    Preconditions: Let n = len(arr). The input satisfies the problem constraints: n >= 1; n <= 50000; for every i with 0 <= i < n, 0 <= arr[i] < n; and 0 <= start < n. -/
  theorem spec_1 (arr : Slice Std.I64) (start : Std.I64)
      (hn1 : 1 ≤ arrSize arr)
      (hn2 : arrSize arr ≤ 50000)
      (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
        ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
      (hstart : 0 ≤ start.val ∧ start.val < arrSize arr) :
      ∃ r : Bool, Aegis.CanReach.can_reach arr start = ok r ∧
        (r = true ↔ ∃ p : List Int, IsZeroPath arr start.val p) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (start : Std.I64)
        (hn1 : 1 ≤ arrSize arr)
        (hn2 : arrSize arr ≤ 50000)
        (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
          ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
        (hstart : 0 ≤ start.val ∧ start.val < arrSize arr), ∃ r : Bool, Aegis.CanReach.can_reach arr start = ok r ∧
          (r = true ↔ ∃ p : List Int, IsZeroPath arr start.val p)) := by
    sorry

  /-- The function returns a result r, either true or false; it does not fail, panic, overflow, or access an index outside 0 .. n - 1.
    Preconditions: Let n = len(arr). The input satisfies the problem constraints: n >= 1; n <= 50000; for every i with 0 <= i < n, 0 <= arr[i] < n; and 0 <= start < n. -/
  theorem spec_2 (arr : Slice Std.I64) (start : Std.I64)
      (hn1 : 1 ≤ arrSize arr)
      (hn2 : arrSize arr ≤ 50000)
      (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
        ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
      (hstart : 0 ≤ start.val ∧ start.val < arrSize arr) :
      ∃ r : Bool, Aegis.CanReach.can_reach arr start = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (start : Std.I64)
        (hn1 : 1 ≤ arrSize arr)
        (hn2 : arrSize arr ≤ 50000)
        (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
          ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
        (hstart : 0 ≤ start.val ∧ start.val < arrSize arr), ∃ r : Bool, Aegis.CanReach.can_reach arr start = ok r) := by
    sorry

  /-- The function returns true.
    Preconditions: Let n = len(arr). The input satisfies the problem constraints: n >= 1; n <= 50000; for every i with 0 <= i < n, 0 <= arr[i] < n; 0 <= start < n; and arr[start] = 0. -/
  theorem spec_3 (arr : Slice Std.I64) (start : Std.I64)
      (hn1 : 1 ≤ arrSize arr)
      (hn2 : arrSize arr ≤ 50000)
      (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
        ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
      (hstart : 0 ≤ start.val ∧ start.val < arrSize arr)
      (hzero : arrAt? arr start.val = some 0) :
      ∃ r : Bool, Aegis.CanReach.can_reach arr start = ok r ∧ r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (start : Std.I64)
        (hn1 : 1 ≤ arrSize arr)
        (hn2 : arrSize arr ≤ 50000)
        (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
          ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
        (hstart : 0 ≤ start.val ∧ start.val < arrSize arr)
        (hzero : arrAt? arr start.val = some 0), ∃ r : Bool, Aegis.CanReach.can_reach arr start = ok r ∧ r = true) := by
    sorry

  /-- The function returns false.
    Preconditions: Let n = len(arr). The input satisfies the problem constraints: n >= 1; n <= 50000; for every i with 0 <= i < n, 0 <= arr[i] < n; 0 <= start < n; and for every i with 0 <= i < n, arr[i] != 0. -/
  theorem spec_4 (arr : Slice Std.I64) (start : Std.I64)
      (hn1 : 1 ≤ arrSize arr)
      (hn2 : arrSize arr ≤ 50000)
      (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
        ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
      (hstart : 0 ≤ start.val ∧ start.val < arrSize arr)
      (hnonzero : ∀ i : Int, 0 ≤ i → i < arrSize arr → arrAt? arr i ≠ some 0) :
      ∃ r : Bool, Aegis.CanReach.can_reach arr start = ok r ∧ r = false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (start : Std.I64)
        (hn1 : 1 ≤ arrSize arr)
        (hn2 : arrSize arr ≤ 50000)
        (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
          ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
        (hstart : 0 ≤ start.val ∧ start.val < arrSize arr)
        (hnonzero : ∀ i : Int, 0 ≤ i → i < arrSize arr → arrAt? arr i ≠ some 0), ∃ r : Bool, Aegis.CanReach.can_reach arr start = ok r ∧ r = false) := by
    sorry

  /-- Whenever the function returns true, there exists a finite sequence of indices p_0, ..., p_k with k >= 0 such that p_0 = start, all p_t lie in 0 .. n - 1, the indices p_0, ..., p_k are pairwise distinct, for every t with 0 <= t < k we have p_{t+1} = p_t + arr[p_t] or p_{t+1} = p_t - arr[p_t], and arr[p_k] = 0.
    Preconditions: Let n = len(arr). The input satisfies the problem constraints: n >= 1; n <= 50000; for every i with 0 <= i < n, 0 <= arr[i] < n; and 0 <= start < n. -/
  theorem spec_5 (arr : Slice Std.I64) (start : Std.I64)
      (hn1 : 1 ≤ arrSize arr)
      (hn2 : arrSize arr ≤ 50000)
      (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
        ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
      (hstart : 0 ≤ start.val ∧ start.val < arrSize arr) :
      Aegis.CanReach.can_reach arr start = ok true →
        ∃ p : List Int, IsZeroPath arr start.val p ∧ p.Nodup := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (start : Std.I64)
        (hn1 : 1 ≤ arrSize arr)
        (hn2 : arrSize arr ≤ 50000)
        (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
          ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
        (hstart : 0 ≤ start.val ∧ start.val < arrSize arr), Aegis.CanReach.can_reach arr start = ok true →
          ∃ p : List Int, IsZeroPath arr start.val p ∧ p.Nodup) := by
    sorry

  /-- Whenever the function returns true, there exists a witnessing sequence p_0, ..., p_k to a zero-valued index, satisfying p_0 = start, all p_t in 0 .. n - 1, each step p_{t+1} = p_t + arr[p_t] or p_{t+1} = p_t - arr[p_t] when 0 <= t < k, and arr[p_k] = 0, with k <= n - 1.
    Preconditions: Let n = len(arr). The input satisfies the problem constraints: n >= 1; n <= 50000; for every i with 0 <= i < n, 0 <= arr[i] < n; and 0 <= start < n. -/
  theorem spec_6 (arr : Slice Std.I64) (start : Std.I64)
      (hn1 : 1 ≤ arrSize arr)
      (hn2 : arrSize arr ≤ 50000)
      (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
        ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
      (hstart : 0 ≤ start.val ∧ start.val < arrSize arr) :
      Aegis.CanReach.can_reach arr start = ok true →
        ∃ p : List Int, IsZeroPath arr start.val p ∧ (p.length : Int) ≤ arrSize arr := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (start : Std.I64)
        (hn1 : 1 ≤ arrSize arr)
        (hn2 : arrSize arr ≤ 50000)
        (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
          ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
        (hstart : 0 ≤ start.val ∧ start.val < arrSize arr), Aegis.CanReach.can_reach arr start = ok true →
          ∃ p : List Int, IsZeroPath arr start.val p ∧ (p.length : Int) ≤ arrSize arr) := by
    sorry

  /-- Define arr_rev by arr_rev[i] = arr[n - 1 - i] for every i with 0 <= i < n, and define start_rev = n - 1 - start. The function returns a result r on (arr, start) and a result r_rev on (arr_rev, start_rev), and r = r_rev.
    Preconditions: Let n = len(arr). The input satisfies the problem constraints: n >= 1; n <= 50000; for every i with 0 <= i < n, 0 <= arr[i] < n; and 0 <= start < n. -/
  theorem spec_7 (arr : Slice Std.I64) (start start_rev : Std.I64)
      (hn1 : 1 ≤ arrSize arr)
      (hn2 : arrSize arr ≤ 50000)
      (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
        ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
      (hstart : 0 ≤ start.val ∧ start.val < arrSize arr)
      (hstart_rev : start_rev.val = arrSize arr - 1 - start.val) :
      ∃ r r_rev : Bool, Aegis.CanReach.can_reach arr start = ok r ∧
        Aegis.CanReach.can_reach (reverseSlice arr) start_rev = ok r_rev ∧ r = r_rev := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (start start_rev : Std.I64)
        (hn1 : 1 ≤ arrSize arr)
        (hn2 : arrSize arr ≤ 50000)
        (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
          ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
        (hstart : 0 ≤ start.val ∧ start.val < arrSize arr)
        (hstart_rev : start_rev.val = arrSize arr - 1 - start.val), ∃ r r_rev : Bool, Aegis.CanReach.can_reach arr start = ok r ∧
          Aegis.CanReach.can_reach (reverseSlice arr) start_rev = ok r_rev ∧ r = r_rev) := by
    sorry

  /-- The function returns a result r on (arr, start) and a result r2 on (arr2, start), and r = r2.
    Preconditions: Let n = len(arr). The input satisfies the problem constraints: n >= 1; n <= 50000; for every i with 0 <= i < n, 0 <= arr[i] < n; and 0 <= start < n. Let R be the set of indices reachable from start under arr by legal jump paths. Let arr2 be any slice of length n such that 0 <= arr2[i] < n for every i with 0 <= i < n, and arr2[i] = arr[i] for every i in R. -/
  theorem spec_8 (arr arr2 : Slice Std.I64) (start : Std.I64)
      (hn1 : 1 ≤ arrSize arr)
      (hn2 : arrSize arr ≤ 50000)
      (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
        ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
      (hstart : 0 ≤ start.val ∧ start.val < arrSize arr)
      (hlen2 : arrSize arr2 = arrSize arr)
      (hvalues2 : ∀ i : Int, 0 ≤ i → i < arrSize arr2 →
        ∃ a : Int, arrAt? arr2 i = some a ∧ 0 ≤ a ∧ a < arrSize arr2)
      (hagree : ∀ i : Int, Reachable arr start.val i → arrAt? arr2 i = arrAt? arr i) :
      ∃ r r2 : Bool, Aegis.CanReach.can_reach arr start = ok r ∧
        Aegis.CanReach.can_reach arr2 start = ok r2 ∧ r = r2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr arr2 : Slice Std.I64) (start : Std.I64)
        (hn1 : 1 ≤ arrSize arr)
        (hn2 : arrSize arr ≤ 50000)
        (hvalues : ∀ i : Int, 0 ≤ i → i < arrSize arr →
          ∃ a : Int, arrAt? arr i = some a ∧ 0 ≤ a ∧ a < arrSize arr)
        (hstart : 0 ≤ start.val ∧ start.val < arrSize arr)
        (hlen2 : arrSize arr2 = arrSize arr)
        (hvalues2 : ∀ i : Int, 0 ≤ i → i < arrSize arr2 →
          ∃ a : Int, arrAt? arr2 i = some a ∧ 0 ≤ a ∧ a < arrSize arr2)
        (hagree : ∀ i : Int, Reachable arr start.val i → arrAt? arr2 i = arrAt? arr i), ∃ r r2 : Bool, Aegis.CanReach.can_reach arr start = ok r ∧
          Aegis.CanReach.can_reach arr2 start = ok r2 ∧ r = r2) := by
    sorry

  end AegisSpec.CanReach
