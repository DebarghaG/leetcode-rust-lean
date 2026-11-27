import Aegis.MaxJumps.Code.Funs

/-!
# Specifications of `Aegis.MaxJumps.max_jumps`

LeetCode problem `jump-game-v`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxJumps

  namespace AegisSpec.MaxJumps

  def entry (arr : Slice I64) (i : Nat) : Int := (arr.val[i]!).val

  def IsJump (arr : Slice I64) (d : I64) (i j : Nat) : Prop :=
    |(i : Int) - (j : Int)| ≤ d.val ∧
      entry arr i > entry arr j ∧
      (∀ k : Nat, min i j < k → k < max i j → entry arr i > entry arr k)

  def IsJumpPath (arr : Slice I64) (d : I64) (p : List Nat) : Prop :=
    1 ≤ p.length ∧
      (∀ t : Nat, t < p.length → p[t]! < arr.val.length) ∧
      (∀ t : Nat, t + 1 < p.length → IsJump arr d (p[t]!) (p[t + 1]!))

  def IsMonoSeg (arr : Slice I64) (l r : Nat) : Prop :=
    l ≤ r ∧ r < arr.val.length ∧
      ((∀ t : Nat, l ≤ t → t < r → entry arr t < entry arr (t + 1)) ∨
        (∀ t : Nat, l ≤ t → t < r → entry arr t > entry arr (t + 1)))

  def rev (arr : Slice I64) : Slice I64 :=
    ⟨arr.val.reverse.length, Aeneas.Data.ListN.ListN.fromList arr.val.reverse, by
      rw [List.length_reverse]
      rw [show arr.val.length = arr.leng from Aeneas.Data.ListN.ListN_length arr.list]
      exact arr.bound⟩

  /-- The function returns a result r, and r equals the maximum length L of a jump path. A jump path is a finite sequence p_0, p_1, ..., p_{L-1} of indices (with L >= 1) such that each p_t satisfies 0 <= p_t < len(arr), and for every t with 0 <= t < L-1, the step from p_t to p_{t+1} satisfies: |p_t - p_{t+1}| <= d, arr[p_t] > arr[p_{t+1}], and arr[p_t] > arr[k] for every k with min(p_t, p_{t+1}) < k < max(p_t, p_{t+1}).
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr). -/
  theorem spec_1 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)) :
      ∃ r : I64, max_jumps arr d = ok r ∧
        (∃ p : List Nat, IsJumpPath arr d p ∧ (p.length : Int) = r.val) ∧
        (∀ p : List Nat, IsJumpPath arr d p → (p.length : Int) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)), ∃ r : I64, max_jumps arr d = ok r ∧
          (∃ p : List Nat, IsJumpPath arr d p ∧ (p.length : Int) = r.val) ∧
          (∀ p : List Nat, IsJumpPath arr d p → (p.length : Int) ≤ r.val)) := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr). -/
  theorem spec_2 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)) :
      ∃ r : I64, max_jumps arr d = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)), ∃ r : I64, max_jumps arr d = ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have r >= 1.
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr). -/
  theorem spec_3 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)) :
      ∀ r : I64, max_jumps arr d = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)), ∀ r : I64, max_jumps arr d = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, we have r <= len(arr).
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr). -/
  theorem spec_4 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)) :
      ∀ r : I64, max_jumps arr d = ok r → r.val ≤ (arr.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)), ∀ r : I64, max_jumps arr d = ok r → r.val ≤ (arr.val.length : Int)) := by
    sorry

  /-- The function returns a result r, and there exists a jump path p_0, p_1, ..., p_{r-1} of length exactly r such that each p_t is in [0, len(arr)) and for every 0 <= t < r-1, |p_t - p_{t+1}| <= d, arr[p_t] > arr[p_{t+1}], and arr[p_t] > arr[k] for all k with min(p_t, p_{t+1}) < k < max(p_t, p_{t+1}).
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr). -/
  theorem spec_5 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)) :
      ∃ r : I64, max_jumps arr d = ok r ∧
        (∃ p : List Nat, IsJumpPath arr d p ∧ (p.length : Int) = r.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)), ∃ r : I64, max_jumps arr d = ok r ∧
          (∃ p : List Nat, IsJumpPath arr d p ∧ (p.length : Int) = r.val)) := by
    sorry

  /-- The function returns a result r, and for every jump path p_0, p_1, ..., p_{L-1} (with L >= 1, each p_t in [0, len(arr)), and for every 0 <= t < L-1 the step is a valid jump: |p_t - p_{t+1}| <= d, arr[p_t] > arr[p_{t+1}], and arr[p_t] > arr[k] for all min(p_t, p_{t+1}) < k < max(p_t, p_{t+1})), we have L <= r.
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr). -/
  theorem spec_6 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)) :
      ∃ r : I64, max_jumps arr d = ok r ∧
        (∀ p : List Nat, IsJumpPath arr d p → (p.length : Int) ≤ r.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)), ∃ r : I64, max_jumps arr d = ok r ∧
          (∀ p : List Nat, IsJumpPath arr d p → (p.length : Int) ≤ r.val)) := by
    sorry

  /-- The function returns a result r with r = 1.
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr); and for every i, j with 0 <= i, j < len(arr), arr[i] = arr[j]. -/
  theorem spec_7 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int))
      (h_const : ∀ i j : Nat, i < arr.val.length → j < arr.val.length →
        entry arr i = entry arr j) :
      ∃ r : I64, max_jumps arr d = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int))
        (h_const : ∀ i j : Nat, i < arr.val.length → j < arr.val.length →
          entry arr i = entry arr j), ∃ r : I64, max_jumps arr d = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r with r = len(arr).
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr); and for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]. -/
  theorem spec_8 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int))
      (h_mono : ∀ i : Nat, i < arr.val.length - 1 → entry arr i < entry arr (i + 1)) :
      ∃ r : I64, max_jumps arr d = ok r ∧ r.val = (arr.val.length : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int))
        (h_mono : ∀ i : Nat, i < arr.val.length - 1 → entry arr i < entry arr (i + 1)), ∃ r : I64, max_jumps arr d = ok r ∧ r.val = (arr.val.length : Int)) := by
    sorry

  /-- The function returns a result r, and r equals the maximum length of a contiguous strictly monotonic segment of arr. A contiguous segment is a pair (l, r) with 0 <= l <= r < len(arr); its length is r - l + 1; it is strictly monotonic if either (for every t with l <= t < r, arr[t] < arr[t+1]) or (for every t with l <= t < r, arr[t] > arr[t+1]).
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr); and d = 1. -/
  theorem spec_9 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int))
      (h_d_one : d.val = 1) :
      ∃ r : I64, max_jumps arr d = ok r ∧
        (∃ l r' : Nat, IsMonoSeg arr l r' ∧ ((r' - l + 1 : Nat) : Int) = r.val) ∧
        (∀ l r' : Nat, IsMonoSeg arr l r' → ((r' - l + 1 : Nat) : Int) ≤ r.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int))
        (h_d_one : d.val = 1), ∃ r : I64, max_jumps arr d = ok r ∧
          (∃ l r' : Nat, IsMonoSeg arr l r' ∧ ((r' - l + 1 : Nat) : Int) = r.val) ∧
          (∀ l r' : Nat, IsMonoSeg arr l r' → ((r' - l + 1 : Nat) : Int) ≤ r.val)) := by
    sorry

  /-- The function returns a result r, and r is at least the maximum length of a contiguous strictly monotonic segment of arr, where a contiguous segment is a pair (l, r) with 0 <= l <= r < len(arr), its length is r - l + 1, and it is strictly monotonic if either (for every t with l <= t < r, arr[t] < arr[t+1]) or (for every t with l <= t < r, arr[t] > arr[t+1]).
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr). -/
  theorem spec_10 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)) :
      ∃ r : I64, max_jumps arr d = ok r ∧
        (∀ l r' : Nat, IsMonoSeg arr l r' → ((r' - l + 1 : Nat) : Int) ≤ r.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)), ∃ r : I64, max_jumps arr d = ok r ∧
          (∀ l r' : Nat, IsMonoSeg arr l r' → ((r' - l + 1 : Nat) : Int) ≤ r.val)) := by
    sorry

  /-- The function returns a result r, and r >= 2 if and only if there exist indices i, j with 0 <= i, j < len(arr) and i != j such that j is a valid jump from i, meaning |i - j| <= d, arr[i] > arr[j], and arr[i] > arr[k] for every k with min(i, j) < k < max(i, j).
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr). -/
  theorem spec_11 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)) :
      ∃ r : I64, max_jumps arr d = ok r ∧
        (2 ≤ r.val ↔
          ∃ i j : Nat, i < arr.val.length ∧ j < arr.val.length ∧ i ≠ j ∧ IsJump arr d i j) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)), ∃ r : I64, max_jumps arr d = ok r ∧
          (2 ≤ r.val ↔
            ∃ i j : Nat, i < arr.val.length ∧ j < arr.val.length ∧ i ≠ j ∧ IsJump arr d i j)) := by
    sorry

  /-- The value returned by max_jumps on arr with d equals the value returned by max_jumps on B with d.
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr). Additionally, let c be an integer and B an array of integers with len(B) = len(arr), B[i] = arr[i] + c for all 0 <= i < len(arr), and 1 <= B[i] <= 100000 for all 0 <= i < len(arr). -/
  theorem spec_12 (arr B : Slice I64) (d : I64) (c : Int)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int))
      (hB_len : B.val.length = arr.val.length)
      (hB : ∀ i : Nat, i < arr.val.length → entry B i = entry arr i + c)
      (hB_lo : ∀ i : Nat, i < B.val.length → 1 ≤ entry B i)
      (hB_hi : ∀ i : Nat, i < B.val.length → entry B i ≤ 100000) :
      ∀ r1 r2 : I64, max_jumps arr d = ok r1 → max_jumps B d = ok r2 → r1.val = r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr B : Slice I64) (d : I64) (c : Int)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int))
        (hB_len : B.val.length = arr.val.length)
        (hB : ∀ i : Nat, i < arr.val.length → entry B i = entry arr i + c)
        (hB_lo : ∀ i : Nat, i < B.val.length → 1 ≤ entry B i)
        (hB_hi : ∀ i : Nat, i < B.val.length → entry B i ≤ 100000), ∀ r1 r2 : I64, max_jumps arr d = ok r1 → max_jumps B d = ok r2 → r1.val = r2.val) := by
    sorry

  /-- Let n = len(arr) and define rev(arr) by rev(arr)[i] = arr[n-1-i] for 0 <= i < n. Then the value returned by max_jumps on rev(arr) with d equals the value returned by max_jumps on arr with d.
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; 1 <= d <= len(arr). -/
  theorem spec_13 (arr : Slice I64) (d : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)) :
      ∀ r1 r2 : I64, max_jumps (rev arr) d = ok r1 → max_jumps arr d = ok r2 →
        r1.val = r2.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr : Slice I64) (d : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d_pos : 1 ≤ d.val) (h_d_le : d.val ≤ (arr.val.length : Int)), ∀ r1 r2 : I64, max_jumps (rev arr) d = ok r1 → max_jumps arr d = ok r2 →
          r1.val = r2.val) := by
    sorry

  /-- The value returned by max_jumps on arr with d1 is at most the value returned by max_jumps on arr with d2.
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000; let d1 and d2 be integers with 1 <= d1 <= d2 <= len(arr). -/
  theorem spec_14 (arr : Slice I64) (d1 d2 : I64)
      (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
      (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
      (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
      (h_d1_pos : 1 ≤ d1.val) (h_d1_le : d1.val ≤ d2.val)
      (h_d2_le : d2.val ≤ (arr.val.length : Int)) :
      ∀ r1 r2 : I64, max_jumps arr d1 = ok r1 → max_jumps arr d2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (arr : Slice I64) (d1 d2 : I64)
        (h_len_pos : 1 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 1000)
        (h_entry_lo : ∀ i : Nat, i < arr.val.length → 1 ≤ entry arr i)
        (h_entry_hi : ∀ i : Nat, i < arr.val.length → entry arr i ≤ 100000)
        (h_d1_pos : 1 ≤ d1.val) (h_d1_le : d1.val ≤ d2.val)
        (h_d2_le : d2.val ≤ (arr.val.length : Int)), ∀ r1 r2 : I64, max_jumps arr d1 = ok r1 → max_jumps arr d2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  end AegisSpec.MaxJumps
