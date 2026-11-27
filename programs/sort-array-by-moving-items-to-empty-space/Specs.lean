import Aegis.SortArray.Code.Funs

/-!
# Specifications of `Aegis.SortArray.sort_array`

LeetCode problem `sort-array-by-moving-items-to-empty-space`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Data.ListN

namespace AegisSpec.SortArray

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def entry (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

def nth (l : List Int) (i : Nat) : Int := l.getD i 0

def IsTargetA (l : List Int) : Prop := ∀ i, i < l.length → nth l i = (i : Int)

def IsTargetB (l : List Int) : Prop :=
  nth l (l.length - 1) = 0 ∧ ∀ i, i < l.length - 1 → nth l i = (i : Int) + 1

def IsTarget (l : List Int) : Prop := IsTargetA l ∨ IsTargetB l

def Step (l l' : List Int) : Prop :=
  ∃ p q, p < l.length ∧ q < l.length ∧ nth l p = 0 ∧ nth l q ≠ 0 ∧
    l' = (l.set p (nth l q)).set q (nth l p)

def swapAt (l : List Int) (p q : Nat) : List Int := (l.set p (nth l q)).set q (nth l p)

def IsMoveSeqTo (start : List Int) (k : Nat) (seq : List (List Int)) : Prop :=
  seq.length = k + 1 ∧ seq.head? = some start ∧
    (∀ a ∈ seq, a.length = start.length) ∧
    (∀ t, t < k → Step (seq.getD t []) (seq.getD (t + 1) [])) ∧
    ∃ last, seq.getLast? = some last ∧ IsTarget last

def MinMovesTo (l : List Int) (k : Nat) : Prop :=
  (∃ seq, IsMoveSeqTo l k seq) ∧ ∀ k', (∃ seq, IsMoveSeqTo l k' seq) → k ≤ k'

def iter (σ : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => σ (iter σ k x)

def orbit (σ : Nat → Nat) (n x : Nat) : List Nat :=
  (List.range n).filter fun y => (List.range n).any fun k => decide (iter σ k x = y)

def isCycleRep (σ : Nat → Nat) (n x : Nat) : Bool :=
  (orbit σ n x).all fun y => decide (x ≤ y)

def cost (σ : Nat → Nat) (n : Nat) : Int :=
  let c0 := orbit σ n 0
  let others :=
    (List.range n).filter fun x =>
      isCycleRep σ n x && decide (2 ≤ (orbit σ n x).length) && !decide (x ∈ c0)
  (others.map fun x => ((orbit σ n x).length : Int) + 1).sum + ((c0.length : Int) - 1)

def pos (nums : Slice Std.I64) (v : Int) : Nat := (vals nums).idxOf v

def tauA (_n i : Nat) : Nat := i

def tauB (n i : Nat) : Nat := if i + 1 = n then 0 else i + 1

def sigmaA (nums : Slice Std.I64) : Nat → Nat :=
  fun v => tauA (vals nums).length (pos nums (v : Int))

def sigmaB (nums : Slice Std.I64) : Nat → Nat :=
  fun v => tauB (vals nums).length (pos nums (v : Int))

def toI64 (x : Int) : Std.I64 := IScalar.mk (BitVec.ofInt 64 x)

def mirrorVal (nums : Slice Std.I64) (i : Nat) : Int :=
  let n := (vals nums).length
  let v := nth (vals nums) (n - 1 - i)
  if v = 0 then 0 else (n : Int) - v

def mirrorList (nums : Slice Std.I64) : List Std.I64 :=
  (List.range (vals nums).length).map fun i => toI64 (mirrorVal nums i)

def mirror (nums : Slice Std.I64) : Slice Std.I64 :=
  Slice.mk (mirrorList nums).length (ListN.fromList (mirrorList nums)) (by
    have hlen : (mirrorList nums).length = nums.leng := by
      simp only [mirrorList, vals, Slice.val, List.length_map, List.length_range]
      exact ListN_length nums.list
    have hbound := nums.bound
    omega)

/-- Let n = len(nums). For each v with 0 <= v < n, let pos(v) be the unique index i with 0 <= i < n and nums[i] = v. Define target A by tau_A(i) = i for 0 <= i < n, and target B by tau_B(i) = i+1 for 0 <= i < n-1 and tau_B(n-1) = 0. For T in {A,B}, define the permutation sigma_T on {0,...,n-1} by sigma_T(v) = tau_T(pos(v)). For any permutation sigma of {0,...,n-1}, let C0 be the cycle of sigma containing 0, and define cost(sigma) = (|C0|-1) + the sum over all cycles C of sigma with C != C0 and |C| >= 2 of (|C|+1). Whenever sort_array(nums) returns r, r = min(cost(sigma_A), cost(sigma_B)).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r) :
    r.val = min (cost (sigmaA nums) (vals nums).length)
      (cost (sigmaB nums) (vals nums).length) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r), r.val = min (cost (sigmaA nums) (vals nums).length)
      (cost (sigmaB nums) (vals nums).length)) := by
  sorry

/-- sort_array(nums) returns a result r (it does not fail, panic, or overflow).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j) :
    ∃ r, Aegis.SortArray.sort_array nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j), ∃ r, Aegis.SortArray.sort_array nums = ok r) := by
  sorry

/-- Whenever sort_array(nums) returns r, 0 <= r.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_3 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever sort_array(nums) returns r, r <= floor((3*n - 3)/2).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_4 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r) :
    r.val ≤ (((3 * (vals nums).length - 3) / 2 : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r), r.val ≤ (((3 * (vals nums).length - 3) / 2 : Nat) : Int)) := by
  sorry

/-- Whenever sort_array(nums) returns r, r = 0 if and only if either (i) nums[0] = 0 and for every i with 1 <= i < n, nums[i] = i, or (ii) nums[n-1] = 0 and for every i with 0 <= i < n-1, nums[i] = i+1.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_5 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r) :
    (r.val = 0 ↔
      (entry nums 0 = 0 ∧
          ∀ i, 1 ≤ i → i < (vals nums).length → entry nums i = (i : Int)) ∨
        (entry nums ((vals nums).length - 1) = 0 ∧
          ∀ i, i < (vals nums).length - 1 → entry nums i = (i : Int) + 1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r), (r.val = 0 ↔
      (entry nums 0 = 0 ∧
          ∀ i, 1 ≤ i → i < (vals nums).length → entry nums i = (i : Int)) ∨
        (entry nums ((vals nums).length - 1) = 0 ∧
          ∀ i, i < (vals nums).length - 1 → entry nums i = (i : Int) + 1))) := by
  sorry

/-- Whenever sort_array(nums) returns r, there exists a sequence of arrays nums_0, nums_1, ..., nums_r, each of length n, such that nums_0 = nums, nums_r is either target A (nums_r[i] = i for all 0 <= i < n) or target B (nums_r[i] = i+1 for 0 <= i < n-1 and nums_r[n-1] = 0), and for every t with 0 <= t < r, nums_{t+1} is obtained from nums_t by choosing indices p,q with nums_t[p] = 0 and nums_t[q] != 0 and swapping the entries at p and q.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_6 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r) :
    ∃ (k : Nat) (seq : List (List Int)), r.val = (k : Int) ∧ IsMoveSeqTo (vals nums) k seq := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r), ∃ (k : Nat) (seq : List (List Int)), r.val = (k : Int) ∧ IsMoveSeqTo (vals nums) k seq) := by
  sorry

/-- Whenever sort_array(nums) returns r, for every k with 0 <= k < r there is no sequence of arrays nums_0, ..., nums_k, each of length n, such that nums_0 = nums, nums_k is target A or target B as defined in spec_6, and each step swaps 0 with a nonzero entry.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_7 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r)
    (k : Nat) (hk : (k : Int) < r.val) :
    ¬ ∃ seq, IsMoveSeqTo (vals nums) k seq := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r)
    (k : Nat) (hk : (k : Int) < r.val), ¬ ∃ seq, IsMoveSeqTo (vals nums) k seq) := by
  sorry

/-- Whenever sort_array(nums) returns r and n = 3, r <= 2.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_8 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r)
    (h3 : (vals nums).length = 3) :
    r.val ≤ 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r)
    (h3 : (vals nums).length = 3), r.val ≤ 2) := by
  sorry

/-- Whenever sort_array(nums) returns r and n = 4, r <= 3.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_9 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r)
    (h4 : (vals nums).length = 4) :
    r.val ≤ 3 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r)
    (h4 : (vals nums).length = 4), r.val ≤ 3) := by
  sorry

/-- Let F(nums) be the array of length n defined by F(nums)[i] = 0 if nums[n-1-i] = 0, and F(nums)[i] = n - nums[n-1-i] otherwise, for 0 <= i < n. Whenever sort_array(nums) returns r and sort_array(F(nums)) returns r', we have r' = r.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_10 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r r' : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r)
    (hr' : Aegis.SortArray.sort_array (mirror nums) = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r r' : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r)
    (hr' : Aegis.SortArray.sort_array (mirror nums) = ok r'), r'.val = r.val) := by
  sorry

/-- Whenever sort_array(nums) returns r with r > 0, there exist indices p,q with 0 <= p,q < n, nums[p] = 0, and nums[q] != 0 such that, if nums' is obtained from nums by swapping the entries at p and q, then the minimum number of legal moves needed to transform nums' into target A or target B is exactly r-1. Here 'minimum number of legal moves' means the least k for which there is a sequence nums'_0, ..., nums'_k with nums'_0 = nums', nums'_k equal to target A or target B, and each step swapping 0 with a nonzero entry.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_11 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r) (hrpos : 0 < r.val) :
    ∃ (p q k : Nat), p < (vals nums).length ∧ q < (vals nums).length ∧
      entry nums p = 0 ∧ entry nums q ≠ 0 ∧ r.val = (k : Int) + 1 ∧
      MinMovesTo (swapAt (vals nums) p q) k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r) (hrpos : 0 < r.val), ∃ (p q k : Nat), p < (vals nums).length ∧ q < (vals nums).length ∧
      entry nums p = 0 ∧ entry nums q ≠ 0 ∧ r.val = (k : Int) + 1 ∧
      MinMovesTo (swapAt (vals nums) p q) k) := by
  sorry

/-- Whenever sort_array(nums) returns r with r > 0, for every p,q with 0 <= p,q < n, nums[p] = 0, and nums[q] != 0, if nums' is obtained from nums by swapping the entries at p and q, then the minimum number of legal moves needed to transform nums' into target A or target B is at least r-1. Here 'minimum number of legal moves' has the same meaning as in spec_11.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] < n; and for every i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_12 (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r) (hrpos : 0 < r.val) :
    ∀ p q, p < (vals nums).length → q < (vals nums).length →
      entry nums p = 0 → entry nums q ≠ 0 →
      ∀ k, (∃ seq, IsMoveSeqTo (swapAt (vals nums) p q) k seq) → r.val - 1 ≤ (k : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 2 ≤ (vals nums).length) (hnle : (vals nums).length ≤ 100000)
    (hrange : ∀ i, i < (vals nums).length →
      0 ≤ entry nums i ∧ entry nums i < ((vals nums).length : Int))
    (hdistinct : ∀ i j, i < j → j < (vals nums).length → entry nums i ≠ entry nums j)
    (r : Std.I64) (hr : Aegis.SortArray.sort_array nums = ok r) (hrpos : 0 < r.val), ∀ p q, p < (vals nums).length → q < (vals nums).length →
      entry nums p = 0 → entry nums q ≠ 0 →
      ∀ k, (∃ seq, IsMoveSeqTo (swapAt (vals nums) p q) k seq) → r.val - 1 ≤ (k : Int)) := by
  sorry

end AegisSpec.SortArray
