import Aegis.DecompressRlElist.Code.Funs

/-!
# Specifications of `Aegis.DecompressRlElist.decompress_rl_elist`

LeetCode problem `decompress-run-length-encoded-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.DecompressRlElist

  namespace AegisSpec.DecompressRlElist

  def inList (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def outList (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

  def intAt (l : List Int) (i : Nat) : Int := (l[i]?).getD 0

  def inAt (nums : Slice Std.I64) (i : Nat) : Int := intAt (inList nums) i

  def outAt (r : alloc.vec.Vec Std.I64) (i : Nat) : Int := intAt (outList r) i

  def m (nums : Slice Std.I64) : Nat := (inList nums).length / 2

  def freq (nums : Slice Std.I64) (i : Nat) : Nat := (inAt nums (2 * i)).toNat

  def valAt (nums : Slice Std.I64) (i : Nat) : Int := inAt nums (2 * i + 1)

  def startPos (nums : Slice Std.I64) (i : Nat) : Nat :=
    ((List.range i).map (fun k => freq nums k)).sum

  def totalLen (nums : Slice Std.I64) : Nat := startPos nums (m nums)

  def lastFreq (nums : Slice Std.I64) : Nat := (inAt nums ((inList nums).length - 2)).toNat

  def lastVal (nums : Slice Std.I64) : Int := inAt nums ((inList nums).length - 1)

  /-- Whenever the function returns a result r, let m = len(nums) / 2. For each i with 0 <= i < m, let f_i = nums[2*i], v_i = nums[2*i+1], and s_i = f_0 + f_1 + ... + f_{i-1} (with s_0 = 0). Then len(r) = f_0 + f_1 + ... + f_{m-1}, and for every i with 0 <= i < m and every j with 0 <= j < f_i, r[s_i + j] = v_i. All indices are 0-based.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
      (h_res : decompress_rl_elist nums = ok r) :
      (outList r).length = totalLen nums ∧
        ∀ (i : Nat), i < m nums → ∀ (j : Nat), j < freq nums i →
          outAt r (startPos nums i + j) = valAt nums i := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
        (h_res : decompress_rl_elist nums = ok r), (outList r).length = totalLen nums ∧
          ∀ (i : Nat), i < m nums → ∀ (j : Nat), j < freq nums i →
            outAt r (startPos nums i + j) = valAt nums i) := by
    sorry

  /-- For every nums satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or execute an out-of-bounds access.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100) :
      ∃ r : alloc.vec.Vec Std.I64, decompress_rl_elist nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100), ∃ r : alloc.vec.Vec Std.I64, decompress_rl_elist nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) >= 1.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
      (h_res : decompress_rl_elist nums = ok r) :
      1 ≤ (outList r).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
        (h_res : decompress_rl_elist nums = ok r), 1 ≤ (outList r).length) := by
    sorry

  /-- Whenever the function returns a result r, let m = len(nums) / 2. Then m <= len(r) <= 5000.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
      (h_res : decompress_rl_elist nums = ok r) :
      m nums ≤ (outList r).length ∧ (outList r).length ≤ 5000 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
        (h_res : decompress_rl_elist nums = ok r), m nums ≤ (outList r).length ∧ (outList r).length ≤ 5000) := by
    sorry

  /-- Whenever the function returns a result r, for every position p with 0 <= p < len(r), 1 <= r[p] <= 100.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
      (h_res : decompress_rl_elist nums = ok r) :
      ∀ (p : Nat), p < (outList r).length → 1 ≤ outAt r p ∧ outAt r p ≤ 100 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
        (h_res : decompress_rl_elist nums = ok r), ∀ (p : Nat), p < (outList r).length → 1 ≤ outAt r p ∧ outAt r p ≤ 100) := by
    sorry

  /-- Whenever the function returns a result r, len(r) >= nums[0], and for every j with 0 <= j < nums[0], r[j] = nums[1].
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
      (h_res : decompress_rl_elist nums = ok r) :
      inAt nums 0 ≤ ((outList r).length : Int) ∧
        ∀ (j : Nat), (j : Int) < inAt nums 0 → outAt r j = inAt nums 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
        (h_res : decompress_rl_elist nums = ok r), inAt nums 0 ≤ ((outList r).length : Int) ∧
          ∀ (j : Nat), (j : Int) < inAt nums 0 → outAt r j = inAt nums 1) := by
    sorry

  /-- Whenever the function returns a result r, let f = nums[len(nums)-2], v = nums[len(nums)-1], and s = len(r) - f. Then f <= len(r), and for every j with 0 <= j < f, r[s + j] = v.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
      (h_res : decompress_rl_elist nums = ok r) :
      lastFreq nums ≤ (outList r).length ∧
        ∀ (j : Nat), j < lastFreq nums →
          outAt r ((outList r).length - lastFreq nums + j) = lastVal nums := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
        (h_res : decompress_rl_elist nums = ok r), lastFreq nums ≤ (outList r).length ∧
          ∀ (j : Nat), j < lastFreq nums →
            outAt r ((outList r).length - lastFreq nums + j) = lastVal nums) := by
    sorry

  /-- Whenever the function returns a result r, let m = len(nums) / 2. For each i with 0 <= i < m, let f_i = nums[2*i] and s_i = nums[0] + nums[2] + ... + nums[2*(i-1)] (with s_0 = 0). Then for all p and q with 0 <= p < len(r), 0 <= q < len(r), s_i <= p < s_i + f_i, and s_i <= q < s_i + f_i, we have r[p] = r[q].
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_8 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
      (h_res : decompress_rl_elist nums = ok r) :
      ∀ (i : Nat), i < m nums → ∀ (p q : Nat),
        startPos nums i ≤ p → p < startPos nums i + freq nums i →
        startPos nums i ≤ q → q < startPos nums i + freq nums i →
        outAt r p = outAt r q := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
        (h_res : decompress_rl_elist nums = ok r), ∀ (i : Nat), i < m nums → ∀ (p q : Nat),
          startPos nums i ≤ p → p < startPos nums i + freq nums i →
          startPos nums i ≤ q → q < startPos nums i + freq nums i →
          outAt r p = outAt r q) := by
    sorry

  /-- Whenever the function returns a result r, let m = len(nums) / 2. For each i with 0 <= i < m, let f_i = nums[2*i] and s_i = nums[0] + nums[2] + ... + nums[2*(i-1)] (with s_0 = 0). For all i and j with 0 <= i < j < m, and all p and q with 0 <= p < len(r), 0 <= q < len(r), s_i <= p < s_i + f_i, and s_j <= q < s_j + f_j, we have p < q.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_9 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
      (h_res : decompress_rl_elist nums = ok r) :
      ∀ (i j : Nat), i < j → j < m nums → ∀ (p q : Nat),
        p < (outList r).length → q < (outList r).length →
        startPos nums i ≤ p → p < startPos nums i + freq nums i →
        startPos nums j ≤ q → q < startPos nums j + freq nums j →
        p < q := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
        (h_res : decompress_rl_elist nums = ok r), ∀ (i j : Nat), i < j → j < m nums → ∀ (p q : Nat),
          p < (outList r).length → q < (outList r).length →
          startPos nums i ≤ p → p < startPos nums i + freq nums i →
          startPos nums j ≤ q → q < startPos nums j + freq nums j →
          p < q) := by
    sorry

  /-- Whenever the function returns a result r, let m = len(nums) / 2. For each i with 0 <= i < m define s_i = nums[0] + nums[2] + ... + nums[2*(i-1)], with the empty sum s_0 = 0. For every position p with 0 <= p < len(r), there exist a unique index i with 0 <= i < m and a unique integer j with 0 <= j < nums[2*i] such that p = s_i + j and r[p] = nums[2*i+1].
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_10 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
      (h_res : decompress_rl_elist nums = ok r) :
      ∀ (p : Nat), p < (outList r).length →
        ∃ (i : Nat), i < m nums ∧ ∃ (j : Nat),
          j < freq nums i ∧ p = startPos nums i + j ∧ outAt r p = valAt nums i ∧
            ∀ (i' j' : Nat), i' < m nums → j' < freq nums i' →
              p = startPos nums i' + j' → outAt r p = valAt nums i' → i' = i ∧ j' = j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
        (h_res : decompress_rl_elist nums = ok r), ∀ (p : Nat), p < (outList r).length →
          ∃ (i : Nat), i < m nums ∧ ∃ (j : Nat),
            j < freq nums i ∧ p = startPos nums i + j ∧ outAt r p = valAt nums i ∧
              ∀ (i' j' : Nat), i' < m nums → j' < freq nums i' →
                p = startPos nums i' + j' → outAt r p = valAt nums i' → i' = i ∧ j' = j) := by
    sorry

  /-- Whenever the function returns a result r, let m = len(nums) / 2. For every k with 1 <= k < m, define s_k = nums[0] + nums[2] + ... + nums[2*(k-1)]. Then 1 <= s_k < len(r), and r[s_k - 1] = nums[2*(k-1)+1] and r[s_k] = nums[2*k+1].
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_11 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
      (h_res : decompress_rl_elist nums = ok r) :
      ∀ (k : Nat), 1 ≤ k → k < m nums →
        1 ≤ startPos nums k ∧ startPos nums k < (outList r).length ∧
          outAt r (startPos nums k - 1) = valAt nums (k - 1) ∧
          outAt r (startPos nums k) = valAt nums k := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
        (h_res : decompress_rl_elist nums = ok r), ∀ (k : Nat), 1 ≤ k → k < m nums →
          1 ≤ startPos nums k ∧ startPos nums k < (outList r).length ∧
            outAt r (startPos nums k - 1) = valAt nums (k - 1) ∧
            outAt r (startPos nums k) = valAt nums k) := by
    sorry

  /-- Whenever the function returns a result r, let m = len(nums) / 2. Then len(r) = m and for every i with 0 <= i < m, r[i] = nums[2*i+1].
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and for every i with 0 <= i < len(nums)/2, nums[2*i] = 1. -/
  theorem spec_12 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_even : (inList nums).length % 2 = 0)
      (h_ge : 2 ≤ (inList nums).length)
      (h_le : (inList nums).length ≤ 100)
      (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
        1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
      (h_unit : ∀ (i : Nat), i < m nums → freq nums i = 1)
      (h_res : decompress_rl_elist nums = ok r) :
      (outList r).length = m nums ∧
        ∀ (i : Nat), i < m nums → outAt r i = valAt nums i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_even : (inList nums).length % 2 = 0)
        (h_ge : 2 ≤ (inList nums).length)
        (h_le : (inList nums).length ≤ 100)
        (h_bnd : ∀ (i : Nat) (hi : i < (inList nums).length),
          1 ≤ (inList nums)[i]'hi ∧ (inList nums)[i]'hi ≤ 100)
        (h_unit : ∀ (i : Nat), i < m nums → freq nums i = 1)
        (h_res : decompress_rl_elist nums = ok r), (outList r).length = m nums ∧
          ∀ (i : Nat), i < m nums → outAt r i = valAt nums i) := by
    sorry

  end AegisSpec.DecompressRlElist
