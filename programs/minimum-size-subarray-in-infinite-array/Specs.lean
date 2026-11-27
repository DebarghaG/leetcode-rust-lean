import Aegis.MinSizeSubarray.Code.Funs

/-!
# Specifications of `Aegis.MinSizeSubarray.min_size_subarray`

LeetCode problem `minimum-size-subarray-in-infinite-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinSizeSubarray

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def cyc (l : List Int) (k : Nat) : Int := l.getD (k % l.length) 0

  def wsum (l : List Int) (i : Nat) : Nat → Int
    | 0 => 0
    | L + 1 => wsum l i L + cyc l (i + L)

  def total (l : List Int) : Int := l.foldr (fun x acc => x + acc) 0

  def maxVal : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl (fun acc y => max acc y) x

  def minVal : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl (fun acc y => min acc y) x

  def ceilDiv (t m : Int) : Int := (t + m - 1) / m

  def HasWin (l : List Int) (t : Int) : Prop := ∃ (L : Nat) (i : Nat), 1 ≤ L ∧ wsum l i L = t

  def WindowOf (l : List Int) (b : Int) (m : Nat) : Prop :=
    1 ≤ m ∧ m < l.length ∧ ∃ p : Nat, p < l.length ∧ wsum l p m = b

  /-- Let infinite_nums[k] = nums[k mod n] for every integer k ≥ 0. The function returns a result r and: (1) if there exist an integer L ≥ 1 and a start index i ≥ 0 such that sum_{j=0}^{L-1} infinite_nums[i+j] = target, then r is the least such L; (2) otherwise r = -1.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_1 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      ∃ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r ∧
        (HasWin (vals nums) target.val →
          1 ≤ r.val ∧
          (∃ i : Nat, wsum (vals nums) i r.val.toNat = target.val) ∧
          (∀ (L : Nat) (i : Nat), 1 ≤ L → (L : Int) < r.val →
            wsum (vals nums) i L ≠ target.val)) ∧
        (¬ HasWin (vals nums) target.val → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), ∃ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r ∧
          (HasWin (vals nums) target.val →
            1 ≤ r.val ∧
            (∃ i : Nat, wsum (vals nums) i r.val.toNat = target.val) ∧
            (∀ (L : Nat) (i : Nat), 1 ≤ L → (L : Int) < r.val →
              wsum (vals nums) i L ≠ target.val)) ∧
          (¬ HasWin (vals nums) target.val → r.val = -1)) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} nums[i], let a = target div S, and let b = target mod S, so target = a*S + b with 0 ≤ b < S. For p with 0 ≤ p < n and L ≥ 0 define C(p,L) = sum_{j=0}^{L-1} nums[(p+j) mod n], with C(p,0) = 0. Let r be the result. If b = 0, then r = a*n. If b > 0, let m be the least integer in [1, n-1] such that there exists p with 0 ≤ p < n and C(p,m) = b. If such an m exists, then r = a*n + m; otherwise r = -1.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_2 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      let S : Int := total (vals nums)
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        (target.val % S = 0 →
            r.val = (target.val / S) * (nums.val.length : Int)) ∧
        (0 < target.val % S →
          ((∃ m : Nat, WindowOf (vals nums) (target.val % S) m) →
              ∃ m : Nat,
                WindowOf (vals nums) (target.val % S) m ∧
                (∀ m' : Nat, WindowOf (vals nums) (target.val % S) m' → m ≤ m') ∧
                r.val = (target.val / S) * (nums.val.length : Int) + (m : Int)) ∧
          (¬ (∃ m : Nat, WindowOf (vals nums) (target.val % S) m) → r.val = -1)) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), let S : Int := total (vals nums)
        ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          (target.val % S = 0 →
              r.val = (target.val / S) * (nums.val.length : Int)) ∧
          (0 < target.val % S →
            ((∃ m : Nat, WindowOf (vals nums) (target.val % S) m) →
                ∃ m : Nat,
                  WindowOf (vals nums) (target.val % S) m ∧
                  (∀ m' : Nat, WindowOf (vals nums) (target.val % S) m' → m ≤ m') ∧
                  r.val = (target.val / S) * (nums.val.length : Int) + (m : Int)) ∧
            (¬ (∃ m : Nat, WindowOf (vals nums) (target.val % S) m) → r.val = -1))) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or return an error) for every input satisfying the preconditions.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_3 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      ∃ r : Std.I64, Aegis.MinSizeSubarray.min_size_subarray nums target = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), ∃ r : Std.I64, Aegis.MinSizeSubarray.min_size_subarray nums target = ok r) := by
    sorry

  /-- Let r be the result. If r ≥ 0, then 1 ≤ r ≤ target.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_4 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        0 ≤ r.val → 1 ≤ r.val ∧ r.val ≤ target.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          0 ≤ r.val → 1 ≤ r.val ∧ r.val ≤ target.val) := by
    sorry

  /-- Let M = max_{0 ≤ i < n} nums[i] and let r be the result. If r ≥ 0, then ceil(target / M) ≤ r ≤ target, where ceil(target / M) is the least integer c with c*M ≥ target.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_5 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        0 ≤ r.val →
          ceilDiv target.val (maxVal (vals nums)) ≤ r.val ∧ r.val ≤ target.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          0 ≤ r.val →
            ceilDiv target.val (maxVal (vals nums)) ≤ r.val ∧ r.val ≤ target.val) := by
    sorry

  /-- Let r be the result. Then r = 1 if and only if there exists an index i with 0 ≤ i < n and nums[i] = target.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_6 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        (r.val = 1 ↔ ∃ (i : Nat) (hi : i < nums.val.length),
          (nums.val[i]'hi).val = target.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          (r.val = 1 ↔ ∃ (i : Nat) (hi : i < nums.val.length),
            (nums.val[i]'hi).val = target.val)) := by
    sorry

  /-- Let m = min_{0 ≤ i < n} nums[i] and let r be the result. If target < m, then r = -1.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_7 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        target.val < minVal (vals nums) → r.val = -1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          target.val < minVal (vals nums) → r.val = -1) := by
    sorry

  /-- Let r be the result. If r ≥ 1, then there exists a start index i ≥ 0 such that sum_{j=0}^{r-1} infinite_nums[i+j] = target, where infinite_nums[k] = nums[k mod n].
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_8 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        1 ≤ r.val → ∃ i : Nat, wsum (vals nums) i r.val.toNat = target.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          1 ≤ r.val → ∃ i : Nat, wsum (vals nums) i r.val.toNat = target.val) := by
    sorry

  /-- Let r be the result. If r ≥ 1, then for every integer L with 1 ≤ L < r and every start index i ≥ 0, sum_{j=0}^{L-1} infinite_nums[i+j] ≠ target, where infinite_nums[k] = nums[k mod n].
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_9 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        1 ≤ r.val →
          ∀ (L : Nat) (i : Nat), 1 ≤ L → (L : Int) < r.val →
            wsum (vals nums) i L ≠ target.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          1 ≤ r.val →
            ∀ (L : Nat) (i : Nat), 1 ≤ L → (L : Int) < r.val →
              wsum (vals nums) i L ≠ target.val) := by
    sorry

  /-- Let r be the result. Then r = -1 if and only if for every integer L ≥ 1 and every start index i ≥ 0, sum_{j=0}^{L-1} infinite_nums[i+j] ≠ target, where infinite_nums[k] = nums[k mod n].
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_10 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        (r.val = -1 ↔ ¬ HasWin (vals nums) target.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          (r.val = -1 ↔ ¬ HasWin (vals nums) target.val)) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} nums[i], let b = target mod S, and let r be the result. If r ≥ 0, then: (a) if b = 0, then r mod n = 0; (b) if b > 0, then 1 ≤ r mod n < n.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_11 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      let S : Int := total (vals nums)
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        0 ≤ r.val →
        ((target.val % S = 0 → r.val % (nums.val.length : Int) = 0) ∧
          (0 < target.val % S →
            1 ≤ r.val % (nums.val.length : Int) ∧
              r.val % (nums.val.length : Int) < (nums.val.length : Int))) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), let S : Int := total (vals nums)
        ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          0 ≤ r.val →
          ((target.val % S = 0 → r.val % (nums.val.length : Int) = 0) ∧
            (0 < target.val % S →
              1 ≤ r.val % (nums.val.length : Int) ∧
                r.val % (nums.val.length : Int) < (nums.val.length : Int)))) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} nums[i] and let r be the result. If target < S and r ≠ -1, then 1 ≤ r < n.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_12 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      let S : Int := total (vals nums)
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        target.val < S → r.val ≠ -1 →
          1 ≤ r.val ∧ r.val < (nums.val.length : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), let S : Int := total (vals nums)
        ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          target.val < S → r.val ≠ -1 →
            1 ≤ r.val ∧ r.val < (nums.val.length : Int)) := by
    sorry

  /-- Let k be any integer with 0 ≤ k < n, and let nums2 be the slice of length n defined by nums2[i] = nums[(i+k) mod n] for 0 ≤ i < n. Then the result returned for nums2 and target is the same as the result returned for nums and target.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_13 (nums nums2 : Slice Std.I64) (target : Std.I64) (k : Nat)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9)
      (hk : k < nums.val.length)
      (hlen2 : nums2.val.length = nums.val.length)
      (hrot : ∀ (i : Nat) (hi : i < nums2.val.length),
        (nums2.val[i]'hi).val = cyc (vals nums) (i + k)) :
      ∀ r r2 : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        Aegis.MinSizeSubarray.min_size_subarray nums2 target = ok r2 → r = r2 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (target : Std.I64) (k : Nat)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9)
        (hk : k < nums.val.length)
        (hlen2 : nums2.val.length = nums.val.length)
        (hrot : ∀ (i : Nat) (hi : i < nums2.val.length),
          (nums2.val[i]'hi).val = cyc (vals nums) (i + k)), ∀ r r2 : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          Aegis.MinSizeSubarray.min_size_subarray nums2 target = ok r2 → r = r2) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} nums[i], let a = target div S, let b = target mod S, and let r be the result. If b > 0 and r ≠ -1, then a*n + 1 ≤ r ≤ (a+1)*n - 1.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_14 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      let S : Int := total (vals nums)
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        0 < target.val % S → r.val ≠ -1 →
          (target.val / S) * (nums.val.length : Int) + 1 ≤ r.val ∧
            r.val ≤ ((target.val / S) + 1) * (nums.val.length : Int) - 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), let S : Int := total (vals nums)
        ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          0 < target.val % S → r.val ≠ -1 →
            (target.val / S) * (nums.val.length : Int) + 1 ≤ r.val ∧
              r.val ≤ ((target.val / S) + 1) * (nums.val.length : Int) - 1) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} nums[i] and let r be the result. If target ≤ S and r ≠ -1, then 1 ≤ r ≤ n.
    Preconditions: Let n = len(nums). Assume 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ 100000, and 1 ≤ target ≤ 10^9. -/
  theorem spec_15 (nums : Slice Std.I64) (target : Std.I64)
      (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9) :
      let S : Int := total (vals nums)
      ∀ r : Std.I64,
        Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
        target.val ≤ S → r.val ≠ -1 →
          1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hne : 1 ≤ nums.val.length) (hle : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (htlo : 1 ≤ target.val) (hthi : target.val ≤ 10 ^ 9), let S : Int := total (vals nums)
        ∀ r : Std.I64,
          Aegis.MinSizeSubarray.min_size_subarray nums target = ok r →
          target.val ≤ S → r.val ≠ -1 →
            1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
    sorry

  end AegisSpec.MinSizeSubarray
