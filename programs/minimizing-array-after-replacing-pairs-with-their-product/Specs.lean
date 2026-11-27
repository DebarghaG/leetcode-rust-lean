import Aegis.MinArrayLength.Code.Funs

/-!
# Specifications of `Aegis.MinArrayLength.min_array_length`

LeetCode problem `minimizing-array-after-replacing-pairs-with-their-product`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinArrayLength (min_array_length)

namespace AegisSpec.MinArrayLength

def toList (nums : Slice Std.I64) : List Int := nums.val.map (fun v => v.val)

def prodRange (a : List Int) (l r : Nat) : Int := ((a.drop l).take (r + 1 - l)).prod

def ReducibleSeg (k : Int) (s : List Int) : Prop := s.length = 1 ∨ s.prod ≤ k

def Parts (k : Int) (m : Nat) (a : List Int) : Prop :=
  ∃ parts : List (List Int),
    parts.length = m ∧ parts.flatten = a ∧ ∀ s ∈ parts, s ≠ [] ∧ ReducibleSeg k s

def PartsProdLE (k : Int) (m : Nat) (a : List Int) : Prop :=
  ∃ parts : List (List Int),
    parts.length = m ∧ parts.flatten = a ∧ ∀ s ∈ parts, s ≠ [] ∧ s.prod ≤ k

def LeastParts (k : Int) (a : List Int) (m : Nat) : Prop :=
  Parts k m a ∧ ∀ m', Parts k m' a → m ≤ m'

def LeastPartsProdLE (k : Int) (a : List Int) (m : Nat) : Prop :=
  PartsProdLE k m a ∧ ∀ m', PartsProdLE k m' a → m ≤ m'

def blocksWhereAux (p : Int → Bool) (cur : List Int) (done : List (List Int)) :
    List Int → List (List Int)
  | [] => if cur.isEmpty then done.reverse else (cur.reverse :: done).reverse
  | x :: xs =>
    if p x then blocksWhereAux p (x :: cur) done xs
    else blocksWhereAux p [] (if cur.isEmpty then done else cur.reverse :: done) xs

def blocksWhere (p : Int → Bool) (a : List Int) : List (List Int) :=
  blocksWhereAux p [] [] a

def countAbove (k : Int) (a : List Int) : Nat := (a.filter (fun x => decide (k < x))).length

def countNe (c : Int) (a : List Int) : Nat := (a.filter (fun x => decide (x ≠ c))).length

def oneBlockCount (a : List Int) : Nat := (blocksWhere (fun x => decide (x = 1)) a).length

def GsLE (k : Int) : List (List Int) → List Nat → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | b :: bs, g :: gs => LeastPartsProdLE k b g ∧ GsLE k bs gs

/-- Let n = len(nums). For 0 <= l <= r < n, call the interval [l,r] reducible if either l = r, or the mathematical product nums[l] * nums[l+1] * ... * nums[r] is at most k. Let M be the least m such that the index range [0,n-1] can be partitioned into m consecutive nonempty intervals [l_0,r_0], ..., [l_{m-1},r_{m-1}] with l_0 = 0, r_{m-1} = n-1, l_{j+1} = r_j+1, and every interval reducible. Then the function returns a result r and r = M.
  Preconditions: n = len(nums) >= 1 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; and 0 <= k. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val) :
    ∃ (r : Std.I64) (M : Nat),
      min_array_length nums k = ok r ∧ LeastParts k.val (toList nums) M ∧ r.val = (M : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val), ∃ (r : Std.I64) (M : Nat),
      min_array_length nums k = ok r ∧ LeastParts k.val (toList nums) M ∧ r.val = (M : Int)) := by
  sorry

/-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: n = len(nums) >= 1 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; and 0 <= k. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val) :
    ∃ r : Std.I64, min_array_length nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val), ∃ r : Std.I64, min_array_length nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= n = len(nums).
  Preconditions: n = len(nums) >= 1 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; and 0 <= k. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val) :
    ∀ r : Std.I64, min_array_length nums k = ok r → r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val), ∀ r : Std.I64, min_array_length nums k = ok r → r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: n = len(nums) >= 1 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; and 0 <= k. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val) :
    ∀ r : Std.I64, min_array_length nums k = ok r → 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val), ∀ r : Std.I64, min_array_length nums k = ok r → 1 ≤ r.val) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: n = len(nums) >= 1 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; 0 <= k; and there exists i with 0 <= i < n and nums[i] = 0. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val)
    (hzero : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = 0) :
    ∃ r : Std.I64, min_array_length nums k = ok r ∧ r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val)
    (hzero : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = 0), ∃ r : Std.I64, min_array_length nums k = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result r and r = n = len(nums).
  Preconditions: n = len(nums) >= 1 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; k = 0; and for every i with 0 <= i < n, nums[i] > 0. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk0 : k.val = 0)
    (hpos : ∀ (i : Nat) (hi : i < nums.val.length), 0 < (nums.val[i]'hi).val) :
    ∃ r : Std.I64, min_array_length nums k = ok r ∧ r.val = (nums.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk0 : k.val = 0)
    (hpos : ∀ (i : Nat) (hi : i < nums.val.length), 0 < (nums.val[i]'hi).val), ∃ r : Std.I64, min_array_length nums k = ok r ∧ r.val = (nums.val.length : Int)) := by
  sorry

/-- The function returns a result r and r = 1 if nums[0] * nums[1] <= k, and r = 2 otherwise.
  Preconditions: n = len(nums) = 2; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; and 0 <= k. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : nums.val.length = 2)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val) :
    ∃ r : Std.I64, min_array_length nums k = ok r ∧
      ((prodRange (toList nums) 0 1 ≤ k.val → r.val = 1) ∧
       (k.val < prodRange (toList nums) 0 1 → r.val = 2)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : nums.val.length = 2)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val), ∃ r : Std.I64, min_array_length nums k = ok r ∧
      ((prodRange (toList nums) 0 1 ≤ k.val → r.val = 1) ∧
       (k.val < prodRange (toList nums) 0 1 → r.val = 2))) := by
  sorry

/-- Whenever the function returns a result r, r >= 2.
  Preconditions: n = len(nums) >= 2 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; 0 <= k; for every i with 0 <= i < n, nums[i] > 0; and the mathematical product nums[0] * nums[1] * ... * nums[n-1] > k. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 2 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val)
    (hpos : ∀ (i : Nat) (hi : i < nums.val.length), 0 < (nums.val[i]'hi).val)
    (hprod : k.val < (toList nums).prod) :
    ∀ r : Std.I64, min_array_length nums k = ok r → 2 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 2 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val)
    (hpos : ∀ (i : Nat) (hi : i < nums.val.length), 0 < (nums.val[i]'hi).val)
    (hprod : k.val < (toList nums).prod), ∀ r : Std.I64, min_array_length nums k = ok r → 2 ≤ r.val) := by
  sorry

/-- The function returns a result r and r = n = len(nums) if and only if for every i with 0 <= i < n-1, the mathematical product nums[i] * nums[i+1] > k.
  Preconditions: n = len(nums) >= 1 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; and 0 <= k. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val) :
    ∃ r : Std.I64, min_array_length nums k = ok r ∧
      (r.val = (nums.val.length : Int) ↔
        ∀ (i : Nat) (hi : i + 1 < nums.val.length),
          k.val < prodRange (toList nums) i (i + 1)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val), ∃ r : Std.I64, min_array_length nums k = ok r ∧
      (r.val = (nums.val.length : Int) ↔
        ∀ (i : Nat) (hi : i + 1 < nums.val.length),
          k.val < prodRange (toList nums) i (i + 1))) := by
  sorry

/-- Let c be the number of indices i with 0 <= i < n and nums[i] > k. Whenever the function returns a result r, r >= c.
  Preconditions: n = len(nums) >= 1 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; 0 <= k; and for every i with 0 <= i < n, nums[i] > 0. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val)
    (hpos : ∀ (i : Nat) (hi : i < nums.val.length), 0 < (nums.val[i]'hi).val) :
    ∀ r : Std.I64, min_array_length nums k = ok r →
      (countAbove k.val (toList nums) : Int) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val)
    (hpos : ∀ (i : Nat) (hi : i < nums.val.length), 0 < (nums.val[i]'hi).val), ∀ r : Std.I64, min_array_length nums k = ok r →
      (countAbove k.val (toList nums) : Int) ≤ r.val) := by
  sorry

/-- Let c be the number of indices i with 0 <= i < n and nums[i] != 1, and let b be the number of maximal contiguous intervals [l,r] with 0 <= l <= r < n such that nums[i] = 1 for every i with l <= i <= r. Then the function returns a result r and r = c + b.
  Preconditions: n = len(nums) >= 1 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; k = 1; and for every i with 0 <= i < n, nums[i] > 0. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : k.val = 1)
    (hpos : ∀ (i : Nat) (hi : i < nums.val.length), 0 < (nums.val[i]'hi).val) :
    ∃ r : Std.I64, min_array_length nums k = ok r ∧
      r.val = ((countNe 1 (toList nums) + oneBlockCount (toList nums) : Nat) : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : k.val = 1)
    (hpos : ∀ (i : Nat) (hi : i < nums.val.length), 0 < (nums.val[i]'hi).val), ∃ r : Std.I64, min_array_length nums k = ok r ∧
      r.val = ((countNe 1 (toList nums) + oneBlockCount (toList nums) : Nat) : Int)) := by
  sorry

/-- The function returns a result r and r is the least m such that [0,n-1] can be partitioned into m consecutive nonempty intervals each having mathematical product at most k.
  Preconditions: n = len(nums) >= 1 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; 0 <= k; and for every i with 0 <= i < n, nums[i] <= k. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val)
    (hsmall : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val ≤ k.val) :
    ∃ (r : Std.I64) (M : Nat),
      min_array_length nums k = ok r ∧ LeastPartsProdLE k.val (toList nums) M ∧
        r.val = (M : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val)
    (hsmall : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val ≤ k.val), ∃ (r : Std.I64) (M : Nat),
      min_array_length nums k = ok r ∧ LeastPartsProdLE k.val (toList nums) M ∧
        r.val = (M : Int)) := by
  sorry

/-- Let B be the set of indices i with nums[i] > k. The complement of B in the index range [0,n-1] splits into maximal nonempty consecutive intervals I_1,...,I_t. For each such interval I = [a,b], let g(I) be the least number of consecutive nonempty intervals into which [a,b] can be partitioned such that the mathematical product of the nums entries in each part is at most k. Then the function returns a result r and r = |B| + sum_{s=1}^t g(I_s), with the sum taken as 0 if B is all of [0,n-1].
  Preconditions: n = len(nums) >= 1 and n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; 0 <= k; and for every i with 0 <= i < n, nums[i] > 0. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val)
    (hpos : ∀ (i : Nat) (hi : i < nums.val.length), 0 < (nums.val[i]'hi).val) :
    ∃ (r : Std.I64) (gs : List Nat),
      min_array_length nums k = ok r ∧
        GsLE k.val (blocksWhere (fun x => decide (x ≤ k.val)) (toList nums)) gs ∧
        r.val = ((countAbove k.val (toList nums) + gs.sum : Nat) : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : 0 ≤ k.val)
    (hpos : ∀ (i : Nat) (hi : i < nums.val.length), 0 < (nums.val[i]'hi).val), ∃ (r : Std.I64) (gs : List Nat),
      min_array_length nums k = ok r ∧
        GsLE k.val (blocksWhere (fun x => decide (x ≤ k.val)) (toList nums)) gs ∧
        r.val = ((countAbove k.val (toList nums) + gs.sum : Nat) : Int)) := by
  sorry

end AegisSpec.MinArrayLength
