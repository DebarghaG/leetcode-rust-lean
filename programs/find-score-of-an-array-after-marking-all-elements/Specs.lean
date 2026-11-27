import Aegis.FindScore.Code.Funs

/-!
# Specifications of `Aegis.FindScore.find_score`

LeetCode problem `find-score-of-an-array-after-marking-all-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindScore

  namespace AegisSpec.FindScore

  def values (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def listAt (a : List Int) (i : Nat) : Int := a.getD i 0

  def entry (nums : Slice Std.I64) (i : Nat) : Int := listAt (values nums) i

  def IsValid (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
      ∀ i, i < nums.val.length → 1 ≤ entry nums i ∧ entry nums i ≤ 1000000

  def markedAt (marked : List Bool) (i : Nat) : Bool := marked.getD i false

  def markAround (n : Nat) (marked : List Bool) (i : Nat) : List Bool :=
    let m1 := marked.set i true
    let m2 := if i = 0 then m1 else m1.set (i - 1) true
    if i + 1 < n then m2.set (i + 1) true else m2

  def pickMin (a : List Int) (marked : List Bool) : Option Nat :=
    (List.range a.length).foldl
      (fun best i =>
        if markedAt marked i then best
        else
          match best with
          | none => some i
          | some j => if listAt a i < listAt a j then some i else best)
      none

  def chosenAux (a : List Int) : Nat → List Bool → List Nat
    | 0, _ => []
    | fuel + 1, marked =>
      match pickMin a marked with
      | none => []
      | some i => i :: chosenAux a fuel (markAround a.length marked i)

  def chosen (a : List Int) : List Nat :=
    chosenAux a a.length (List.replicate a.length false)

  def scoreOf (a : List Int) : Int := ((chosen a).map (fun i => listAt a i)).sum

  def listMin (a : List Int) (d : Int) : Int :=
    match a with
    | [] => d
    | x :: xs => xs.foldl (fun acc y => min acc y) x

  def sumEven (a : List Int) : Int :=
    ((List.range ((a.length + 1) / 2)).map (fun k => listAt a (2 * k))).sum

  /-- Let n = len(nums). Consider the deterministic marking process on indices 0,...,n-1. Initially no index is marked and score = 0. While an unmarked index remains, let i be the unmarked index satisfying both: nums[i] is minimal among all unmarked indices, and among all unmarked indices with that minimal value, i is the smallest index. Add nums[i] to the score, then mark i and every index j with 0 <= j < n and |j-i| <= 1. Let T be the number of iterations before all indices are marked, and let i_0,...,i_{T-1} be the chosen indices in order. The function returns a result r and r = sum_{k=0}^{T-1} nums[i_k], with the sum taken as a mathematical integer; this value fits in i64.
    Preconditions: nums is a valid input: 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_1 (nums : Slice Std.I64) (h : IsValid nums) :
      ∃ r, find_score nums = Result.ok r ∧ r.val = scoreOf (values nums) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValid nums), ∃ r, find_score nums = Result.ok r ∧ r.val = scoreOf (values nums)) := by
    sorry

  /-- For every valid nums, the function returns a result r and does not fail (no panic and no 64-bit overflow). In particular, the exact score is at most 100000 * 1000000 = 100000000000, which is below 2^63-1, so the final sum and all intermediate cumulative scores fit in i64.
    Preconditions: nums is a valid input: 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_2 (nums : Slice Std.I64) (h : IsValid nums) :
      ∃ r, find_score nums = Result.ok r ∧ r.val = scoreOf (values nums) ∧
        scoreOf (values nums) ≤ 100000000000 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValid nums), ∃ r, find_score nums = Result.ok r ∧ r.val = scoreOf (values nums) ∧
          scoreOf (values nums) ≤ 100000000000) := by
    sorry

  /-- Whenever the function returns a result r, min_{0 <= i < len(nums)} nums[i] <= r <= sum_{i=0}^{len(nums)-1} nums[i], where the minimum and sum are mathematical integers.
    Preconditions: nums is a valid input: 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_3 (nums : Slice Std.I64) (h : IsValid nums) :
      ∀ r, find_score nums = Result.ok r →
        listMin (values nums) 0 ≤ r.val ∧ r.val ≤ (values nums).sum := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValid nums), ∀ r, find_score nums = Result.ok r →
          listMin (values nums) 0 ≤ r.val ∧ r.val ≤ (values nums).sum) := by
    sorry

  /-- Whenever the function returns a result r, r = nums[0].
    Preconditions: nums is a valid input and len(nums) = 1. -/
  theorem spec_4 (nums : Slice Std.I64) (a : Int) (h : IsValid nums)
      (hlen : values nums = [a]) :
      ∀ r, find_score nums = Result.ok r → r.val = a := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (a : Int) (h : IsValid nums)
        (hlen : values nums = [a]), ∀ r, find_score nums = Result.ok r → r.val = a) := by
    sorry

  /-- Whenever the function returns a result r, r = min(nums[0], nums[1]), the smaller of the two values; if they are equal, their common value.
    Preconditions: nums is a valid input and len(nums) = 2. -/
  theorem spec_5 (nums : Slice Std.I64) (a b : Int) (h : IsValid nums)
      (hlen : values nums = [a, b]) :
      ∀ r, find_score nums = Result.ok r → r.val = min a b := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (a b : Int) (h : IsValid nums)
        (hlen : values nums = [a, b]), ∀ r, find_score nums = Result.ok r → r.val = min a b) := by
    sorry

  /-- Whenever the function returns a result r, r = c * ceil(len(nums) / 2), where ceil is integer ceiling.
    Preconditions: nums is a valid input and there is a constant c with 1 <= c <= 1000000 such that nums[i] = c for every i with 0 <= i < len(nums). -/
  theorem spec_6 (nums : Slice Std.I64) (c : Int) (h : IsValid nums)
      (hc1 : 1 ≤ c) (hc2 : c ≤ 1000000)
      (hconst : ∀ i, i < nums.val.length → entry nums i = c) :
      ∀ r, find_score nums = Result.ok r →
        r.val = c * ↑((nums.val.length + 1) / 2) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (c : Int) (h : IsValid nums)
        (hc1 : 1 ≤ c) (hc2 : c ≤ 1000000)
        (hconst : ∀ i, i < nums.val.length → entry nums i = c), ∀ r, find_score nums = Result.ok r →
          r.val = c * ↑((nums.val.length + 1) / 2)) := by
    sorry

  /-- Whenever the function returns a result r, r = sum over all integers k with 0 <= k and 2k < len(nums) of nums[2k], i.e. the sum of the values at even indices 0,2,4,... .
    Preconditions: nums is a valid input and, for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
  theorem spec_7 (nums : Slice Std.I64) (h : IsValid nums)
      (hsorted : ∀ i, i + 1 < nums.val.length → entry nums i ≤ entry nums (i + 1)) :
      ∀ r, find_score nums = Result.ok r → r.val = sumEven (values nums) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValid nums)
        (hsorted : ∀ i, i + 1 < nums.val.length → entry nums i ≤ entry nums (i + 1)), ∀ r, find_score nums = Result.ok r → r.val = sumEven (values nums)) := by
    sorry

  /-- Whenever find_score(nums) returns a result r, let S be the set of indices chosen by the marking process whose values sum to r. Then S is independent on the path: for all distinct i,j in S, |i-j| >= 2. Equivalently, no two chosen indices are adjacent.
    Preconditions: nums is a valid input: 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_8 (nums : Slice Std.I64) (h : IsValid nums) :
      ∀ r, find_score nums = Result.ok r →
        ∀ i j, i ∈ chosen (values nums) → j ∈ chosen (values nums) → i ≠ j →
          2 ≤ ((i : Int) - (j : Int)).natAbs := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValid nums), ∀ r, find_score nums = Result.ok r →
          ∀ i j, i ∈ chosen (values nums) → j ∈ chosen (values nums) → i ≠ j →
            2 ≤ ((i : Int) - (j : Int)).natAbs) := by
    sorry

  /-- Whenever find_score(nums) returns a result r, let S be the set of indices chosen by the marking process whose values sum to r. Then S dominates every index: for every t with 0 <= t < len(nums), there exists s in S with |t-s| <= 1.
    Preconditions: nums is a valid input: 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_9 (nums : Slice Std.I64) (h : IsValid nums) :
      ∀ r, find_score nums = Result.ok r →
        ∀ t, t < nums.val.length →
          ∃ s, s ∈ chosen (values nums) ∧ ((t : Int) - (s : Int)).natAbs ≤ 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValid nums), ∀ r, find_score nums = Result.ok r →
          ∀ t, t < nums.val.length →
            ∃ s, s ∈ chosen (values nums) ∧ ((t : Int) - (s : Int)).natAbs ≤ 1) := by
    sorry

  /-- Let n = len(nums). Let i be the smallest index attaining m = min_{0 <= j < n} nums[j]. Let L be the contiguous sequence nums[0],...,nums[i-2] (empty if i < 2), and let R be nums[i+2],...,nums[n-1] (empty if i+2 >= n). Let score(L) and score(R) be the scores produced by the same marking algorithm on these sequences, with score(empty) = 0. Whenever find_score(nums) returns r, r = nums[i] + score(L) + score(R).
    Preconditions: nums is a valid input: 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_10 (nums : Slice Std.I64) (i : Nat) (m : Int) (h : IsValid nums)
      (hi : i < nums.val.length) (hm : entry nums i = m)
      (hmin : ∀ j, j < nums.val.length → m ≤ entry nums j)
      (hfirst : ∀ j, j < i → m < entry nums j) :
      ∀ r, find_score nums = Result.ok r →
        r.val = entry nums i + scoreOf ((values nums).take (i - 1)) +
          scoreOf ((values nums).drop (i + 2)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (i : Nat) (m : Int) (h : IsValid nums)
        (hi : i < nums.val.length) (hm : entry nums i = m)
        (hmin : ∀ j, j < nums.val.length → m ≤ entry nums j)
        (hfirst : ∀ j, j < i → m < entry nums j), ∀ r, find_score nums = Result.ok r →
          r.val = entry nums i + scoreOf ((values nums).take (i - 1)) +
            scoreOf ((values nums).drop (i + 2))) := by
    sorry

  /-- Let S be the set of indices chosen by the marking process for nums. Whenever find_score(nums) returns r and find_score(nums') returns r', r' = r + c * |S|, where |S| is the number of chosen indices for nums.
    Preconditions: nums is a valid input, and c is an integer such that for every i with 0 <= i < len(nums), 1 <= nums[i] + c <= 1000000. Let nums' be defined by nums'[i] = nums[i] + c for all i. -/
  theorem spec_11 (nums nums' : Slice Std.I64) (c : Int) (h : IsValid nums)
      (hlens : nums'.val.length = nums.val.length)
      (hshift : ∀ i, i < nums.val.length → entry nums' i = entry nums i + c) :
      ∀ r r', find_score nums = Result.ok r → find_score nums' = Result.ok r' →
        r'.val = r.val + c * ↑((chosen (values nums)).length) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (c : Int) (h : IsValid nums)
        (hlens : nums'.val.length = nums.val.length)
        (hshift : ∀ i, i < nums.val.length → entry nums' i = entry nums i + c), ∀ r r', find_score nums = Result.ok r → find_score nums' = Result.ok r' →
          r'.val = r.val + c * ↑((chosen (values nums)).length)) := by
    sorry

  /-- Whenever find_score(nums) returns a result r, let S be the set of indices chosen by the marking process whose values sum to r, and let n = len(nums). Then ceil(n/3) <= |S| <= ceil(n/2). Equivalently, (n+2) div 3 <= |S| <= (n+1) div 2 for integer division.
    Preconditions: nums is a valid input: 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_12 (nums : Slice Std.I64) (h : IsValid nums) :
      ∀ r, find_score nums = Result.ok r →
        (nums.val.length + 2) / 3 ≤ (chosen (values nums)).length ∧
          (chosen (values nums)).length ≤ (nums.val.length + 1) / 2 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValid nums), ∀ r, find_score nums = Result.ok r →
          (nums.val.length + 2) / 3 ≤ (chosen (values nums)).length ∧
            (chosen (values nums)).length ≤ (nums.val.length + 1) / 2) := by
    sorry

  /-- Let m = min_{0 <= i < len(nums)} nums[i], and let i0 be the smallest index with nums[i0] = m. In the marking process, the first chosen index is i0, and the first value added to the score is m. Consequently, whenever find_score(nums) returns r, the selected-index sequence whose values sum to r begins with i0 and has first contribution m.
    Preconditions: nums is a valid input: 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_13 (nums : Slice Std.I64) (i0 : Nat) (m : Int) (h : IsValid nums)
      (hi0 : i0 < nums.val.length) (hm : entry nums i0 = m)
      (hmin : ∀ j, j < nums.val.length → m ≤ entry nums j)
      (hfirst : ∀ j, j < i0 → m < entry nums j) :
      ∀ r, find_score nums = Result.ok r →
        (∃ rest : List Nat, chosen (values nums) = i0 :: rest) ∧
          entry nums i0 = m := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (i0 : Nat) (m : Int) (h : IsValid nums)
        (hi0 : i0 < nums.val.length) (hm : entry nums i0 = m)
        (hmin : ∀ j, j < nums.val.length → m ≤ entry nums j)
        (hfirst : ∀ j, j < i0 → m < entry nums j), ∀ r, find_score nums = Result.ok r →
          (∃ rest : List Nat, chosen (values nums) = i0 :: rest) ∧
            entry nums i0 = m) := by
    sorry

  /-- Let i satisfy 0 <= i < len(nums). Suppose i is a strict local minimum, meaning (i = 0 or nums[i] < nums[i-1]) and (i = len(nums)-1 or nums[i] < nums[i+1]). Then i belongs to the set S of indices chosen by the marking process for nums. In particular, whenever find_score(nums) returns r, nums[i] is one of the summands in the sum over S that equals r.
    Preconditions: nums is a valid input: 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_14 (nums : Slice Std.I64) (i : Nat) (h : IsValid nums)
      (hi : i < nums.val.length)
      (hleft : i = 0 ∨ entry nums i < entry nums (i - 1))
      (hright : i = nums.val.length - 1 ∨ entry nums i < entry nums (i + 1)) :
      ∀ r, find_score nums = Result.ok r →
        i ∈ chosen (values nums) ∧
          entry nums i ∈ (chosen (values nums)).map (fun j => listAt (values nums) j) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (i : Nat) (h : IsValid nums)
        (hi : i < nums.val.length)
        (hleft : i = 0 ∨ entry nums i < entry nums (i - 1))
        (hright : i = nums.val.length - 1 ∨ entry nums i < entry nums (i + 1)), ∀ r, find_score nums = Result.ok r →
          i ∈ chosen (values nums) ∧
            entry nums i ∈ (chosen (values nums)).map (fun j => listAt (values nums) j)) := by
    sorry

  end AegisSpec.FindScore
