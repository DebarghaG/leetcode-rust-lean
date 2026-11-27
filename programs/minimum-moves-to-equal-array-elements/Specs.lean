import Aegis.MinMoves.Code.Funs

/-!
# Specifications of `Aegis.MinMoves.min_moves`

LeetCode problem `minimum-moves-to-equal-array-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinMoves

  namespace AegisSpec.MinMoves

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def len (nums : Slice Std.I64) : ℕ := nums.val.length

  def listMin : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr min x

  def listMax : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr max x

  def IsMin (l : List ℤ) (m : ℤ) : Prop := m ∈ l ∧ ∀ x ∈ l, m ≤ x

  def IsMax (l : List ℤ) (M : ℤ) : Prop := M ∈ l ∧ ∀ x ∈ l, x ≤ M

  def IsConstant (l : List ℤ) : Prop := ∀ x ∈ l, ∀ y ∈ l, x = y

  def answer (nums : Slice Std.I64) : ℤ :=
    (vals nums).sum - (len nums : ℤ) * listMin (vals nums)

  def FitsI32 (k : ℤ) : Prop := -2147483648 ≤ k ∧ k ≤ 2147483647

  def legalStep (n : ℕ) (skip : Fin n) (l : List ℤ) : List ℤ :=
    (List.finRange n).map
      (fun i => if i = skip then l.getD i.val 0 else l.getD i.val 0 + 1)

  def applyMoves (n : ℕ) : List (Fin n) → List ℤ → List ℤ
    | [], l => l
    | skip :: rest, l => applyMoves n rest (legalStep n skip l)

  def ReachableIn (k : ℕ) (l l' : List ℤ) : Prop :=
    ∃ moves : List (Fin l.length), moves.length = k ∧ applyMoves l.length moves l = l'

  /-- The function returns a result r and r = sum_{i=0}^{len(nums)-1} (nums[i] - m), where m is the minimum element of nums (that is, m = nums[j] for some j with 0 <= j < len(nums), and m <= nums[i] for every i with 0 <= i < len(nums)).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and 0 <= sum_{i=0}^{len(nums)-1} (nums[i] - min(nums)) <= 2147483647, where min(nums) is the smallest element of nums. -/
  theorem spec_1 (nums : Slice Std.I64) (m : ℤ)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hmin : IsMin (vals nums) m)
      (hanswer_lo : 0 ≤ (vals nums).sum - (len nums : ℤ) * m)
      (hanswer_hi : (vals nums).sum - (len nums : ℤ) * m ≤ 2147483647) :
      ∃ r, min_moves nums = ok r ∧ r.val = (vals nums).sum - (len nums : ℤ) * m := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : ℤ)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hmin : IsMin (vals nums) m)
        (hanswer_lo : 0 ≤ (vals nums).sum - (len nums : ℤ) * m)
        (hanswer_hi : (vals nums).sum - (len nums : ℤ) * m ≤ 2147483647), ∃ r, min_moves nums = ok r ∧ r.val = (vals nums).sum - (len nums : ℤ) * m) := by
    sorry

  /-- The function returns a result r; it does not fail (no arithmetic overflow, out-of-bounds access, or panic) on any such input, and the returned value satisfies 0 <= r <= 2147483647.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and the minimum-move answer for nums fits in a signed 32-bit integer. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit : FitsI32 (answer nums)) :
      ∃ r, min_moves nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 2147483647 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit : FitsI32 (answer nums)), ∃ r, min_moves nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 2147483647) := by
    sorry

  /-- The function returns a result r and r >= max(nums) - min(nums), where max(nums) and min(nums) are the maximum and minimum elements of nums.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and the minimum-move answer for nums fits in a signed 32-bit integer. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit : FitsI32 (answer nums)) :
      ∃ r, min_moves nums = ok r ∧
        listMax (vals nums) - listMin (vals nums) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit : FitsI32 (answer nums)), ∃ r, min_moves nums = ok r ∧
          listMax (vals nums) - listMin (vals nums) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= (len(nums) - 1) * (max(nums) - min(nums)), where max(nums) and min(nums) are the maximum and minimum elements of nums.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and the minimum-move answer for nums fits in a signed 32-bit integer. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit : FitsI32 (answer nums)) :
      ∃ r, min_moves nums = ok r ∧
        r.val ≤ ((len nums : ℤ) - 1) * (listMax (vals nums) - listMin (vals nums)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit : FitsI32 (answer nums)), ∃ r, min_moves nums = ok r ∧
          r.val ≤ ((len nums : ℤ) - 1) * (listMax (vals nums) - listMin (vals nums))) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if all elements of nums are equal, i.e. for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] = nums[j].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and the minimum-move answer for nums fits in a signed 32-bit integer. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit : FitsI32 (answer nums)) :
      ∃ r, min_moves nums = ok r ∧ (r.val = 0 ↔ IsConstant (vals nums)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit : FitsI32 (answer nums)), ∃ r, min_moves nums = ok r ∧ (r.val = 0 ↔ IsConstant (vals nums))) := by
    sorry

  /-- The function returns results r and r' for nums and nums' respectively, and r = r'.
    Preconditions: Both nums and nums' satisfy the problem constraints: nonempty, length at most 100000, entries in [-1000000000,1000000000], and the corresponding minimum-move answer fits in a signed 32-bit integer. Also len(nums) = len(nums'), and nums' is a permutation of nums: there exists a bijection pi from {0,...,len(nums)-1} to itself such that nums'[i] = nums[pi(i)] for every i with 0 <= i < len(nums). -/
  theorem spec_6 (nums nums' : Slice Std.I64)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit : FitsI32 (answer nums))
      (hne' : 1 ≤ len nums') (hlen' : len nums' ≤ 100000)
      (hentries' : ∀ x ∈ vals nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit' : FitsI32 (answer nums'))
      (hperm_len : len nums = len nums')
      (hperm : ∃ pi : Fin (len nums) → Fin (len nums),
        Function.Bijective pi ∧
          ∀ i : Fin (len nums), (vals nums')[i.val]? = (vals nums)[(pi i).val]?) :
      ∃ r r', min_moves nums = ok r ∧ min_moves nums' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit : FitsI32 (answer nums))
        (hne' : 1 ≤ len nums') (hlen' : len nums' ≤ 100000)
        (hentries' : ∀ x ∈ vals nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit' : FitsI32 (answer nums'))
        (hperm_len : len nums = len nums')
        (hperm : ∃ pi : Fin (len nums) → Fin (len nums),
          Function.Bijective pi ∧
            ∀ i : Fin (len nums), (vals nums')[i.val]? = (vals nums)[(pi i).val]?), ∃ r r', min_moves nums = ok r ∧ min_moves nums' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- The function returns results r and r' for nums and nums' respectively, and r' = c * r.
    Preconditions: Both nums and nums' satisfy the problem constraints: nonempty, length at most 100000, entries in [-1000000000,1000000000], and the corresponding minimum-move answer fits in a signed 32-bit integer. Also len(nums) = len(nums'), and there is an integer c with 0 <= c such that nums'[i] = c * nums[i] for every i with 0 <= i < len(nums). -/
  theorem spec_7 (nums nums' : Slice Std.I64) (c : ℤ)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit : FitsI32 (answer nums))
      (hne' : 1 ≤ len nums') (hlen' : len nums' ≤ 100000)
      (hentries' : ∀ x ∈ vals nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit' : FitsI32 (answer nums'))
      (hscale_len : len nums = len nums')
      (hc : 0 ≤ c)
      (hscale : ∀ i : Fin (len nums),
        (vals nums')[i.val]? = ((vals nums)[i.val]?).map (fun x => c * x)) :
      ∃ r r', min_moves nums = ok r ∧ min_moves nums' = ok r' ∧ r'.val = c * r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit : FitsI32 (answer nums))
        (hne' : 1 ≤ len nums') (hlen' : len nums' ≤ 100000)
        (hentries' : ∀ x ∈ vals nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit' : FitsI32 (answer nums'))
        (hscale_len : len nums = len nums')
        (hc : 0 ≤ c)
        (hscale : ∀ i : Fin (len nums),
          (vals nums')[i.val]? = ((vals nums)[i.val]?).map (fun x => c * x)), ∃ r r', min_moves nums = ok r ∧ min_moves nums' = ok r' ∧ r'.val = c * r.val) := by
    sorry

  /-- The function returns results r for nums and r' for nums', and r' = r + (x - m).
    Preconditions: nums satisfies the problem constraints. Let n = len(nums) and m = min(nums). Suppose n < 100000, x is an integer with x >= max(nums) and -1000000000 <= x <= 1000000000, and nums' is the length-(n+1) array with nums'[i] = nums[i] for 0 <= i < n and nums'[n] = x. Suppose nums' satisfies the problem constraints, including its 32-bit answer guarantee. -/
  theorem spec_8 (nums nums' : Slice Std.I64) (x : ℤ)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ y ∈ vals nums, -1000000000 ≤ y ∧ y ≤ 1000000000)
      (hfit : FitsI32 (answer nums))
      (hlt : len nums < 100000)
      (hx_ge_max : listMax (vals nums) ≤ x)
      (hx_lo : -1000000000 ≤ x) (hx_hi : x ≤ 1000000000)
      (hnums' : vals nums' = vals nums ++ [x])
      (hne' : 1 ≤ len nums') (hlen' : len nums' ≤ 100000)
      (hentries' : ∀ y ∈ vals nums', -1000000000 ≤ y ∧ y ≤ 1000000000)
      (hfit' : FitsI32 (answer nums')) :
      ∃ r r', min_moves nums = ok r ∧ min_moves nums' = ok r' ∧
        r'.val = r.val + (x - listMin (vals nums)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (x : ℤ)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ y ∈ vals nums, -1000000000 ≤ y ∧ y ≤ 1000000000)
        (hfit : FitsI32 (answer nums))
        (hlt : len nums < 100000)
        (hx_ge_max : listMax (vals nums) ≤ x)
        (hx_lo : -1000000000 ≤ x) (hx_hi : x ≤ 1000000000)
        (hnums' : vals nums' = vals nums ++ [x])
        (hne' : 1 ≤ len nums') (hlen' : len nums' ≤ 100000)
        (hentries' : ∀ y ∈ vals nums', -1000000000 ≤ y ∧ y ≤ 1000000000)
        (hfit' : FitsI32 (answer nums')), ∃ r r', min_moves nums = ok r ∧ min_moves nums' = ok r' ∧
          r'.val = r.val + (x - listMin (vals nums))) := by
    sorry

  /-- The function returns results r for nums and r' for nums', and r' = r + d.
    Preconditions: nums satisfies the problem constraints. Choose an index j with 0 <= j < len(nums) and an integer d > 0 such that nums' is defined by nums'[i] = nums[i] for i != j and nums'[j] = nums[j] + d. Suppose nums' satisfies the problem constraints and min(nums') = min(nums), so the increase does not change the minimum value. -/
  theorem spec_9 (nums nums' : Slice Std.I64) (j : ℕ) (d : ℤ)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit : FitsI32 (answer nums))
      (hj : j < len nums)
      (hd : 0 < d)
      (hset : ∃ y, (vals nums)[j]? = some y ∧ vals nums' = (vals nums).set j (y + d))
      (hne' : 1 ≤ len nums') (hlen' : len nums' ≤ 100000)
      (hentries' : ∀ x ∈ vals nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit' : FitsI32 (answer nums'))
      (hmin' : listMin (vals nums') = listMin (vals nums)) :
      ∃ r r', min_moves nums = ok r ∧ min_moves nums' = ok r' ∧ r'.val = r.val + d := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (j : ℕ) (d : ℤ)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit : FitsI32 (answer nums))
        (hj : j < len nums)
        (hd : 0 < d)
        (hset : ∃ y, (vals nums)[j]? = some y ∧ vals nums' = (vals nums).set j (y + d))
        (hne' : 1 ≤ len nums') (hlen' : len nums' ≤ 100000)
        (hentries' : ∀ x ∈ vals nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit' : FitsI32 (answer nums'))
        (hmin' : listMin (vals nums') = listMin (vals nums)), ∃ r r', min_moves nums = ok r ∧ min_moves nums' = ok r' ∧ r'.val = r.val + d) := by
    sorry

  /-- The function returns results r for nums and r' for nums', and r' = r.
    Preconditions: nums satisfies the problem constraints, len(nums) >= 2, and m = min(nums) occurs at least twice in nums. Let nums' be obtained from nums by deleting one occurrence of m, so len(nums') = len(nums) - 1. Suppose nums' satisfies the problem constraints. -/
  theorem spec_10 (nums nums' : Slice Std.I64) (m : ℤ)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit : FitsI32 (answer nums))
      (hge_two : 2 ≤ len nums)
      (hmin : IsMin (vals nums) m)
      (hocc : 2 ≤ (vals nums).count m)
      (hdel : vals nums' = (vals nums).erase m)
      (hne' : 1 ≤ len nums') (hlen' : len nums' ≤ 100000)
      (hentries' : ∀ x ∈ vals nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit' : FitsI32 (answer nums')) :
      ∃ r r', min_moves nums = ok r ∧ min_moves nums' = ok r' ∧ r'.val = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (m : ℤ)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit : FitsI32 (answer nums))
        (hge_two : 2 ≤ len nums)
        (hmin : IsMin (vals nums) m)
        (hocc : 2 ≤ (vals nums).count m)
        (hdel : vals nums' = (vals nums).erase m)
        (hne' : 1 ≤ len nums') (hlen' : len nums' ≤ 100000)
        (hentries' : ∀ x ∈ vals nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit' : FitsI32 (answer nums')), ∃ r r', min_moves nums = ok r ∧ min_moves nums' = ok r' ∧ r'.val = r.val) := by
    sorry

  /-- The function returns a result r, and there exists a finite sequence of exactly r legal moves that transforms nums into an array all of whose elements are equal. A legal move consists of choosing n-1 distinct indices, where n = len(nums), and incrementing each chosen element by 1.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and the minimum-move answer for nums fits in a signed 32-bit integer. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit : FitsI32 (answer nums)) :
      ∃ r, min_moves nums = ok r ∧
        ∃ k : ℕ, (k : ℤ) = r.val ∧
          ∃ l' : List ℤ, ReachableIn k (vals nums) l' ∧ IsConstant l' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit : FitsI32 (answer nums)), ∃ r, min_moves nums = ok r ∧
          ∃ k : ℕ, (k : ℤ) = r.val ∧
            ∃ l' : List ℤ, ReachableIn k (vals nums) l' ∧ IsConstant l') := by
    sorry

  /-- The function returns a result r, and for every nonnegative integer k < r, there is no finite sequence of k legal moves that transforms nums into an array all of whose elements are equal, where a legal move chooses n-1 distinct indices (n = len(nums)) and increments each chosen element by 1.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and the minimum-move answer for nums fits in a signed 32-bit integer. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
      (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfit : FitsI32 (answer nums)) :
      ∃ r, min_moves nums = ok r ∧
        ∀ k : ℕ, (k : ℤ) < r.val →
          ¬ ∃ l' : List ℤ, ReachableIn k (vals nums) l' ∧ IsConstant l' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ len nums) (hlen : len nums ≤ 100000)
        (hentries : ∀ x ∈ vals nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfit : FitsI32 (answer nums)), ∃ r, min_moves nums = ok r ∧
          ∀ k : ℕ, (k : ℤ) < r.val →
            ¬ ∃ l' : List ℤ, ReachableIn k (vals nums) l' ∧ IsConstant l') := by
    sorry

  end AegisSpec.MinMoves
