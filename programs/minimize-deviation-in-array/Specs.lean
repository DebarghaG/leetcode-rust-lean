import Aegis.MinimumDeviation.Code.Funs

/-!
# Specifications of `Aegis.MinimumDeviation.minimum_deviation`

LeetCode problem `minimize-deviation-in-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumDeviation

namespace AegisSpec.MinimumDeviation

def v2 (x : ℕ) : ℕ := Nat.findGreatest (fun k => 2 ^ k ∣ x) x

def oddpartNat (x : ℕ) : ℕ := x / 2 ^ v2 x

def oddpart (x : ℤ) : ℤ := (oddpartNat x.toNat : ℤ)

def Reach (x : ℤ) (y : ℕ) : Prop :=
  ∃ (m : ℕ) (k j : ℕ),
    Odd m ∧ x = (m : ℤ) * 2 ^ k ∧ y = m * 2 ^ j ∧ j ≤ max k 1

noncomputable def zmax {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℤ) : ℤ :=
  (s.image f).max' (hs.image f)

noncomputable def zmin {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℤ) : ℤ :=
  (s.image f).min' (hs.image f)

noncomputable def zspread {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℤ) : ℤ :=
  zmax s hs f - zmin s hs f

noncomputable def nmax {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℕ) : ℕ :=
  (s.image f).max' (hs.image f)

noncomputable def nmin {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℕ) : ℕ :=
  (s.image f).min' (hs.image f)

noncomputable def nspread {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℕ) : ℕ :=
  nmax s hs f - nmin s hs f

theorem univFinNonempty (n : ℕ) (h : 0 < n) : (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0, h⟩, Finset.mem_univ _⟩

def firstK (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i : ℕ) < k)

lemma firstK_nonempty {n k : ℕ} (hn : 0 < n) (hk : 0 < k) : (firstK n k).Nonempty := by
  refine ⟨⟨0, hn⟩, ?_⟩
  simp [firstK, hk]

noncomputable def minVal (S : Set ℤ) : ℤ :=
  ((sInf (Set.preimage (fun n : ℕ => (n : ℤ)) S) : ℕ) : ℤ)

noncomputable def spreadSet (nums : Slice Std.I64) (s : Finset (Fin nums.val.length))
    (hs : s.Nonempty) : Set ℤ :=
  { d | ∃ y : Fin nums.val.length → ℕ,
      (∀ i ∈ s, 0 < y i ∧ Reach (nums.val[i]).val (y i)) ∧
      d = (nspread s hs y : ℤ) }

noncomputable def spreads (nums : Slice Std.I64) (hn : 0 < nums.val.length) : Set ℤ :=
  spreadSet nums Finset.univ (univFinNonempty _ hn)

noncomputable def fullNSpread (nums : Slice Std.I64) (h : 0 < nums.val.length)
    (y : Fin nums.val.length → ℕ) : ℕ :=
  nspread Finset.univ (univFinNonempty _ h) y

noncomputable def fullMax (nums : Slice Std.I64) (h : 0 < nums.val.length)
    (f : Fin nums.val.length → ℤ) : ℤ :=
  zmax Finset.univ (univFinNonempty _ h) f

noncomputable def fullMin (nums : Slice Std.I64) (h : 0 < nums.val.length)
    (f : Fin nums.val.length → ℤ) : ℤ :=
  zmin Finset.univ (univFinNonempty _ h) f

noncomputable def fullSpread (nums : Slice Std.I64) (h : 0 < nums.val.length)
    (f : Fin nums.val.length → ℤ) : ℤ :=
  zspread Finset.univ (univFinNonempty _ h) f

noncomputable def reachSet (x : ℤ) : Finset ℕ :=
  (Finset.range (max (v2 x.toNat) 1 + 1)).image (fun j => oddpartNat x.toNat * 2 ^ j)

lemma reachSet_nonempty (x : ℤ) : (reachSet x).Nonempty := by
  unfold reachSet
  exact Finset.Nonempty.image ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ _

noncomputable def deltaVals (x y : ℤ) : Finset ℕ :=
  (reachSet x ×ˢ reachSet y).image (fun p => max (p.1 - p.2) (p.2 - p.1))

lemma deltaVals_nonempty (x y : ℤ) : (deltaVals x y).Nonempty := by
  unfold deltaVals
  exact Finset.Nonempty.image
    (Finset.Nonempty.product (reachSet_nonempty x) (reachSet_nonempty y)) _

noncomputable def delta (x y : ℤ) : ℕ :=
  (deltaVals x y).min' (deltaVals_nonempty x y)

def upperReach (x : ℤ) : ℤ := oddpart x * (2 : ℤ) ^ max (v2 x.toNat) 1

noncomputable def intervalSet (nums : Slice Std.I64) : Set ℤ :=
  { d | ∃ (A B : ℤ), A ≤ B ∧
      (∀ i : Fin nums.val.length,
        ∃ y : ℕ, 0 < y ∧ Reach (nums.val[i]).val y ∧ A ≤ (y : ℤ) ∧ (y : ℤ) ≤ B) ∧
      d = B - A }

structure Precond (nums : Slice Std.I64) : Prop where
  len_ge : 2 ≤ nums.val.length
  len_le : nums.val.length ≤ 50000
  val_bounds : ∀ i : Fin nums.val.length,
    1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000

lemma Precond.pos {nums : Slice Std.I64} (h : Precond nums) : 0 < nums.val.length := by
  have := h.len_ge; omega

/-- The function returns a result r, and r = min { (max_{0 <= i < n} y_i) - (min_{0 <= i < n} y_i) | y_0,...,y_{n-1} are positive integers and Reach(nums[i], y_i) for every i }, where Reach(x,y) is defined as follows. Write x = m * 2^k with m odd and k >= 0, and put e = max(k,1). Then Reach(x,y) holds exactly when y = m * 2^j for some integer j with 0 <= j <= e.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∃ r, minimum_deviation nums = ok r ∧ IsLeast (spreads nums hpre.pos) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∃ r, minimum_deviation nums = ok r ∧ IsLeast (spreads nums hpre.pos) r.val) := by
  sorry

/-- The function returns a result r on every input satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∃ r, minimum_deviation nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∃ r, minimum_deviation nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∀ r, minimum_deviation nums = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∀ r, minimum_deviation nums = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= (max_{0 <= i < n} nums[i]) - (min_{0 <= i < n} nums[i]).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∀ r, minimum_deviation nums = ok r →
      r.val ≤ fullSpread nums hpre.pos (fun i => (nums.val[i]).val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∀ r, minimum_deviation nums = ok r →
      r.val ≤ fullSpread nums hpre.pos (fun i => (nums.val[i]).val)) := by
  sorry

/-- For a positive integer x, let oddpart(x) be x divided by the largest power of 2 dividing x. Whenever the function returns a result r, r <= (max_{0 <= i < n} oddpart(nums[i])) - (min_{0 <= i < n} oddpart(nums[i])).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∀ r, minimum_deviation nums = ok r →
      r.val ≤ fullSpread nums hpre.pos (fun i => oddpart (nums.val[i]).val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∀ r, minimum_deviation nums = ok r →
      r.val ≤ fullSpread nums hpre.pos (fun i => oddpart (nums.val[i]).val)) := by
  sorry

/-- For each i, let m_i = oddpart(nums[i]) and let E_i = max(v2(nums[i]), 1), where v2(x) is the exponent of 2 in the factorization of x. Define L_i = m_i and U_i = m_i * 2^{E_i}. Whenever the function returns a result r, r >= (max_{0 <= i < n} L_i) - (min_{0 <= i < n} U_i).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∀ r, minimum_deviation nums = ok r →
      fullMax nums hpre.pos (fun i => oddpart (nums.val[i]).val) -
        fullMin nums hpre.pos (fun i => upperReach (nums.val[i]).val) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∀ r, minimum_deviation nums = ok r →
      fullMax nums hpre.pos (fun i => oddpart (nums.val[i]).val) -
        fullMin nums hpre.pos (fun i => upperReach (nums.val[i]).val) ≤ r.val) := by
  sorry

/-- For every pair of indices i,j with 0 <= i < j < n, let delta(i,j) = min { |a-b| : a is reachable from nums[i] and b is reachable from nums[j] }. Here a is reachable from x exactly when, writing x = m * 2^k with m odd, a = m * 2^t for some integer t with 0 <= t <= max(k,1). Whenever the function returns a result r, r >= delta(i,j).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∀ r, minimum_deviation nums = ok r →
      ∀ i j : Fin nums.val.length, (i : ℕ) < (j : ℕ) →
        (delta (nums.val[i]).val (nums.val[j]).val : ℤ) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∀ r, minimum_deviation nums = ok r →
      ∀ i j : Fin nums.val.length, (i : ℕ) < (j : ℕ) →
        (delta (nums.val[i]).val (nums.val[j]).val : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist positive integers y_0,...,y_{n-1} such that Reach(nums[i], y_i) for every i and (max_{0 <= i < n} y_i) - (min_{0 <= i < n} y_i) = r. Here Reach(x,y) means: if x = m * 2^k with m odd, then y = m * 2^j for some integer j with 0 <= j <= max(k,1).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∀ r, minimum_deviation nums = ok r →
      ∃ y : Fin nums.val.length → ℕ,
        (∀ i : Fin nums.val.length, 0 < y i ∧ Reach (nums.val[i]).val (y i)) ∧
        (fullNSpread nums hpre.pos y : ℤ) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∀ r, minimum_deviation nums = ok r →
      ∃ y : Fin nums.val.length → ℕ,
        (∀ i : Fin nums.val.length, 0 < y i ∧ Reach (nums.val[i]).val (y i)) ∧
        (fullNSpread nums hpre.pos y : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every choice of positive integers y_0,...,y_{n-1} such that Reach(nums[i], y_i) for every i, one has r <= (max_{0 <= i < n} y_i) - (min_{0 <= i < n} y_i). Here Reach(x,y) means: if x = m * 2^k with m odd, then y = m * 2^j for some integer j with 0 <= j <= max(k,1).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∀ r, minimum_deviation nums = ok r →
      ∀ y : Fin nums.val.length → ℕ,
        (∀ i : Fin nums.val.length, 0 < y i ∧ Reach (nums.val[i]).val (y i)) →
        r.val ≤ (fullNSpread nums hpre.pos y : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∀ r, minimum_deviation nums = ok r →
      ∀ y : Fin nums.val.length → ℕ,
        (∀ i : Fin nums.val.length, 0 < y i ∧ Reach (nums.val[i]).val (y i)) →
        r.val ≤ (fullNSpread nums hpre.pos y : ℤ)) := by
  sorry

/-- For a positive integer x, let oddpart(x) be x divided by the largest power of 2 dividing x. Whenever the function returns a result r, r = 0 if and only if oddpart(nums[i]) = oddpart(nums[j]) for every pair of indices i,j with 0 <= i < n and 0 <= j < n.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∀ r, minimum_deviation nums = ok r →
      (r.val = 0 ↔
        ∀ i j : Fin nums.val.length,
          oddpart (nums.val[i]).val = oddpart (nums.val[j]).val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∀ r, minimum_deviation nums = ok r →
      (r.val = 0 ↔
        ∀ i j : Fin nums.val.length,
          oddpart (nums.val[i]).val = oddpart (nums.val[j]).val)) := by
  sorry

/-- Whenever the function returns a result r, for every pair of integers A and B with A <= B, if for every i with 0 <= i < n there exists a positive integer y_i reachable from nums[i] with A <= y_i <= B, then r <= B - A. Here reachable is as follows: if x = m * 2^k with m odd, the reachable values from x are m * 2^j for 0 <= j <= max(k,1).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_11 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∀ r, minimum_deviation nums = ok r →
      ∀ A B : ℤ, A ≤ B →
        (∀ i : Fin nums.val.length,
          ∃ y : ℕ, 0 < y ∧ Reach (nums.val[i]).val y ∧ A ≤ (y : ℤ) ∧ (y : ℤ) ≤ B) →
        r.val ≤ B - A := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∀ r, minimum_deviation nums = ok r →
      ∀ A B : ℤ, A ≤ B →
        (∀ i : Fin nums.val.length,
          ∃ y : ℕ, 0 < y ∧ Reach (nums.val[i]).val y ∧ A ≤ (y : ℤ) ∧ (y : ℤ) ≤ B) →
        r.val ≤ B - A) := by
  sorry

/-- Whenever the function returns a result r, for every k with 2 <= k <= n, define D_k as the minimum, over all choices of positive integers y_0,...,y_{k-1} such that y_i is reachable from nums[i] for each 0 <= i < k, of (max_{0 <= i < k} y_i) - (min_{0 <= i < k} y_i). Here reachable is as follows: if nums[i] = m * 2^t with m odd, the reachable values from nums[i] are m * 2^j for 0 <= j <= max(t,1). Then r >= D_k.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_12 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∀ r, minimum_deviation nums = ok r →
      ∀ (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ nums.val.length),
        minVal (spreadSet nums (firstK nums.val.length k)
          (firstK_nonempty hpre.pos (by omega))) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∀ r, minimum_deviation nums = ok r →
      ∀ (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ nums.val.length),
        minVal (spreadSet nums (firstK nums.val.length k)
          (firstK_nonempty hpre.pos (by omega))) ≤ r.val) := by
  sorry

/-- For every nonempty subset I of {0,...,n-1}, let D_I be the minimum, over all choices of positive integers y_i with Reach(nums[i], y_i) for each i in I, of (max_{i in I} y_i) - (min_{i in I} y_i), where Reach(x,y) means: if x = m * 2^k with m odd, then y = m * 2^j for some integer j with 0 <= j <= max(k,1). Whenever the function returns a result r, r >= D_I.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_13 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∀ r, minimum_deviation nums = ok r →
      ∀ (I : Finset (Fin nums.val.length)) (hI : I.Nonempty),
        minVal (spreadSet nums I hI) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∀ r, minimum_deviation nums = ok r →
      ∀ (I : Finset (Fin nums.val.length)) (hI : I.Nonempty),
        minVal (spreadSet nums I hI) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = min { B - A | A and B are integers with A <= B and, for every i with 0 <= i < n, there exists a positive integer y_i reachable from nums[i] with A <= y_i <= B }. Here y is reachable from x exactly when, writing x = m * 2^k with m odd, y = m * 2^j for some integer j with 0 <= j <= max(k,1).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 50000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_14 (nums : Slice Std.I64) (hpre : Precond nums) :
    ∃ r, minimum_deviation nums = ok r ∧ IsLeast (intervalSet nums) r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∃ r, minimum_deviation nums = ok r ∧ IsLeast (intervalSet nums) r.val) := by
  sorry

end AegisSpec.MinimumDeviation
