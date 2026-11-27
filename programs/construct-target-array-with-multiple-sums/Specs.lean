import Aegis.IsPossible.Code.Funs

/-!
# Specifications of `Aegis.IsPossible.is_possible`

LeetCode problem `construct-target-array-with-multiple-sums`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IsPossible (is_possible)

namespace AegisSpec.IsPossible

def ivals (target : Slice I64) : List ℤ := target.val.map (fun x => x.val)

def ones (n : ℕ) : List ℤ := List.replicate n (1 : ℤ)

def sumOthers (l : List I64) (i : ℕ) : ℤ :=
  ((l.take i).map (fun x => x.val)).sum + ((l.drop (i + 1)).map (fun x => x.val)).sum

def replaceAt (l : List ℤ) (i : ℕ) (v : ℤ) : List ℤ := l.take i ++ (v :: l.drop (i + 1))

def StepAt (a : List ℤ) (i : ℕ) (a' : List ℤ) : Prop :=
  i < a.length ∧ a' = replaceAt a i a.sum

def Step (a a' : List ℤ) : Prop := ∃ i : ℕ, StepAt a i a'

def IsChain (n : ℕ) (A : ℕ → List ℤ) (k : ℕ) : Prop :=
  (∀ t, t ≤ k → (A t).length = n) ∧ A 0 = ones n ∧ ∀ t, t < k → Step (A t) (A (t + 1))

def IsChainAt (n : ℕ) (A : ℕ → List ℤ) (idx : ℕ → ℕ) (k : ℕ) : Prop :=
  (∀ t, t ≤ k → (A t).length = n) ∧ A 0 = ones n ∧
    ∀ t, t < k → StepAt (A t) (idx t) (A (t + 1))

def Constructible (tgt : List ℤ) : Prop :=
  ∃ (k : ℕ) (A : ℕ → List ℤ), IsChain tgt.length A k ∧ A k = tgt

def MajorityIndex (l : List I64) (i : ℕ) : Prop :=
  ∃ x : I64, l[i]? = some x ∧ x.val > sumOthers l i

def NotAllOnes (l : List I64) : Prop :=
  ∃ (i : ℕ) (x : I64), l[i]? = some x ∧ x.val ≠ 1

def EntriesInRange (l : List I64) : Prop :=
  ∀ (i : ℕ) (x : I64), l[i]? = some x → 1 ≤ x.val ∧ x.val ≤ 1000000000

def IsCommonDivisor (l : List I64) (d : ℕ) : Prop :=
  ∀ (i : ℕ) (x : I64), l[i]? = some x → (d : ℤ) ∣ x.val

/-- Whenever the function returns a result r, r is true if and only if there exist an integer k >= 0 and arrays A^0,...,A^k, each of length n, such that: (1) A^0[i] = 1 for every 0 <= i < n; (2) A^k[i] = target[i] for every 0 <= i < n; and (3) for every t with 0 <= t < k there is an index i_t with 0 <= i_t < n such that A^{t+1}[i_t] = sum_{j=0}^{n-1} A^t[j] and A^{t+1}[j] = A^t[j] for every j with 0 <= j < n and j != i_t. Equivalently, r is false exactly when no such finite sequence exists.
  Preconditions: Let n = len(target). The slice is nonempty with 1 <= n <= 50000, and every entry satisfies 1 <= target[i] <= 10^9 for 0 <= i < n. -/
theorem spec_1 (target : Slice I64)
    (hn_pos : 1 ≤ target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) :
    (r = true ↔ Constructible (ivals target)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (target : Slice I64)
    (hn_pos : 1 ≤ target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r), (r = true ↔ Constructible (ivals target))) := by
  sorry

/-- For every target satisfying the preconditions, the function returns a result (a Bool); it does not fail, panic, or overflow.
  Preconditions: Let n = len(target). The slice is nonempty with 1 <= n <= 50000, and every entry satisfies 1 <= target[i] <= 10^9 for 0 <= i < n. -/
theorem spec_2 (target : Slice I64)
    (hn_pos : 1 ≤ target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val) :
    ∃ r : Bool, is_possible target = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (target : Slice I64)
    (hn_pos : 1 ≤ target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val), ∃ r : Bool, is_possible target = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, r is true if and only if target[0] = 1.
  Preconditions: n = len(target) = 1 and 1 <= target[0] <= 10^9. -/
theorem spec_3 (target : Slice I64) (x : I64)
    (hn : target.val.length = 1) (h0 : target.val[0]? = some x)
    (hlo : 1 ≤ x.val) (hhi : x.val ≤ 1000000000)
    (r : Bool) (hr : is_possible target = Result.ok r) :
    (r = true ↔ x.val = 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (target : Slice I64) (x : I64)
    (hn : target.val.length = 1) (h0 : target.val[0]? = some x)
    (hlo : 1 ≤ x.val) (hhi : x.val ≤ 1000000000)
    (r : Bool) (hr : is_possible target = Result.ok r), (r = true ↔ x.val = 1)) := by
  sorry

/-- Whenever the function returns a result r, r is true.
  Preconditions: n = len(target) >= 1 and target[i] = 1 for every 0 <= i < n. -/
theorem spec_4 (target : Slice I64)
    (hn : 1 ≤ target.val.length)
    (hall : ∀ (i : ℕ) (x : I64), target.val[i]? = some x → x.val = 1)
    (r : Bool) (hr : is_possible target = Result.ok r) :
    r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (target : Slice I64)
    (hn : 1 ≤ target.val.length)
    (hall : ∀ (i : ℕ) (x : I64), target.val[i]? = some x → x.val = 1)
    (r : Bool) (hr : is_possible target = Result.ok r), r = true) := by
  sorry

/-- Whenever the function returns a result r, r is false.
  Preconditions: n = len(target) > 1 and there exists an integer c > 1 such that target[i] = c for every 0 <= i < n. -/
theorem spec_5 (target : Slice I64) (c : ℤ)
    (hn : 1 < target.val.length) (hc : 1 < c)
    (hall : ∀ (i : ℕ) (x : I64), target.val[i]? = some x → x.val = c)
    (r : Bool) (hr : is_possible target = Result.ok r) :
    r = false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (target : Slice I64) (c : ℤ)
    (hn : 1 < target.val.length) (hc : 1 < c)
    (hall : ∀ (i : ℕ) (x : I64), target.val[i]? = some x → x.val = c)
    (r : Bool) (hr : is_possible target = Result.ok r), r = false) := by
  sorry

/-- Whenever the function returns a result r with r = true, the greatest positive integer d that divides target[i] for every 0 <= i < n is 1.
  Preconditions: Let n = len(target). The slice is nonempty with 1 <= n <= 50000, and every entry satisfies 1 <= target[i] <= 10^9 for 0 <= i < n. -/
theorem spec_6 (target : Slice I64)
    (hn_pos : 1 ≤ target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true) :
    ∀ d : ℕ, 0 < d → IsCommonDivisor target.val d → d = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (target : Slice I64)
    (hn_pos : 1 ≤ target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true), ∀ d : ℕ, 0 < d → IsCommonDivisor target.val d → d = 1) := by
  sorry

/-- Whenever the function returns a result r, r is true if and only if gcd(target[0], target[1]) = 1, where gcd(a,b) is the greatest positive integer dividing both a and b.
  Preconditions: n = len(target) = 2, and 1 <= target[0], target[1] <= 10^9. -/
theorem spec_7 (target : Slice I64) (a b : I64)
    (hn : target.val.length = 2) (h0 : target.val[0]? = some a) (h1 : target.val[1]? = some b)
    (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
    (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
    (r : Bool) (hr : is_possible target = Result.ok r) :
    (r = true ↔ ∀ d : ℕ, 0 < d → (d : ℤ) ∣ a.val → (d : ℤ) ∣ b.val → d = 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (target : Slice I64) (a b : I64)
    (hn : target.val.length = 2) (h0 : target.val[0]? = some a) (h1 : target.val[1]? = some b)
    (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
    (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
    (r : Bool) (hr : is_possible target = Result.ok r), (r = true ↔ ∀ d : ℕ, 0 < d → (d : ℤ) ∣ a.val → (d : ℤ) ∣ b.val → d = 1)) := by
  sorry

/-- Whenever the function returns a result r with r = true and target is not the all-ones array, there is exactly one index i with 0 <= i < n such that target[i] > sum_{0 <= j < n, j != i} target[j].
  Preconditions: Let n = len(target) > 1, with 1 <= n <= 50000 and 1 <= target[i] <= 10^9 for 0 <= i < n. -/
theorem spec_8 (target : Slice I64)
    (hn : 1 < target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true)
    (hnotones : NotAllOnes target.val) :
    ∃! i : ℕ, MajorityIndex target.val i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (target : Slice I64)
    (hn : 1 < target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true)
    (hnotones : NotAllOnes target.val), ∃! i : ℕ, MajorityIndex target.val i) := by
  sorry

/-- There is a unique index i with 0 <= i < n such that target[i] > sum_{0 <= j < n, j != i} target[j]. For this i, define target' by target'[i] = target[i] - sum_{0 <= j < n, j != i} target[j] and target'[j] = target[j] for every j != i. Then target' is constructible from the all-ones array by the same operation, i.e. there is a finite sequence as in spec_1 ending at target'.
  Preconditions: Let n = len(target) > 1, with 1 <= n <= 50000 and 1 <= target[i] <= 10^9 for 0 <= i < n. Assume the function returns r = true and target is not the all-ones array. -/
theorem spec_9 (target : Slice I64)
    (hn : 1 < target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true)
    (hnotones : NotAllOnes target.val) :
    (∃! i : ℕ, MajorityIndex target.val i) ∧
      ∀ (i : ℕ) (x : I64), MajorityIndex target.val i → target.val[i]? = some x →
        Constructible (replaceAt (ivals target) i (x.val - sumOthers target.val i)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (target : Slice I64)
    (hn : 1 < target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true)
    (hnotones : NotAllOnes target.val), (∃! i : ℕ, MajorityIndex target.val i) ∧
      ∀ (i : ℕ) (x : I64), MajorityIndex target.val i → target.val[i]? = some x →
        Constructible (replaceAt (ivals target) i (x.val - sumOthers target.val i))) := by
  sorry

/-- Whenever the function returns a result r, r is true if and only if there exists an integer q >= 0 such that target[i] = 1 + q*(n-1).
  Preconditions: n = len(target) > 1, and there is exactly one index i with 0 <= i < n such that target[i] > 1, while target[j] = 1 for every j != i. Also 1 <= target[i] <= 10^9. -/
theorem spec_10 (target : Slice I64) (i : ℕ) (c : I64)
    (hn : 1 < target.val.length) (hi : i < target.val.length)
    (hc : target.val[i]? = some c) (hc_gt : 1 < c.val) (hc_le : c.val ≤ 1000000000)
    (hrest : ∀ (j : ℕ) (y : I64), j ≠ i → target.val[j]? = some y → y.val = 1)
    (r : Bool) (hr : is_possible target = Result.ok r) :
    (r = true ↔ ∃ q : ℕ, c.val = 1 + (q : ℤ) * ((target.val.length : ℤ) - 1)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (target : Slice I64) (i : ℕ) (c : I64)
    (hn : 1 < target.val.length) (hi : i < target.val.length)
    (hc : target.val[i]? = some c) (hc_gt : 1 < c.val) (hc_le : c.val ≤ 1000000000)
    (hrest : ∀ (j : ℕ) (y : I64), j ≠ i → target.val[j]? = some y → y.val = 1)
    (r : Bool) (hr : is_possible target = Result.ok r), (r = true ↔ ∃ q : ℕ, c.val = 1 + (q : ℤ) * ((target.val.length : ℤ) - 1))) := by
  sorry

/-- Whenever the function returns a result r with r = true, target[i] is odd for every 0 <= i < n, equivalently target[i] mod 2 = 1.
  Preconditions: n = len(target) is odd, with 1 <= n <= 50000, and 1 <= target[i] <= 10^9 for 0 <= i < n. -/
theorem spec_11 (target : Slice I64)
    (hn_pos : 1 ≤ target.val.length) (hn_le : target.val.length ≤ 50000)
    (hn_odd : Odd target.val.length)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true) :
    ∀ (i : ℕ) (x : I64), target.val[i]? = some x → x.val % 2 = 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (target : Slice I64)
    (hn_pos : 1 ≤ target.val.length) (hn_le : target.val.length ≤ 50000)
    (hn_odd : Odd target.val.length)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true), ∀ (i : ℕ) (x : I64), target.val[i]? = some x → x.val % 2 = 1) := by
  sorry

/-- For every permutation pi of {0,...,n-1}, let target' be defined by target'[i] = target[pi(i)] for 0 <= i < n. Whenever the function returns a result r on target and a result r' on target', we have r = r'.
  Preconditions: Let n = len(target). The slice is nonempty with 1 <= n <= 50000, and every entry satisfies 1 <= target[i] <= 10^9 for 0 <= i < n. -/
theorem spec_12 (target perm : Slice I64)
    (hn_pos : 1 ≤ target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (his_perm : List.Perm perm.val target.val)
    (r r' : Bool) (hr : is_possible target = Result.ok r) (hr' : is_possible perm = Result.ok r') :
    r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (target perm : Slice I64)
    (hn_pos : 1 ≤ target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (his_perm : List.Perm perm.val target.val)
    (r r' : Bool) (hr : is_possible target = Result.ok r) (hr' : is_possible perm = Result.ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r with r = true, sum_{i=0}^{n-1} target[i] >= 2*n - 1.
  Preconditions: Let n = len(target) > 1, with 1 <= n <= 50000 and 1 <= target[i] <= 10^9 for 0 <= i < n. Assume target is not the all-ones array. -/
theorem spec_13 (target : Slice I64)
    (hn : 1 < target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val) (hnotones : NotAllOnes target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true) :
    (ivals target).sum ≥ 2 * (target.val.length : ℤ) - 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (target : Slice I64)
    (hn : 1 < target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val) (hnotones : NotAllOnes target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true), (ivals target).sum ≥ 2 * (target.val.length : ℤ) - 1) := by
  sorry

/-- Let i be the unique index with 0 <= i < n such that target[i] > sum_{0 <= j < n, j != i} target[j]. Then every finite sequence A^0,...,A^k as in spec_1 with A^k = target has k >= 1, and its last step (t = k-1) chooses index i, i.e. i_{k-1} = i.
  Preconditions: Let n = len(target) > 1, with 1 <= n <= 50000 and 1 <= target[i] <= 10^9 for 0 <= i < n. Assume the function returns r = true and target is not the all-ones array. -/
theorem spec_14 (target : Slice I64)
    (hn : 1 < target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true)
    (hnotones : NotAllOnes target.val) :
    ∀ (i : ℕ), MajorityIndex target.val i →
      ∀ (k : ℕ) (A : ℕ → List ℤ) (idx : ℕ → ℕ),
        IsChainAt target.val.length A idx k → A k = ivals target → 1 ≤ k ∧ idx (k - 1) = i := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (target : Slice I64)
    (hn : 1 < target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val)
    (r : Bool) (hr : is_possible target = Result.ok r) (hr_true : r = true)
    (hnotones : NotAllOnes target.val), ∀ (i : ℕ), MajorityIndex target.val i →
      ∀ (k : ℕ) (A : ℕ → List ℤ) (idx : ℕ → ℕ),
        IsChainAt target.val.length A idx k → A k = ivals target → 1 ≤ k ∧ idx (k - 1) = i) := by
  sorry

/-- Whenever the function returns results r on target and r' on target', r = true if and only if r' = true; equivalently, target is constructible exactly when target' is constructible.
  Preconditions: Let n = len(target) > 1, with 1 <= n <= 50000 and 1 <= target[i] <= 10^9 for 0 <= i < n. Assume target is not the all-ones array and has a unique index i with 0 <= i < n such that target[i] > sum_{0 <= j < n, j != i} target[j]. Define target' by target'[i] = target[i] - sum_{0 <= j < n, j != i} target[j] and target'[j] = target[j] for every j != i. -/
theorem spec_15 (target reduced : Slice I64)
    (hn : 1 < target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val) (hnotones : NotAllOnes target.val)
    (i : ℕ) (x : I64) (hi : i < target.val.length) (hx : target.val[i]? = some x)
    (hmaj : MajorityIndex target.val i)
    (huniq : ∀ j : ℕ, MajorityIndex target.val j → j = i)
    (hval : ivals reduced = replaceAt (ivals target) i (x.val - sumOthers target.val i))
    (r r' : Bool) (hr : is_possible target = Result.ok r) (hr' : is_possible reduced = Result.ok r') :
    (r = true ↔ r' = true) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (target reduced : Slice I64)
    (hn : 1 < target.val.length) (hn_le : target.val.length ≤ 50000)
    (hrange : EntriesInRange target.val) (hnotones : NotAllOnes target.val)
    (i : ℕ) (x : I64) (hi : i < target.val.length) (hx : target.val[i]? = some x)
    (hmaj : MajorityIndex target.val i)
    (huniq : ∀ j : ℕ, MajorityIndex target.val j → j = i)
    (hval : ivals reduced = replaceAt (ivals target) i (x.val - sumOthers target.val i))
    (r r' : Bool) (hr : is_possible target = Result.ok r) (hr' : is_possible reduced = Result.ok r'), (r = true ↔ r' = true)) := by
  sorry

end AegisSpec.IsPossible
