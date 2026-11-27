import Aegis.NumberOfWeeks.Code.Funs

/-!
# Specifications of `Aegis.NumberOfWeeks.number_of_weeks`

LeetCode problem `maximum-number-of-weeks-for-which-you-can-work`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfWeeks

def contents (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

def lenI (s : Slice Std.I64) : Int := (s.val.length : Int)

def total (s : Slice Std.I64) : Int := (contents s).sum

def listMax : List Int → Int
  | [] => 0
  | a :: t => t.foldl max a

def listMin : List Int → Int
  | [] => 0
  | a :: t => t.foldl min a

def maxVal (s : Slice Std.I64) : Int := listMax (contents s)

def minVal (s : Slice Std.I64) : Int := listMin (contents s)

def elemAt (s : Slice Std.I64) (i : Nat) : Int :=
  match (contents s).drop i with
  | [] => 0
  | x :: _ => x

def ValuesOk (s : Slice Std.I64) : Prop :=
  ∀ (i : Nat) (hi : i < s.val.length),
    1 ≤ (s.val.get ⟨i, hi⟩).val ∧ (s.val.get ⟨i, hi⟩).val ≤ 1000000000

def countIdx (p : List Nat) (i : Nat) : Nat := p.count i

def AdjacentDistinct (p : List Nat) : Prop :=
  ∀ (j : Nat) (h : j + 1 < p.length),
    p.get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) h⟩ ≠ p.get ⟨j + 1, h⟩

def Feasible (s : Slice Std.I64) (p : List Nat) : Prop :=
  (∀ j ∈ p, j < s.val.length) ∧
  (∀ (i : Nat) (hi : i < s.val.length), countIdx p i ≤ (s.val.get ⟨i, hi⟩).val.toNat) ∧
  AdjacentDistinct p

/-- Let S = sum_{i=0}^{n-1} milestones[i] and M = max_{0 <= i < n} milestones[i]. The function returns a result r and r = min(S, 2*(S-M)+1).
  Preconditions: Let n = len(milestones). n >= 1, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_1 (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones) :
    ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧
        r.val = min (total milestones) (2 * (total milestones - maxVal milestones) + 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones), ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧
        r.val = min (total milestones) (2 * (total milestones - maxVal milestones) + 1)) := by
  sorry

/-- The function returns a result r and does not fail: there is no arithmetic overflow, out-of-bounds access, or panic on any input satisfying the preconditions.
  Preconditions: Let n = len(milestones). n >= 1, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_2 (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones) :
    ∃ r : Std.I64, Aegis.NumberOfWeeks.number_of_weeks milestones = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones), ∃ r : Std.I64, Aegis.NumberOfWeeks.number_of_weeks milestones = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= S, where S = sum_{i=0}^{n-1} milestones[i].
  Preconditions: Let n = len(milestones). n >= 1, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_3 (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones) :
    ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r → r.val ≤ total milestones := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones), ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r → r.val ≤ total milestones) := by
  sorry

/-- Whenever the function returns a result r, r <= 2*(S-M)+1, where S = sum_{i=0}^{n-1} milestones[i] and M = max_{0 <= i < n} milestones[i].
  Preconditions: Let n = len(milestones). n >= 1, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_4 (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones) :
    ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r →
        r.val ≤ 2 * (total milestones - maxVal milestones) + 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones), ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r →
        r.val ≤ 2 * (total milestones - maxVal milestones) + 1) := by
  sorry

/-- Whenever the function returns a result r, r >= n.
  Preconditions: Let n = len(milestones). n >= 1, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_5 (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones) :
    ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r → lenI milestones ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones), ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r → lenI milestones ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= 2 * min_{0 <= i < n} milestones[i].
  Preconditions: Let n = len(milestones). n >= 2, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_6 (milestones : Slice Std.I64)
    (hlen_ge : 2 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones) :
    ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r → 2 * minVal milestones ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_ge : 2 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones), ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r → 2 * minVal milestones ≤ r.val) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: Let n = len(milestones). n = 1, and 1 <= milestones[0] <= 1000000000. -/
theorem spec_7 (milestones : Slice Std.I64)
    (hlen : milestones.val.length = 1)
    (hvals : ValuesOk milestones) :
    ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧ r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen : milestones.val.length = 1)
    (hvals : ValuesOk milestones), ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧ r.val = 1) := by
  sorry

/-- Let a = milestones[0] and b = milestones[1]. The function returns a result r and r = min(a+b, 2*min(a,b)+1).
  Preconditions: Let n = len(milestones). n = 2, and 1 <= milestones[0] <= 1000000000, 1 <= milestones[1] <= 1000000000. -/
theorem spec_8 (milestones : Slice Std.I64)
    (hlen : milestones.val.length = 2)
    (hvals : ValuesOk milestones) :
    ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧
        r.val = min (elemAt milestones 0 + elemAt milestones 1)
          (2 * min (elemAt milestones 0) (elemAt milestones 1) + 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen : milestones.val.length = 2)
    (hvals : ValuesOk milestones), ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧
        r.val = min (elemAt milestones 0 + elemAt milestones 1)
          (2 * min (elemAt milestones 0) (elemAt milestones 1) + 1)) := by
  sorry

/-- The function returns a result r and r = n*c. Equivalently, r = S, where S = sum_{i=0}^{n-1} milestones[i].
  Preconditions: Let n = len(milestones). n >= 2, n <= 100000, and there exists an integer c >= 1 such that milestones[i] = c for every i with 0 <= i < n. -/
theorem spec_9 (milestones : Slice Std.I64) (c : Int)
    (hlen_ge : 2 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hc : 1 ≤ c)
    (hconst : ∀ (i : Nat) (hi : i < milestones.val.length),
      (milestones.val.get ⟨i, hi⟩).val = c) :
    ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧
        r.val = lenI milestones * c ∧ r.val = total milestones := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (milestones : Slice Std.I64) (c : Int)
    (hlen_ge : 2 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hc : 1 ≤ c)
    (hconst : ∀ (i : Nat) (hi : i < milestones.val.length),
      (milestones.val.get ⟨i, hi⟩).val = c), ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧
        r.val = lenI milestones * c ∧ r.val = total milestones) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} milestones[i] and M = max_{0 <= i < n} milestones[i]. If M <= (S-M)+1, then the function returns a result r and r = S.
  Preconditions: Let n = len(milestones). n >= 1, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_10 (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones)
    (hM : maxVal milestones ≤ (total milestones - maxVal milestones) + 1) :
    ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧ r.val = total milestones := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones)
    (hM : maxVal milestones ≤ (total milestones - maxVal milestones) + 1), ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧ r.val = total milestones) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} milestones[i] and M = max_{0 <= i < n} milestones[i]. If M > (S-M)+1, then the function returns a result r and r = 2*(S-M)+1.
  Preconditions: Let n = len(milestones). n >= 1, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_11 (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones)
    (hM : (total milestones - maxVal milestones) + 1 < maxVal milestones) :
    ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧
        r.val = 2 * (total milestones - maxVal milestones) + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones)
    (hM : (total milestones - maxVal milestones) + 1 < maxVal milestones), ∃ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r ∧
        r.val = 2 * (total milestones - maxVal milestones) + 1) := by
  sorry

/-- Whenever the function returns a result r, S - r = max(0, 2*M - S - 1), where S = sum_{i=0}^{n-1} milestones[i] and M = max_{0 <= i < n} milestones[i].
  Preconditions: Let n = len(milestones). n >= 1, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_12 (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones) :
    ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r →
        total milestones - r.val = max 0 (2 * maxVal milestones - total milestones - 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones), ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r →
        total milestones - r.val = max 0 (2 * maxVal milestones - total milestones - 1)) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite sequence of project indices p_0, p_1, ..., p_{r-1} such that: (1) each p_j is an integer with 0 <= p_j < n; (2) for every project i, the number of indices j with p_j = i is at most milestones[i]; and (3) p_j != p_{j+1} for every j with 0 <= j < r-1.
  Preconditions: Let n = len(milestones). n >= 1, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_13 (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones) :
    ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r →
        ∃ p : List Nat, Feasible milestones p ∧ (p.length : Int) = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones), ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r →
        ∃ p : List Nat, Feasible milestones p ∧ (p.length : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer W >= 0 and every finite sequence of project indices p_0, p_1, ..., p_{W-1} satisfying: each p_j is in [0,n-1], each project i is used at most milestones[i] times, and p_j != p_{j+1} for every j with 0 <= j < W-1, we have W <= r.
  Preconditions: Let n = len(milestones). n >= 1, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_14 (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones) :
    ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r →
        ∀ p : List Nat, Feasible milestones p → (p.length : Int) ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones), ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r →
        ∀ p : List Nat, Feasible milestones p → (p.length : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if r < S, where S = sum_{i=0}^{n-1} milestones[i], then r is odd.
  Preconditions: Let n = len(milestones). n >= 1, n <= 100000, and for every integer i with 0 <= i < n, 1 <= milestones[i] <= 1000000000. -/
theorem spec_15 (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones) :
    ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r →
        r.val < total milestones → Odd r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (milestones : Slice Std.I64)
    (hlen_pos : 1 ≤ milestones.val.length)
    (hlen_le : milestones.val.length ≤ 100000)
    (hvals : ValuesOk milestones), ∀ r : Std.I64,
      Aegis.NumberOfWeeks.number_of_weeks milestones = ok r →
        r.val < total milestones → Odd r.val) := by
  sorry

end AegisSpec.NumberOfWeeks
