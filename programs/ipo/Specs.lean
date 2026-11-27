import Aegis.FindMaximizedCapital.Code.Funs

/-!
# Specifications of `Aegis.FindMaximizedCapital.find_maximized_capital`

LeetCode problem `ipo`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindMaximizedCapital

def IsMaxOf (S : Set ℤ) (m : ℤ) : Prop := m ∈ S ∧ ∀ x ∈ S, x ≤ m

def capitalAfter (profits : List I64) (w : ℤ) (P : List ℕ) : ℕ → ℤ
  | 0 => w
  | j + 1 => capitalAfter profits w P j + (profits.getD (P.getD j 0) 0#i64).val

def IsPlan (n : ℕ) (k : ℤ) (P : List ℕ) : Prop :=
  (P.length : ℤ) ≤ k ∧ P.Nodup ∧ ∀ j ∈ P, j < n

def IsFeasiblePlan (profits capital : List I64) (w : ℤ) (n : ℕ) (k : ℤ) (P : List ℕ) : Prop :=
  IsPlan n k P ∧ ∀ j, j < P.length →
    (capital.getD (P.getD j 0) 0#i64).val ≤ capitalAfter profits w P j

def feasibleFinals (profits capital : List I64) (w : ℤ) (n : ℕ) (k : ℤ) : Set ℤ :=
  {c : ℤ | ∃ P : List ℕ,
    IsFeasiblePlan profits capital w n k P ∧ c = capitalAfter profits w P P.length}

def insertDesc (x : ℤ) : List ℤ → List ℤ
  | [] => [x]
  | y :: ys => if x ≥ y then x :: y :: ys else y :: insertDesc x ys

def sortDesc : List ℤ → List ℤ
  | [] => []
  | x :: xs => insertDesc x (sortDesc xs)

def topSum (m : ℕ) (l : List I64) : ℤ := ((sortDesc (l.map fun x => x.val)).take m).sum

def IsPermOf (n : ℕ) (sigma : ℕ → ℕ) : Prop :=
  (∀ i, i < n → sigma i < n) ∧ ∀ i, i < n → ∀ j, j < n → sigma i = sigma j → i = j

def permute (sigma : ℕ → ℕ) (l : List I64) : List I64 :=
  List.ofFn fun i : Fin l.length => l.getD (sigma i) 0#i64

/-- Whenever find_maximized_capital(k, w, profits, capital) returns a result r, r equals the maximum final capital over all feasible plans, defined as follows. A plan is a finite sequence P = (p_0, ..., p_{m-1}) where m is an integer with 0 <= m <= k and p_0, ..., p_{m-1} are pairwise distinct integers with 0 <= p_j < n for all j. For a plan P set C_0 = w and C_{j+1} = C_j + profits[p_j] for 0 <= j < m; P is feasible iff C_j >= capital[p_j] for every j with 0 <= j < m; its final capital is C_m. Then r = max { C_m : P is a feasible plan }.
  Preconditions: 1 <= k <= 100000; 0 <= w <= 10^9; n := len(profits) = len(capital); 1 <= n <= 100000; for every i with 0 <= i < n: 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9. (These bounds imply the maximized capital is at most 2*10^9, which fits in the 32-bit signed range as the statement guarantees.) -/
theorem spec_1 (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r) :
    IsMaxOf (feasibleFinals profits.val capital.val w.val profits.val.length k.val) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r), IsMaxOf (feasibleFinals profits.val capital.val w.val profits.val.length k.val) r.val) := by
  sorry

/-- find_maximized_capital(k, w, profits, capital) returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= k <= 100000; 0 <= w <= 10^9; n := len(profits) = len(capital); 1 <= n <= 100000; for every i with 0 <= i < n: 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9. -/
theorem spec_2 (k w : I64) (profits capital : Slice I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000) :
    ∃ r : I64, Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (k w : I64) (profits capital : Slice I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000), ∃ r : I64, Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r) := by
  sorry

/-- Whenever find_maximized_capital(k, w, profits, capital) returns a result r, we have r >= w.
  Preconditions: 1 <= k <= 100000; 0 <= w <= 10^9; n := len(profits) = len(capital); 1 <= n <= 100000; for every i with 0 <= i < n: 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9. -/
theorem spec_3 (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r) :
    w.val ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r), w.val ≤ r.val) := by
  sorry

/-- Whenever find_maximized_capital(k, w, profits, capital) returns a result r, if L is the sum of the min(k, n) largest values among profits[0], ..., profits[n-1] (the sum of the min(k,n) largest elements of the multiset of profits, counting multiplicity), then r <= w + L.
  Preconditions: 1 <= k <= 100000; 0 <= w <= 10^9; n := len(profits) = len(capital); 1 <= n <= 100000; for every i with 0 <= i < n: 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9. -/
theorem spec_4 (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r) :
    r.val ≤ w.val + topSum (min k.val.toNat profits.val.length) profits.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r), r.val ≤ w.val + topSum (min k.val.toNat profits.val.length) profits.val) := by
  sorry

/-- Whenever find_maximized_capital(k, w, profits, capital) returns a result r, there exists a feasible plan P (as defined in the main specification) whose final capital equals r.
  Preconditions: 1 <= k <= 100000; 0 <= w <= 10^9; n := len(profits) = len(capital); 1 <= n <= 100000; for every i with 0 <= i < n: 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9. -/
theorem spec_5 (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r) :
    ∃ P : List ℕ,
      IsFeasiblePlan profits.val capital.val w.val profits.val.length k.val P ∧
        capitalAfter profits.val w.val P P.length = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r), ∃ P : List ℕ,
      IsFeasiblePlan profits.val capital.val w.val profits.val.length k.val P ∧
        capitalAfter profits.val w.val P P.length = r.val) := by
  sorry

/-- Whenever find_maximized_capital(k, w, profits, capital) returns a result r, for every i with 0 <= i < n and capital[i] <= w we have r >= w + profits[i].
  Preconditions: 1 <= k <= 100000; 0 <= w <= 10^9; n := len(profits) = len(capital); 1 <= n <= 100000; for every i with 0 <= i < n: 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9. -/
theorem spec_6 (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r) :
    ∀ i, i < profits.val.length → (capital.val.getD i 0#i64).val ≤ w.val →
      w.val + (profits.val.getD i 0#i64).val ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r), ∀ i, i < profits.val.length → (capital.val.getD i 0#i64).val ≤ w.val →
      w.val + (profits.val.getD i 0#i64).val ≤ r.val) := by
  sorry

/-- Whenever find_maximized_capital(k, w, profits, capital) returns a result r, we have r = w.
  Preconditions: 1 <= k <= 100000; 0 <= w <= 10^9; n := len(profits) = len(capital); 1 <= n <= 100000; for every i with 0 <= i < n: 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9; and for every i with 0 <= i < n, capital[i] > w. -/
theorem spec_7 (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hnone : ∀ i, i < capital.val.length → w.val < (capital.val.getD i 0#i64).val)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r) :
    r.val = w.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hnone : ∀ i, i < capital.val.length → w.val < (capital.val.getD i 0#i64).val)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r), r.val = w.val) := by
  sorry

/-- Whenever find_maximized_capital(k, w, profits, capital) returns a result r, if L is the sum of the min(k, n) largest values among profits[0], ..., profits[n-1], then r = w + L.
  Preconditions: 1 <= k <= 100000; 0 <= w <= 10^9; n := len(profits) = len(capital); 1 <= n <= 100000; for every i with 0 <= i < n: 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9; and for every i with 0 <= i < n, capital[i] <= w. -/
theorem spec_8 (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hall : ∀ i, i < capital.val.length → (capital.val.getD i 0#i64).val ≤ w.val)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r) :
    r.val = w.val + topSum (min k.val.toNat profits.val.length) profits.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hall : ∀ i, i < capital.val.length → (capital.val.getD i 0#i64).val ≤ w.val)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r), r.val = w.val + topSum (min k.val.toNat profits.val.length) profits.val) := by
  sorry

/-- Whenever find_maximized_capital(k, w, profits, capital) returns a result r: if there exists i with 0 <= i < n and capital[i] <= w, then r = w + max{ profits[i] : 0 <= i < n and capital[i] <= w }; otherwise r = w.
  Preconditions: 1 <= k <= 100000; 0 <= w <= 10^9; n := len(profits) = len(capital); 1 <= n <= 100000; for every i with 0 <= i < n: 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9; and k = 1. -/
theorem spec_9 (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hk : k.val = 1)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r) :
    ((∃ i, i < profits.val.length ∧ (capital.val.getD i 0#i64).val ≤ w.val) →
        IsMaxOf {p : ℤ | ∃ i, i < profits.val.length ∧
          (capital.val.getD i 0#i64).val ≤ w.val ∧
            (profits.val.getD i 0#i64).val = p} (r.val - w.val)) ∧
      (¬ (∃ i, i < profits.val.length ∧ (capital.val.getD i 0#i64).val ≤ w.val) →
        r.val = w.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (k w : I64) (profits capital : Slice I64) (r : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hk : k.val = 1)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r), ((∃ i, i < profits.val.length ∧ (capital.val.getD i 0#i64).val ≤ w.val) →
        IsMaxOf {p : ℤ | ∃ i, i < profits.val.length ∧
          (capital.val.getD i 0#i64).val ≤ w.val ∧
            (profits.val.getD i 0#i64).val = p} (r.val - w.val)) ∧
      (¬ (∃ i, i < profits.val.length ∧ (capital.val.getD i 0#i64).val ≤ w.val) →
        r.val = w.val)) := by
  sorry

/-- Whenever find_maximized_capital(k, w1, profits, capital) returns a result r1 and find_maximized_capital(k, w2, profits, capital) returns a result r2, we have r1 <= r2.
  Preconditions: k, profits, capital satisfy the constraints (1 <= k <= 100000, n = len(profits) = len(capital), 1 <= n <= 100000, 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9 for all i); and w1, w2 are integers with 0 <= w1 <= w2 <= 10^9. -/
theorem spec_10 (k w1 w2 : I64) (profits capital : Slice I64) (r1 r2 : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w1.val) (hw2 : w1.val ≤ w2.val) (hw3 : w2.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres1 : Aegis.FindMaximizedCapital.find_maximized_capital k w1 profits capital = ok r1)
    (hres2 : Aegis.FindMaximizedCapital.find_maximized_capital k w2 profits capital = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (k w1 w2 : I64) (profits capital : Slice I64) (r1 r2 : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w1.val) (hw2 : w1.val ≤ w2.val) (hw3 : w2.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres1 : Aegis.FindMaximizedCapital.find_maximized_capital k w1 profits capital = ok r1)
    (hres2 : Aegis.FindMaximizedCapital.find_maximized_capital k w2 profits capital = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Whenever find_maximized_capital(k1, w, profits, capital) returns a result r1 and find_maximized_capital(k2, w, profits, capital) returns a result r2, we have r1 <= r2.
  Preconditions: w, profits, capital satisfy the constraints (0 <= w <= 10^9, n = len(profits) = len(capital), 1 <= n <= 100000, 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9 for all i); and k1, k2 are integers with 1 <= k1 <= k2 <= 100000. -/
theorem spec_11 (k1 k2 w : I64) (profits capital : Slice I64) (r1 r2 : I64)
    (hk1 : 1 ≤ k1.val) (hk2 : k1.val ≤ k2.val) (hk3 : k2.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres1 : Aegis.FindMaximizedCapital.find_maximized_capital k1 w profits capital = ok r1)
    (hres2 : Aegis.FindMaximizedCapital.find_maximized_capital k2 w profits capital = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (k1 k2 w : I64) (profits capital : Slice I64) (r1 r2 : I64)
    (hk1 : 1 ≤ k1.val) (hk2 : k1.val ≤ k2.val) (hk3 : k2.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hres1 : Aegis.FindMaximizedCapital.find_maximized_capital k1 w profits capital = ok r1)
    (hres2 : Aegis.FindMaximizedCapital.find_maximized_capital k2 w profits capital = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Whenever find_maximized_capital(k, w, profits, capital) returns a result r and find_maximized_capital(k, w, profits', capital') returns a result r', we have r = r'.
  Preconditions: k, w, profits, capital satisfy the constraints (1 <= k <= 100000, 0 <= w <= 10^9, n = len(profits) = len(capital), 1 <= n <= 100000, 0 <= profits[i] <= 10000 and 0 <= capital[i] <= 10^9 for all i); and sigma is a permutation (bijection) of {0, ..., n-1}; define profits'[i] = profits[sigma(i)] and capital'[i] = capital[sigma(i)] for 0 <= i < n (both arrays still satisfy the constraints). -/
theorem spec_12 (k w : I64) (profits capital profits' capital' : Slice I64)
    (sigma : ℕ → ℕ) (r r' : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hsigma : IsPermOf profits.val.length sigma)
    (hprofits'_def : profits'.val = permute sigma profits.val)
    (hcapital'_def : capital'.val = permute sigma capital.val)
    (hn' : profits'.val.length = capital'.val.length)
    (hn1' : 1 ≤ profits'.val.length) (hn2' : profits'.val.length ≤ 100000)
    (hprofit' : ∀ i, i < profits'.val.length →
      0 ≤ (profits'.val.getD i 0#i64).val ∧ (profits'.val.getD i 0#i64).val ≤ 10000)
    (hcapital'_bounds : ∀ i, i < capital'.val.length →
      0 ≤ (capital'.val.getD i 0#i64).val ∧ (capital'.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r)
    (hres' : Aegis.FindMaximizedCapital.find_maximized_capital k w profits' capital' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (k w : I64) (profits capital profits' capital' : Slice I64)
    (sigma : ℕ → ℕ) (r r' : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hsigma : IsPermOf profits.val.length sigma)
    (hprofits'_def : profits'.val = permute sigma profits.val)
    (hcapital'_def : capital'.val = permute sigma capital.val)
    (hn' : profits'.val.length = capital'.val.length)
    (hn1' : 1 ≤ profits'.val.length) (hn2' : profits'.val.length ≤ 100000)
    (hprofit' : ∀ i, i < profits'.val.length →
      0 ≤ (profits'.val.getD i 0#i64).val ∧ (profits'.val.getD i 0#i64).val ≤ 10000)
    (hcapital'_bounds : ∀ i, i < capital'.val.length →
      0 ≤ (capital'.val.getD i 0#i64).val ∧ (capital'.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r)
    (hres' : Aegis.FindMaximizedCapital.find_maximized_capital k w profits' capital' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever find_maximized_capital(k, w, profits, capital) returns a result r and find_maximized_capital(k, w, profits', capital) returns a result r', we have r <= r'.
  Preconditions: k, w, capital satisfy the constraints (1 <= k <= 100000, 0 <= w <= 10^9, n = len(capital), 1 <= n <= 100000, 0 <= capital[i] <= 10^9 for all i); and profits and profits' are arrays of length n with 0 <= profits[i] <= profits'[i] <= 10000 for every i. -/
theorem spec_13 (k w : I64) (capital profits profits' : Slice I64) (r r' : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn' : profits'.val.length = capital.val.length)
    (hn1 : 1 ≤ capital.val.length) (hn2 : capital.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hmono : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧
        (profits.val.getD i 0#i64).val ≤ (profits'.val.getD i 0#i64).val ∧
          (profits'.val.getD i 0#i64).val ≤ 10000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r)
    (hres' : Aegis.FindMaximizedCapital.find_maximized_capital k w profits' capital = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (k w : I64) (capital profits profits' : Slice I64) (r r' : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn' : profits'.val.length = capital.val.length)
    (hn1 : 1 ≤ capital.val.length) (hn2 : capital.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hmono : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧
        (profits.val.getD i 0#i64).val ≤ (profits'.val.getD i 0#i64).val ∧
          (profits'.val.getD i 0#i64).val ≤ 10000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r)
    (hres' : Aegis.FindMaximizedCapital.find_maximized_capital k w profits' capital = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever find_maximized_capital(k, w, profits, capital) returns a result r and find_maximized_capital(k, w, profits, capital') returns a result r', we have r >= r'.
  Preconditions: k, w, profits satisfy the constraints (1 <= k <= 100000, 0 <= w <= 10^9, n = len(profits), 1 <= n <= 100000, 0 <= profits[i] <= 10000 for all i); and capital and capital' are arrays of length n with 0 <= capital[i] <= capital'[i] <= 10^9 for every i. -/
theorem spec_14 (k w : I64) (profits capital capital' : Slice I64) (r r' : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn' : profits.val.length = capital'.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hmono : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧
        (capital.val.getD i 0#i64).val ≤ (capital'.val.getD i 0#i64).val ∧
          (capital'.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r)
    (hres' : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital' = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (k w : I64) (profits capital capital' : Slice I64) (r r' : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hw1 : 0 ≤ w.val) (hw2 : w.val ≤ 1000000000)
    (hn : profits.val.length = capital.val.length)
    (hn' : profits.val.length = capital'.val.length)
    (hn1 : 1 ≤ profits.val.length) (hn2 : profits.val.length ≤ 100000)
    (hprofit : ∀ i, i < profits.val.length →
      0 ≤ (profits.val.getD i 0#i64).val ∧ (profits.val.getD i 0#i64).val ≤ 10000)
    (hcapital : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧ (capital.val.getD i 0#i64).val ≤ 1000000000)
    (hmono : ∀ i, i < capital.val.length →
      0 ≤ (capital.val.getD i 0#i64).val ∧
        (capital.val.getD i 0#i64).val ≤ (capital'.val.getD i 0#i64).val ∧
          (capital'.val.getD i 0#i64).val ≤ 1000000000)
    (hres : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital = ok r)
    (hres' : Aegis.FindMaximizedCapital.find_maximized_capital k w profits capital' = ok r'), r'.val ≤ r.val) := by
  sorry

end AegisSpec.FindMaximizedCapital
