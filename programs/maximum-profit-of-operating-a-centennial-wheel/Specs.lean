import Aegis.MinOperationsMaxProfit.Code.Funs

/-!
# Specifications of `Aegis.MinOperationsMaxProfit.min_operations_max_profit`

LeetCode problem `maximum-profit-of-operating-a-centennial-wheel`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperationsMaxProfit

def values (customers : Slice Std.I64) : List ℤ :=
  customers.val.map (fun c => c.val)

def EntriesWithinBounds (customers : Slice Std.I64) : Prop :=
  ∀ (i : ℕ), i < customers.val.length →
    ∀ (c : Std.I64), customers.val[i]? = some c → 0 ≤ c.val ∧ c.val ≤ 50

def totalCustomers (customers : List ℤ) : ℤ :=
  customers.sum

def rotate (w c : ℤ) : ℤ × ℤ :=
  let w' := w + c
  let b := min 4 w'
  (w' - b, b)

def rotState (customers : List ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | (k + 1) =>
      let p := rotState customers k
      let s := rotate p.1 (customers.getD k 0)
      (s.1, p.2 + s.2)

def waitingAt (customers : List ℤ) (k : ℕ) : ℤ :=
  (rotState customers k).1

def boardedNat (customers : List ℤ) (k : ℕ) : ℤ :=
  (rotState customers k).2

def boarded (customers : List ℤ) (k : ℤ) : ℤ :=
  if 0 ≤ k then boardedNat customers k.toNat else 0

def profit (customers : List ℤ) (boardingCost runningCost : ℤ) (k : ℤ) : ℤ :=
  boardingCost * boarded customers k - runningCost * k

noncomputable def firstFull (customers : List ℤ) : ℕ :=
  by
  classical
  exact if h : ∃ k : ℕ, boardedNat customers k = totalCustomers customers then
    Nat.find h
  else 0

noncomputable def maxProfit (customers : List ℤ) (boardingCost runningCost : ℤ) : ℤ :=
  by
  classical
  exact if h : ∃ k : ℕ,
      ∀ j : ℕ, profit customers boardingCost runningCost (j : ℤ) ≤
        profit customers boardingCost runningCost (k : ℤ)
    then profit customers boardingCost runningCost ((Nat.find h : ℕ) : ℤ)
    else 0

/-- Use these definitions. Let S = sum_{0<=i<n} customers[i]. For an integer k >= 0 define the k-rotation process: a counter w starts at 0; for j = 0,1,...,k-1 do: w := w + (customers[j] if j < n else 0); then b_j := min(4, w); then w := w - b_j. Let B(k) = b_0 + b_1 + ... + b_{k-1} (so B(0) = 0) and let P(k) = boardingCost * B(k) - runningCost * k. P is eventually strictly decreasing (for all k >= K with K = min{k : B(k) = S} it equals boardingCost*S - runningCost*k), so M := max_{k>=0} P(k) is attained and M >= 0 since P(0) = 0. Whenever min_operations_max_profit returns a result r, it holds that: if M > 0 then r is the least integer k >= 0 with P(k) = M; and if M = 0 then r = -1.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_1
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∃ r : Std.I64,
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r ∧
        (0 < maxProfit (values customers) boardingCost.val runningCost.val →
          profit (values customers) boardingCost.val runningCost.val r.val
              = maxProfit (values customers) boardingCost.val runningCost.val ∧
            ∀ (k : ℤ), 0 ≤ k →
              profit (values customers) boardingCost.val runningCost.val k
                  = maxProfit (values customers) boardingCost.val runningCost.val →
                r.val ≤ k) ∧
        (maxProfit (values customers) boardingCost.val runningCost.val = 0 → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∃ r : Std.I64,
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r ∧
        (0 < maxProfit (values customers) boardingCost.val runningCost.val →
          profit (values customers) boardingCost.val runningCost.val r.val
              = maxProfit (values customers) boardingCost.val runningCost.val ∧
            ∀ (k : ℤ), 0 ≤ k →
              profit (values customers) boardingCost.val runningCost.val k
                  = maxProfit (values customers) boardingCost.val runningCost.val →
                r.val ≤ k) ∧
        (maxProfit (values customers) boardingCost.val runningCost.val = 0 → r.val = -1)) := by
  sorry

/-- min_operations_max_profit returns a result (Result.ok r for some integer r); it never fails, overflows, indexes out of bounds, or panics.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_2
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∃ r : Std.I64,
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
        = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∃ r : Std.I64,
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
        = ok r) := by
  sorry

/-- Whenever min_operations_max_profit returns a result r, either r = -1 or r >= 1. In particular r is never 0 and never <= -2.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_3
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val = -1 ∨ 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val = -1 ∨ 1 ≤ r.val) := by
  sorry

/-- Let S = sum_{0<=i<n} customers[i], and let B(k) be the total boarded during the first k rotations (w=0; for j<k: w += customers[j] if j<n else 0; b_j = min(4,w); w -= b_j; B(k)=sum b_j). Let K = min{k >= 0 : B(k) = S}, the least number of rotations after which every customer has boarded. Whenever min_operations_max_profit returns r with r != -1, it holds that r <= K.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_4
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 → r.val ≤ (firstFull (values customers) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 → r.val ≤ (firstFull (values customers) : ℤ)) := by
  sorry

/-- With B(k) and P(k) = boardingCost*B(k) - runningCost*k as in the k-rotation process, whenever min_operations_max_profit returns r with r != -1, P(r) > 0. Thus the returned rotation count r is a witness that a strictly positive profit is achievable.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_5
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 →
          0 < profit (values customers) boardingCost.val runningCost.val r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 →
          0 < profit (values customers) boardingCost.val runningCost.val r.val) := by
  sorry

/-- With B(k) and P(k) = boardingCost*B(k) - runningCost*k as in the k-rotation process, whenever min_operations_max_profit returns r with r != -1, it holds that for every integer k >= 0, P(k) <= P(r). That is, the profit realized at r is the global maximum over all rotation counts.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_6
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 →
          ∀ (k : ℤ), 0 ≤ k →
            profit (values customers) boardingCost.val runningCost.val k ≤
              profit (values customers) boardingCost.val runningCost.val r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 →
          ∀ (k : ℤ), 0 ≤ k →
            profit (values customers) boardingCost.val runningCost.val k ≤
              profit (values customers) boardingCost.val runningCost.val r.val) := by
  sorry

/-- With B(k) and P(k) = boardingCost*B(k) - runningCost*k as in the k-rotation process, whenever min_operations_max_profit returns r with r != -1, it holds that for every integer k with 0 <= k < r, P(k) < P(r). That is, r is the earliest rotation count that attains its profit value.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_7
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 →
          ∀ (k : ℤ), 0 ≤ k → k < r.val →
            profit (values customers) boardingCost.val runningCost.val k <
              profit (values customers) boardingCost.val runningCost.val r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 →
          ∀ (k : ℤ), 0 ≤ k → k < r.val →
            profit (values customers) boardingCost.val runningCost.val k <
              profit (values customers) boardingCost.val runningCost.val r.val) := by
  sorry

/-- With B(k) and P(k) = boardingCost*B(k) - runningCost*k as in the k-rotation process, whenever min_operations_max_profit returns r, it holds that r = -1 if and only if for every integer k >= 0, P(k) <= 0.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_8
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        (r.val = -1 ↔
          ∀ (k : ℤ), 0 ≤ k → profit (values customers) boardingCost.val runningCost.val k ≤ 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        (r.val = -1 ↔
          ∀ (k : ℤ), 0 ≤ k → profit (values customers) boardingCost.val runningCost.val k ≤ 0)) := by
  sorry

/-- Whenever min_operations_max_profit returns r, if 4 * boardingCost <= runningCost then r = -1.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_9
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        4 * boardingCost.val ≤ runningCost.val → r.val = -1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        4 * boardingCost.val ≤ runningCost.val → r.val = -1) := by
  sorry

/-- With B(k) as in the k-rotation process, whenever min_operations_max_profit returns r with r != -1, B(r) - B(r-1) >= 1. That is, during the last performed rotation (rotation index r-1) at least one customer boards.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_10
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 →
          1 ≤ boarded (values customers) r.val - boarded (values customers) (r.val - 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 →
          1 ≤ boarded (values customers) r.val - boarded (values customers) (r.val - 1)) := by
  sorry

/-- With B(k) as in the k-rotation process, whenever min_operations_max_profit returns r with r != -1, boardingCost * (B(r) - B(r-1)) - runningCost > 0. That is, the net profit change of the last performed rotation (rotation index r-1) is strictly positive.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_11
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 →
          0 < boardingCost.val *
                (boarded (values customers) r.val - boarded (values customers) (r.val - 1)) -
              runningCost.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        r.val ≠ -1 →
          0 < boardingCost.val *
                (boarded (values customers) r.val - boarded (values customers) (r.val - 1)) -
              runningCost.val) := by
  sorry

/-- Let customers' be customers extended by m additional entries, each equal to 0. Then min_operations_max_profit(customers', boardingCost, runningCost) and min_operations_max_profit(customers, boardingCost, runningCost) agree: either both return -1, or both return the same integer r.
  Preconditions: n = len(customers); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= customers[i] <= 50; 1 <= boardingCost <= 100; 1 <= runningCost <= 100; m is an integer with m >= 1 and n + m <= 100000. -/
theorem spec_12
    (customers customers' : Slice Std.I64) (boardingCost runningCost : Std.I64) (n m : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100)
    (hm_pos : 1 ≤ m) (hnm_le : n + m ≤ 100000)
    (hvalues : values customers' = values customers ++ List.replicate m 0) :
    ∀ (r r' : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers' boardingCost runningCost
          = ok r →
        Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
            = ok r' →
          (r.val = -1 ∧ r'.val = -1) ∨ r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (customers customers' : Slice Std.I64) (boardingCost runningCost : Std.I64) (n m : ℕ)
    (hlen : customers.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hcustomers : EntriesWithinBounds customers)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100)
    (hm_pos : 1 ≤ m) (hnm_le : n + m ≤ 100000)
    (hvalues : values customers' = values customers ++ List.replicate m 0), ∀ (r r' : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers' boardingCost runningCost
          = ok r →
        Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
            = ok r' →
          (r.val = -1 ∧ r'.val = -1) ∨ r.val = r'.val) := by
  sorry

/-- Whenever min_operations_max_profit returns r: if boardingCost * customers[0] - runningCost > 0 then r = 1; otherwise (boardingCost * customers[0] - runningCost <= 0) r = -1.
  Preconditions: n = len(customers) = 1 and 1 <= customers[0] <= 4; 1 <= boardingCost <= 100; 1 <= runningCost <= 100. -/
theorem spec_13
    (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (c0 : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n) (hn_one : n = 1)
    (hc0 : customers.val = [c0])
    (hc0_lo : 1 ≤ c0.val) (hc0_hi : c0.val ≤ 4)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100) :
    ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        (0 < boardingCost.val * c0.val - runningCost.val → r.val = 1) ∧
          (boardingCost.val * c0.val - runningCost.val ≤ 0 → r.val = -1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (customers : Slice Std.I64) (boardingCost runningCost : Std.I64) (c0 : Std.I64) (n : ℕ)
    (hlen : customers.val.length = n) (hn_one : n = 1)
    (hc0 : customers.val = [c0])
    (hc0_lo : 1 ≤ c0.val) (hc0_hi : c0.val ≤ 4)
    (hboard_lo : 1 ≤ boardingCost.val) (hboard_hi : boardingCost.val ≤ 100)
    (hrun_lo : 1 ≤ runningCost.val) (hrun_hi : runningCost.val ≤ 100), ∀ (r : Std.I64),
      Aegis.MinOperationsMaxProfit.min_operations_max_profit customers boardingCost runningCost
          = ok r →
        (0 < boardingCost.val * c0.val - runningCost.val → r.val = 1) ∧
          (boardingCost.val * c0.val - runningCost.val ≤ 0 → r.val = -1)) := by
  sorry

end AegisSpec.MinOperationsMaxProfit
