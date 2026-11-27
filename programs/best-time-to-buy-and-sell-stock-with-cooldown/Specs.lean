import Aegis.MaxProfit.Code.Funs

/-!
# Specifications of `Aegis.MaxProfit.max_profit`

LeetCode problem `best-time-to-buy-and-sell-stock-with-cooldown`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxProfit

open Aegis.MaxProfit

def valAt (l : List I64) (i : ℕ) : ℤ := if h : i < l.length then (l.get ⟨i, h⟩).val else 0

theorem valAt_of_lt (l : List I64) (i : ℕ) (h : i < l.length) :
    valAt l i = (l.get ⟨i, h⟩).val := by
  simp [valAt, h]

theorem valAt_of_ge (l : List I64) (i : ℕ) (h : ¬ i < l.length) : valAt l i = 0 := by
  simp [valAt, h]

def CooldownOk : List (ℕ × ℕ) → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => p.2 + 2 ≤ q.1 ∧ CooldownOk (q :: rest)

def IsSchedule (n : ℕ) (ts : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ ts, p.1 < p.2 ∧ p.2 < n) ∧ CooldownOk ts

@[simp]
theorem isSchedule_nil (n : ℕ) : IsSchedule n [] := ⟨by simp, trivial⟩

def scheduleProfit (l : List I64) (ts : List (ℕ × ℕ)) : ℤ :=
  (ts.map (fun p => valAt l p.2 - valAt l p.1)).sum

@[simp]
theorem scheduleProfit_nil (l : List I64) : scheduleProfit l [] = 0 := rfl

def IsMaxScheduleProfit (l : List I64) (r : ℤ) : Prop :=
  (∀ ts, IsSchedule l.length ts → scheduleProfit l ts ≤ r) ∧
    ∃ ts, IsSchedule l.length ts ∧ scheduleProfit l ts = r

def sumPositiveDiffs (l : List I64) : ℤ :=
  ((List.range (l.length - 1)).map (fun i => max 0 (valAt l (i + 1) - valAt l i))).sum

/-- Let n = len(prices). A trading schedule is a finite sequence of transactions (b_1, s_1), ..., (b_k, s_k) for some k >= 0 such that for every j with 1 <= j <= k we have 0 <= b_j < s_j < n, and for every j with 1 <= j < k we have s_j + 2 <= b_{j+1}. The profit of such a schedule is the sum over j = 1..k of (prices[s_j] - prices[b_j]); the empty schedule (k = 0) has profit 0. The function returns a result r, and r is equal to the maximum profit over all trading schedules on prices. (The maximum exists because there are finitely many schedules, and it is at least 0 because the empty schedule is allowed.)
  Preconditions: 1 <= len(prices) <= 5000, and 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices). -/
theorem spec_1 (prices : Slice I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000) :
    ∃ r, max_profit prices = ok r ∧ IsMaxScheduleProfit prices.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (prices : Slice I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000), ∃ r, max_profit prices = ok r ∧ IsMaxScheduleProfit prices.val r.val) := by
  sorry

/-- For every prices satisfying the preconditions, the function returns a result r; it does not panic, overflow, or access an index out of bounds.
  Preconditions: 1 <= len(prices) <= 5000, and 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices). -/
theorem spec_2 (prices : Slice I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000) :
    ∃ r, max_profit prices = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (prices : Slice I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000), ∃ r, max_profit prices = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: 1 <= len(prices) <= 5000, and 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices). -/
theorem spec_3 (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hres : max_profit prices = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hres : max_profit prices = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{len(prices)-2} max(0, prices[i+1] - prices[i]).
  Preconditions: 1 <= len(prices) <= 5000, and 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices). -/
theorem spec_4 (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hres : max_profit prices = ok r) :
    r.val ≤ sumPositiveDiffs prices.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hres : max_profit prices = ok r), r.val ≤ sumPositiveDiffs prices.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite sequence of transactions (b_1, s_1), ..., (b_k, s_k) with k >= 0 such that for every j with 1 <= j <= k, 0 <= b_j < s_j < len(prices), for every j with 1 <= j < k, s_j + 2 <= b_{j+1}, and sum_{j=1}^{k} (prices[s_j] - prices[b_j]) = r.
  Preconditions: 1 <= len(prices) <= 5000, and 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices). -/
theorem spec_5 (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hres : max_profit prices = ok r) :
    ∃ ts, IsSchedule prices.val.length ts ∧ scheduleProfit prices.val ts = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hres : max_profit prices = ok r), ∃ ts, IsSchedule prices.val.length ts ∧ scheduleProfit prices.val ts = r.val) := by
  sorry

/-- Whenever the function returns a result r, r = prices[len(prices)-1] - prices[0].
  Preconditions: 1 <= len(prices) <= 5000, 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices), and prices[i] < prices[i+1] for every integer i with 0 <= i < len(prices)-1. -/
theorem spec_6 (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hincr : ∀ i, i + 1 < prices.val.length →
      valAt prices.val i < valAt prices.val (i + 1))
    (hres : max_profit prices = ok r) :
    r.val = valAt prices.val (prices.val.length - 1) - valAt prices.val 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hincr : ∀ i, i + 1 < prices.val.length →
      valAt prices.val i < valAt prices.val (i + 1))
    (hres : max_profit prices = ok r), r.val = valAt prices.val (prices.val.length - 1) - valAt prices.val 0) := by
  sorry

/-- Whenever the function returns a result r, r = max(0, prices[1] - prices[0]).
  Preconditions: 1 <= len(prices) <= 5000, 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices), and len(prices) = 2. -/
theorem spec_7 (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hlen : prices.val.length = 2)
    (hres : max_profit prices = ok r) :
    r.val = max 0 (valAt prices.val 1 - valAt prices.val 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hlen : prices.val.length = 2)
    (hres : max_profit prices = ok r), r.val = max 0 (valAt prices.val 1 - valAt prices.val 0)) := by
  sorry

/-- Whenever the function returns r on input prices and r2 on input prices2, r = r2.
  Preconditions: prices and prices2 are slices of the same length n with 1 <= n <= 5000; 0 <= prices[i] <= 1000 and 0 <= prices2[i] <= 1000 for every integer i with 0 <= i < n; and there exists an integer c such that prices2[i] = prices[i] + c for every integer i with 0 <= i < n. -/
theorem spec_8 (prices prices2 : Slice I64) (n : ℕ) (r r2 : I64)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 5000)
    (hlen : prices.val.length = n) (hlen2 : prices2.val.length = n)
    (hbound : ∀ i, i < n → 0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hbound2 : ∀ i, i < n → 0 ≤ valAt prices2.val i ∧ valAt prices2.val i ≤ 1000)
    (hshift : ∃ c : ℤ, ∀ i, i < n → valAt prices2.val i = valAt prices.val i + c)
    (hres : max_profit prices = ok r) (hres2 : max_profit prices2 = ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (prices prices2 : Slice I64) (n : ℕ) (r r2 : I64)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 5000)
    (hlen : prices.val.length = n) (hlen2 : prices2.val.length = n)
    (hbound : ∀ i, i < n → 0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hbound2 : ∀ i, i < n → 0 ≤ valAt prices2.val i ∧ valAt prices2.val i ≤ 1000)
    (hshift : ∃ c : ℤ, ∀ i, i < n → valAt prices2.val i = valAt prices.val i + c)
    (hres : max_profit prices = ok r) (hres2 : max_profit prices2 = ok r2), r.val = r2.val) := by
  sorry

/-- Whenever the function returns r on input prices and r2 on input prices2, r <= r2.
  Preconditions: prices and prices2 are slices of the same length n with 1 <= n <= 5000; 0 <= prices[i] <= 1000 and 0 <= prices2[i] <= 1000 for every integer i with 0 <= i < n; prices[i] <= prices2[i] for every integer i with 0 <= i < n; and the differences d_i = prices2[i] - prices[i] are nondecreasing, i.e. d_i <= d_{i+1} for every integer i with 0 <= i < n-1. -/
theorem spec_9 (prices prices2 : Slice I64) (n : ℕ) (r r2 : I64)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 5000)
    (hlen : prices.val.length = n) (hlen2 : prices2.val.length = n)
    (hbound : ∀ i, i < n → 0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hbound2 : ∀ i, i < n → 0 ≤ valAt prices2.val i ∧ valAt prices2.val i ≤ 1000)
    (hle : ∀ i, i < n → valAt prices.val i ≤ valAt prices2.val i)
    (hdiff : ∀ i, i + 1 < n →
      valAt prices2.val i - valAt prices.val i ≤
        valAt prices2.val (i + 1) - valAt prices.val (i + 1))
    (hres : max_profit prices = ok r) (hres2 : max_profit prices2 = ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (prices prices2 : Slice I64) (n : ℕ) (r r2 : I64)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 5000)
    (hlen : prices.val.length = n) (hlen2 : prices2.val.length = n)
    (hbound : ∀ i, i < n → 0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hbound2 : ∀ i, i < n → 0 ≤ valAt prices2.val i ∧ valAt prices2.val i ≤ 1000)
    (hle : ∀ i, i < n → valAt prices.val i ≤ valAt prices2.val i)
    (hdiff : ∀ i, i + 1 < n →
      valAt prices2.val i - valAt prices.val i ≤
        valAt prices2.val (i + 1) - valAt prices.val (i + 1))
    (hres : max_profit prices = ok r) (hres2 : max_profit prices2 = ok r2), r.val ≤ r2.val) := by
  sorry

/-- Let prefix be the slice of prices consisting of its first k entries (indices 0 through k-1). Whenever the function returns r on input prices and rk on input prefix, rk <= r.
  Preconditions: 1 <= len(prices) <= 5000, 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices), and 1 <= k <= len(prices). -/
theorem spec_10 (prices pre : Slice I64) (k : ℕ) (r rk : I64)
    (hlen1 : 1 ≤ prices.val.length) (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hk1 : 1 ≤ k) (hk2 : k ≤ prices.val.length)
    (hprefix : pre.val = prices.val.take k)
    (hres : max_profit prices = ok r) (hresk : max_profit pre = ok rk) :
    rk.val ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (prices pre : Slice I64) (k : ℕ) (r rk : I64)
    (hlen1 : 1 ≤ prices.val.length) (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hk1 : 1 ≤ k) (hk2 : k ≤ prices.val.length)
    (hprefix : pre.val = prices.val.take k)
    (hres : max_profit prices = ok r) (hresk : max_profit pre = ok rk), rk.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every pair of integers b and s with 0 <= b < s < len(prices) we have r >= prices[s] - prices[b].
  Preconditions: 1 <= len(prices) <= 5000, and 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices). -/
theorem spec_11 (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hres : max_profit prices = ok r)
    (b s : ℕ) (hbs : b < s) (hs : s < prices.val.length) :
    r.val ≥ valAt prices.val s - valAt prices.val b := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hres : max_profit prices = ok r)
    (b s : ℕ) (hbs : b < s) (hs : s < prices.val.length), r.val ≥ valAt prices.val s - valAt prices.val b) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exists an integer i with 0 <= i < len(prices)-1 and prices[i+1] > prices[i].
  Preconditions: 1 <= len(prices) <= 5000, and 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices). -/
theorem spec_12 (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hres : max_profit prices = ok r) :
    (r.val > 0 ↔ ∃ i, i + 1 < prices.val.length ∧
      valAt prices.val i < valAt prices.val (i + 1)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hres : max_profit prices = ok r), (r.val > 0 ↔ ∃ i, i + 1 < prices.val.length ∧
      valAt prices.val i < valAt prices.val (i + 1))) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: 1 <= len(prices) <= 5000, 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices), and prices[i] >= prices[i+1] for every integer i with 0 <= i < len(prices)-1. -/
theorem spec_13 (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hdecr : ∀ i, i + 1 < prices.val.length →
      valAt prices.val (i + 1) ≤ valAt prices.val i)
    (hres : max_profit prices = ok r) :
    r.val = 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hdecr : ∀ i, i + 1 < prices.val.length →
      valAt prices.val (i + 1) ≤ valAt prices.val i)
    (hres : max_profit prices = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = max(0, prices[1] - prices[0], prices[2] - prices[1], prices[2] - prices[0]).
  Preconditions: 1 <= len(prices) <= 5000, 0 <= prices[i] <= 1000 for every integer i with 0 <= i < len(prices), and len(prices) = 3. -/
theorem spec_14 (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hlen : prices.val.length = 3)
    (hres : max_profit prices = ok r) :
    r.val = max (max (max 0 (valAt prices.val 1 - valAt prices.val 0))
      (valAt prices.val 2 - valAt prices.val 1))
      (valAt prices.val 2 - valAt prices.val 0) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (prices : Slice I64) (r : I64) (hlen1 : 1 ≤ prices.val.length)
    (hlen2 : prices.val.length ≤ 5000)
    (hbound : ∀ i, i < prices.val.length →
      0 ≤ valAt prices.val i ∧ valAt prices.val i ≤ 1000)
    (hlen : prices.val.length = 3)
    (hres : max_profit prices = ok r), r.val = max (max (max 0 (valAt prices.val 1 - valAt prices.val 0))
      (valAt prices.val 2 - valAt prices.val 1))
      (valAt prices.val 2 - valAt prices.val 0)) := by
  sorry

end AegisSpec.MaxProfit
