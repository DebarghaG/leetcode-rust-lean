import Aegis.GetDescentPeriods.Code.Funs

/-!
# Specifications of `Aegis.GetDescentPeriods.get_descent_periods`

LeetCode problem `number-of-smooth-descent-periods-of-a-stock`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.GetDescentPeriods (get_descent_periods)

  namespace AegisSpec.GetDescentPeriods

  def vals (prices : Slice Std.I64) : List ℤ := prices.val.map (fun x => x.val)

  def lenOf (prices : Slice Std.I64) : ℕ := (vals prices).length

  def entry (prices : Slice Std.I64) (i : ℕ) : ℤ := (vals prices).getD i 0

  def goodEdge (prices : Slice Std.I64) (k : ℕ) : Prop :=
    entry prices k - entry prices (k + 1) = 1

  noncomputable def periodPairs (prices : Slice Std.I64) : Finset (ℕ × ℕ) := by
    classical
    exact ((Finset.range (lenOf prices)).product (Finset.range (lenOf prices))).filter
      (fun lu => lu.1 ≤ lu.2 ∧ ∀ k, lu.1 ≤ k → k < lu.2 → goodEdge prices k)

  noncomputable def periodCount (prices : Slice Std.I64) : ℕ := (periodPairs prices).card

  noncomputable def goodEdgeCount (prices : Slice Std.I64) : ℕ := by
    classical
    exact ((Finset.range (lenOf prices - 1)).filter (fun k => goodEdge prices k)).card

  def IsMaxGoodBlock (prices : Slice Std.I64) (a b : ℕ) : Prop :=
    a ≤ b ∧ b + 1 < lenOf prices ∧
      (∀ k, a ≤ k → k ≤ b → goodEdge prices k) ∧
      (a = 0 ∨ ¬ goodEdge prices (a - 1)) ∧
      (b + 2 = lenOf prices ∨ ¬ goodEdge prices (b + 1))

  noncomputable def maxGoodBlocks (prices : Slice Std.I64) : Finset (ℕ × ℕ) := by
    classical
    exact ((Finset.range (lenOf prices)).product (Finset.range (lenOf prices))).filter
      (fun ab => IsMaxGoodBlock prices ab.1 ab.2)

  noncomputable def blockTriSum (prices : Slice Std.I64) : ℕ :=
    (maxGoodBlocks prices).sum (fun ab => (ab.2 - ab.1 + 1) * (ab.2 - ab.1 + 2) / 2)

  def IsLongestRunEndingAt (prices : Slice Std.I64) (e d : ℕ) : Prop :=
    d ≤ e ∧ (∀ k, e - d ≤ k → k < e → goodEdge prices k) ∧
      (d = e ∨ ¬ goodEdge prices (e - d - 1))

  noncomputable def suffixRunCount (prices : Slice Std.I64) : ℕ := by
    classical
    exact ((Finset.range (lenOf prices)).filter
      (fun l => ∀ k, l ≤ k → k < lenOf prices - 1 → goodEdge prices k)).card

  /-- Whenever get_descent_periods(prices) returns a result res, res is the number of pairs (l,u) of integers with 0 <= l <= u < n such that for every k with l <= k < u, prices[k] - prices[k+1] = 1. This includes all one-day periods (l = u), whose condition is vacuous.
    Preconditions: Let n = len(prices). Assume 1 <= n <= 100000 and 1 <= prices[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_1 (prices : Slice Std.I64)
      (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
      (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000) :
      ∀ res, get_descent_periods prices = ok res → res.val = (periodCount prices : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
        (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000), ∀ res, get_descent_periods prices = ok res → res.val = (periodCount prices : ℤ)) := by
    sorry

  /-- get_descent_periods(prices) returns a result res; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: Let n = len(prices). Assume 1 <= n <= 100000 and 1 <= prices[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_2 (prices : Slice Std.I64)
      (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
      (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000) :
      ∃ res, get_descent_periods prices = ok res := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
        (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000), ∃ res, get_descent_periods prices = ok res) := by
    sorry

  /-- Let g be the number of indices i with 0 <= i < n-1 and prices[i] - prices[i+1] = 1. Whenever get_descent_periods(prices) returns a result res, res >= n + g.
    Preconditions: Let n = len(prices). Assume 1 <= n <= 100000 and 1 <= prices[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_3 (prices : Slice Std.I64)
      (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
      (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000) :
      ∀ res, get_descent_periods prices = ok res →
        (lenOf prices : ℤ) + (goodEdgeCount prices : ℤ) ≤ res.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
        (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000), ∀ res, get_descent_periods prices = ok res →
          (lenOf prices : ℤ) + (goodEdgeCount prices : ℤ) ≤ res.val) := by
    sorry

  /-- Whenever get_descent_periods(prices) returns a result res, res <= n*(n+1)/2.
    Preconditions: Let n = len(prices). Assume 1 <= n <= 100000 and 1 <= prices[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_4 (prices : Slice Std.I64)
      (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
      (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000) :
      ∀ res, get_descent_periods prices = ok res →
        res.val ≤ ((lenOf prices * (lenOf prices + 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
        (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000), ∀ res, get_descent_periods prices = ok res →
          res.val ≤ ((lenOf prices * (lenOf prices + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever get_descent_periods(prices) returns a result res, res = n if and only if for every i with 0 <= i < n-1, prices[i] - prices[i+1] != 1.
    Preconditions: Let n = len(prices). Assume 1 <= n <= 100000 and 1 <= prices[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_5 (prices : Slice Std.I64)
      (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
      (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000) :
      ∀ res, get_descent_periods prices = ok res →
        (res.val = (lenOf prices : ℤ) ↔ ∀ i, i < lenOf prices - 1 → ¬ goodEdge prices i) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
        (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000), ∀ res, get_descent_periods prices = ok res →
          (res.val = (lenOf prices : ℤ) ↔ ∀ i, i < lenOf prices - 1 → ¬ goodEdge prices i)) := by
    sorry

  /-- Call an index i with 0 <= i < n-1 a good edge if prices[i] - prices[i+1] = 1. Let (a_1,b_1), ..., (a_m,b_m) be all maximal intervals of consecutive good edges: each [a_j,b_j] consists only of good edges, and either a_j = 0 or a_j-1 is not good, and either b_j = n-2 or b_j+1 is not good. Let L_j = b_j - a_j + 1. Whenever get_descent_periods(prices) returns a result res, res = n + sum_{j=1}^m L_j*(L_j+1)/2.
    Preconditions: Let n = len(prices). Assume 1 <= n <= 100000 and 1 <= prices[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_6 (prices : Slice Std.I64)
      (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
      (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000) :
      ∀ res, get_descent_periods prices = ok res →
        res.val = (lenOf prices : ℤ) + (blockTriSum prices : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
        (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000), ∀ res, get_descent_periods prices = ok res →
          res.val = (lenOf prices : ℤ) + (blockTriSum prices : ℤ)) := by
    sorry

  /-- get_descent_periods(prices) returns a result res and get_descent_periods(shifted) returns a result res'; moreover res = res'.
    Preconditions: Let n = len(prices). Assume 1 <= n <= 100000 and 1 <= prices[i] <= 100000 for every i with 0 <= i < n. Let c be an integer such that 1 <= prices[i] + c <= 100000 for every i with 0 <= i < n, and let shifted be the list with shifted[i] = prices[i] + c. -/
  theorem spec_7 (prices shifted : Slice Std.I64) (c : ℤ)
      (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
      (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000)
      (hc : ∀ i, i < lenOf prices →
        1 ≤ entry prices i + c ∧ entry prices i + c ≤ 100000)
      (hshift : vals shifted = (vals prices).map (fun v => v + c)) :
      ∃ res res', get_descent_periods prices = ok res ∧
        get_descent_periods shifted = ok res' ∧ res = res' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (prices shifted : Slice Std.I64) (c : ℤ)
        (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
        (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000)
        (hc : ∀ i, i < lenOf prices →
          1 ≤ entry prices i + c ∧ entry prices i + c ≤ 100000)
        (hshift : vals shifted = (vals prices).map (fun v => v + c)), ∃ res res', get_descent_periods prices = ok res ∧
          get_descent_periods shifted = ok res' ∧ res = res') := by
    sorry

  /-- get_descent_periods(C) returns a result r_C, get_descent_periods(A) returns r_A, get_descent_periods(B) returns r_B, and r_C = r_A + r_B.
    Preconditions: Let A and B be nonempty lists of i64 with 1 <= len(A), 1 <= len(B), len(A)+len(B) <= 100000, and every element of A and B in the range 1..100000. Let C be the concatenation of A followed by B. Assume A[len(A)-1] - B[0] != 1. -/
  theorem spec_8 (A B C : Slice Std.I64)
      (hA1 : 1 ≤ lenOf A) (hB1 : 1 ≤ lenOf B)
      (hAB : lenOf A + lenOf B ≤ 100000)
      (hAv : ∀ i, i < lenOf A → 1 ≤ entry A i ∧ entry A i ≤ 100000)
      (hBv : ∀ i, i < lenOf B → 1 ≤ entry B i ∧ entry B i ≤ 100000)
      (hC : vals C = vals A ++ vals B)
      (hboundary : entry A (lenOf A - 1) - entry B 0 ≠ 1) :
      ∃ rC rA rB, get_descent_periods C = ok rC ∧ get_descent_periods A = ok rA ∧
        get_descent_periods B = ok rB ∧ rC.val = rA.val + rB.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (A B C : Slice Std.I64)
        (hA1 : 1 ≤ lenOf A) (hB1 : 1 ≤ lenOf B)
        (hAB : lenOf A + lenOf B ≤ 100000)
        (hAv : ∀ i, i < lenOf A → 1 ≤ entry A i ∧ entry A i ≤ 100000)
        (hBv : ∀ i, i < lenOf B → 1 ≤ entry B i ∧ entry B i ≤ 100000)
        (hC : vals C = vals A ++ vals B)
        (hboundary : entry A (lenOf A - 1) - entry B 0 ≠ 1), ∃ rC rA rB, get_descent_periods C = ok rC ∧ get_descent_periods A = ok rA ∧
          get_descent_periods B = ok rB ∧ rC.val = rA.val + rB.val) := by
    sorry

  /-- Let s be the number of indices l with 0 <= l < n such that for every k with l <= k < n-1, prices[k] - prices[k+1] = 1 (so s >= 1, with l = n-1 always allowed vacuously). Whenever get_descent_periods(prices) returns a result res and get_descent_periods(ext) returns a result res_ext, res_ext = res + 1 + (if prices[n-1] - x = 1 then s else 0).
    Preconditions: Let n = len(prices). Assume 1 <= n < 100000, 1 <= prices[i] <= 100000 for every i with 0 <= i < n, and let x be an integer with 1 <= x <= 100000. Let ext be the list of length n+1 with ext[i] = prices[i] for 0 <= i < n and ext[n] = x. -/
  theorem spec_9 (prices ext : Slice Std.I64) (x : ℤ)
      (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices < 100000)
      (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000)
      (hx : 1 ≤ x ∧ x ≤ 100000)
      (hext : vals ext = vals prices ++ [x]) :
      ∀ res res_ext, get_descent_periods prices = ok res →
        get_descent_periods ext = ok res_ext →
        res_ext.val = res.val + 1 +
          (if entry prices (lenOf prices - 1) - x = 1 then (suffixRunCount prices : ℤ) else 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (prices ext : Slice Std.I64) (x : ℤ)
        (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices < 100000)
        (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000)
        (hx : 1 ≤ x ∧ x ≤ 100000)
        (hext : vals ext = vals prices ++ [x]), ∀ res res_ext, get_descent_periods prices = ok res →
          get_descent_periods ext = ok res_ext →
          res_ext.val = res.val + 1 +
            (if entry prices (lenOf prices - 1) - x = 1 then (suffixRunCount prices : ℤ) else 0)) := by
    sorry

  /-- For each e with 0 <= e < n, let d_e be the largest integer d such that 0 <= d <= e and for every k with e-d <= k < e, prices[k] - prices[k+1] = 1. Whenever get_descent_periods(prices) returns a result res, res = sum_{e=0}^{n-1} (d_e + 1).
    Preconditions: Let n = len(prices). Assume 1 <= n <= 100000 and 1 <= prices[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_10 (prices : Slice Std.I64) (d : ℕ → ℕ)
      (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
      (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000)
      (hd : ∀ e, e < lenOf prices → IsLongestRunEndingAt prices e (d e)) :
      ∀ res, get_descent_periods prices = ok res →
        res.val = ∑ e ∈ Finset.range (lenOf prices), ((d e : ℤ) + 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (prices : Slice Std.I64) (d : ℕ → ℕ)
        (hn1 : 1 ≤ lenOf prices) (hn2 : lenOf prices ≤ 100000)
        (hb : ∀ i, i < lenOf prices → 1 ≤ entry prices i ∧ entry prices i ≤ 100000)
        (hd : ∀ e, e < lenOf prices → IsLongestRunEndingAt prices e (d e)), ∀ res, get_descent_periods prices = ok res →
          res.val = ∑ e ∈ Finset.range (lenOf prices), ((d e : ℤ) + 1)) := by
    sorry

  end AegisSpec.GetDescentPeriods
