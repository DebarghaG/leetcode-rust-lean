import Aegis.FinalPrices.Code.Funs

/-!
# Specifications of `Aegis.FinalPrices.final_prices`

LeetCode problem `final-prices-with-a-special-discount-in-a-shop`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  namespace AegisSpec.FinalPrices

  /-- The function returns a result r such that len(r) = len(prices), and for every i with 0 <= i < len(prices): if there exists j with i < j < len(prices) and prices[j] <= prices[i], then, taking j0 to be the least such j, r[i] = prices[i] - prices[j0]; otherwise r[i] = prices[i].
    Preconditions: 1 <= len(prices) <= 500 and for every i with 0 <= i < len(prices), 1 <= prices[i] <= 1000. -/
  theorem spec_1 (prices : Slice Std.I64)
      (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
      (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.FinalPrices.final_prices prices = ok r ∧
          r.val.length = prices.val.length ∧
          ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
            ((∃ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
                (prices.val[j]).val ≤ (prices.val[i]).val) →
              ∃ (j0 : ℕ) (hj0 : i < j0) (hj0' : j0 < prices.val.length),
                (prices.val[j0]).val ≤ (prices.val[i]).val ∧
                  (∀ (k : ℕ) (hk : i < k) (hk' : k < j0),
                    (prices.val[i]).val < (prices.val[k]).val) ∧
                  (r.val[i]).val = (prices.val[i]).val - (prices.val[j0]).val) ∧
            ((∀ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
                (prices.val[i]).val < (prices.val[j]).val) →
              (r.val[i]).val = (prices.val[i]).val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
        (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.FinalPrices.final_prices prices = ok r ∧
            r.val.length = prices.val.length ∧
            ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
              ((∃ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
                  (prices.val[j]).val ≤ (prices.val[i]).val) →
                ∃ (j0 : ℕ) (hj0 : i < j0) (hj0' : j0 < prices.val.length),
                  (prices.val[j0]).val ≤ (prices.val[i]).val ∧
                    (∀ (k : ℕ) (hk : i < k) (hk' : k < j0),
                      (prices.val[i]).val < (prices.val[k]).val) ∧
                    (r.val[i]).val = (prices.val[i]).val - (prices.val[j0]).val) ∧
              ((∀ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
                  (prices.val[i]).val < (prices.val[j]).val) →
                (r.val[i]).val = (prices.val[i]).val)) := by
    sorry

  /-- For every prices satisfying the preconditions, the function returns a result r; it does not fail, overflow, or panic.
    Preconditions: 1 <= len(prices) <= 500 and for every i with 0 <= i < len(prices), 1 <= prices[i] <= 1000. -/
  theorem spec_2 (prices : Slice Std.I64)
      (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
      (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.FinalPrices.final_prices prices = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
        (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000), ∃ r : alloc.vec.Vec Std.I64, Aegis.FinalPrices.final_prices prices = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(prices).
    Preconditions: 1 <= len(prices) <= 500 and for every i with 0 <= i < len(prices), 1 <= prices[i] <= 1000. -/
  theorem spec_3 (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
      (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
      (hr : Aegis.FinalPrices.final_prices prices = ok r) :
      r.val.length = prices.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
        (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
        (hr : Aegis.FinalPrices.final_prices prices = ok r), r.val.length = prices.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(prices), 0 <= r[i] and r[i] <= prices[i].
    Preconditions: 1 <= len(prices) <= 500 and for every i with 0 <= i < len(prices), 1 <= prices[i] <= 1000. -/
  theorem spec_4 (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
      (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
      (hr : Aegis.FinalPrices.final_prices prices = ok r) :
      ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
        0 ≤ (r.val[i]).val ∧ (r.val[i]).val ≤ (prices.val[i]).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
        (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
        (hr : Aegis.FinalPrices.final_prices prices = ok r), ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
          0 ≤ (r.val[i]).val ∧ (r.val[i]).val ≤ (prices.val[i]).val) := by
    sorry

  /-- Whenever the function returns a result r, r[len(prices)-1] = prices[len(prices)-1].
    Preconditions: 1 <= len(prices) <= 500 and for every i with 0 <= i < len(prices), 1 <= prices[i] <= 1000. -/
  theorem spec_5 (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
      (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
      (hr : Aegis.FinalPrices.final_prices prices = ok r) :
      ∀ (i : ℕ) (hi : i = prices.val.length - 1) (hi' : i < r.val.length),
        (r.val[i]).val = (prices.val[i]).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
        (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
        (hr : Aegis.FinalPrices.final_prices prices = ok r), ∀ (i : ℕ) (hi : i = prices.val.length - 1) (hi' : i < r.val.length),
          (r.val[i]).val = (prices.val[i]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(prices), if for every j with i < j < len(prices) we have prices[j] > prices[i], then r[i] = prices[i].
    Preconditions: 1 <= len(prices) <= 500 and for every i with 0 <= i < len(prices), 1 <= prices[i] <= 1000. -/
  theorem spec_6 (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
      (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
      (hr : Aegis.FinalPrices.final_prices prices = ok r) :
      ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
        (∀ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
          (prices.val[i]).val < (prices.val[j]).val) →
          (r.val[i]).val = (prices.val[i]).val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
        (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
        (hr : Aegis.FinalPrices.final_prices prices = ok r), ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
          (∀ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
            (prices.val[i]).val < (prices.val[j]).val) →
            (r.val[i]).val = (prices.val[i]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(prices), if there exists j with i < j < len(prices) and prices[j] <= prices[i], then r[i] < prices[i].
    Preconditions: 1 <= len(prices) <= 500 and for every i with 0 <= i < len(prices), 1 <= prices[i] <= 1000. -/
  theorem spec_7 (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
      (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
      (hr : Aegis.FinalPrices.final_prices prices = ok r) :
      ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
        (∃ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
          (prices.val[j]).val ≤ (prices.val[i]).val) →
          (r.val[i]).val < (prices.val[i]).val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
        (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
        (hr : Aegis.FinalPrices.final_prices prices = ok r), ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
          (∃ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
            (prices.val[j]).val ≤ (prices.val[i]).val) →
            (r.val[i]).val < (prices.val[i]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(prices), if prices[j] <= prices[i] and for every k with i < k < j we have prices[k] > prices[i], then r[i] = prices[i] - prices[j].
    Preconditions: 1 <= len(prices) <= 500 and for every i with 0 <= i < len(prices), 1 <= prices[i] <= 1000. -/
  theorem spec_8 (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
      (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
      (hr : Aegis.FinalPrices.final_prices prices = ok r) :
      ∀ (i j : ℕ) (hi : i < prices.val.length) (hj : i < j)
        (hj' : j < prices.val.length) (hi' : i < r.val.length),
        (prices.val[j]).val ≤ (prices.val[i]).val →
          (∀ (k : ℕ) (hk : i < k) (hk' : k < j), (prices.val[i]).val < (prices.val[k]).val) →
            (r.val[i]).val = (prices.val[i]).val - (prices.val[j]).val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
        (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
        (hr : Aegis.FinalPrices.final_prices prices = ok r), ∀ (i j : ℕ) (hi : i < prices.val.length) (hj : i < j)
          (hj' : j < prices.val.length) (hi' : i < r.val.length),
          (prices.val[j]).val ≤ (prices.val[i]).val →
            (∀ (k : ℕ) (hk : i < k) (hk' : k < j), (prices.val[i]).val < (prices.val[k]).val) →
              (r.val[i]).val = (prices.val[i]).val - (prices.val[j]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(prices), either r[i] = prices[i], or there exists j with i < j < len(prices) such that prices[j] <= prices[i] and r[i] = prices[i] - prices[j].
    Preconditions: 1 <= len(prices) <= 500 and for every i with 0 <= i < len(prices), 1 <= prices[i] <= 1000. -/
  theorem spec_9 (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
      (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
      (hr : Aegis.FinalPrices.final_prices prices = ok r) :
      ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
        (r.val[i]).val = (prices.val[i]).val ∨
          ∃ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
            (prices.val[j]).val ≤ (prices.val[i]).val ∧
              (r.val[i]).val = (prices.val[i]).val - (prices.val[j]).val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
        (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
        (hr : Aegis.FinalPrices.final_prices prices = ok r), ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
          (r.val[i]).val = (prices.val[i]).val ∨
            ∃ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
              (prices.val[j]).val ≤ (prices.val[i]).val ∧
                (r.val[i]).val = (prices.val[i]).val - (prices.val[j]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(prices), if r[i] = prices[i], then for every j with i < j < len(prices) we have prices[j] > prices[i].
    Preconditions: 1 <= len(prices) <= 500 and for every i with 0 <= i < len(prices), 1 <= prices[i] <= 1000. -/
  theorem spec_10 (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
      (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
      (hr : Aegis.FinalPrices.final_prices prices = ok r) :
      ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
        (r.val[i]).val = (prices.val[i]).val →
          ∀ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
            (prices.val[i]).val < (prices.val[j]).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (prices : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
        (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
        (hr : Aegis.FinalPrices.final_prices prices = ok r), ∀ (i : ℕ) (hi : i < prices.val.length) (hi' : i < r.val.length),
          (r.val[i]).val = (prices.val[i]).val →
            ∀ (j : ℕ) (hj : i < j) (hj' : j < prices.val.length),
              (prices.val[i]).val < (prices.val[j]).val) := by
    sorry

  /-- Let prices' be the array with len(prices') = len(prices) and prices'[i] = c * prices[i] for every i with 0 <= i < len(prices). If r is the result returned for prices and r' is the result returned for prices', then len(r') = len(r) and for every i with 0 <= i < len(prices), r'[i] = c * r[i].
    Preconditions: 1 <= len(prices) <= 500; for every i with 0 <= i < len(prices), 1 <= prices[i] <= 1000; c is a positive integer and for every i with 0 <= i < len(prices), c * prices[i] <= 1000. -/
  theorem spec_11 (prices prices' : Slice Std.I64) (c : ℕ)
      (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
      (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
      (hc_pos : 0 < c)
      (hc_bound : ∀ (i : ℕ) (hi : i < prices.val.length),
        (c : ℤ) * (prices.val[i]).val ≤ 1000)
      (h_len : prices'.val.length = prices.val.length)
      (h_entries' : ∀ (i : ℕ) (hi : i < prices.val.length),
        (prices'.val[i]).val = (c : ℤ) * (prices.val[i]).val)
      (r r' : alloc.vec.Vec Std.I64) (hr : Aegis.FinalPrices.final_prices prices = ok r)
      (hr' : Aegis.FinalPrices.final_prices prices' = ok r') :
      r'.val.length = r.val.length ∧
        ∀ (i : ℕ) (hi : i < prices.val.length) (hiR : i < r.val.length)
          (hiR' : i < r'.val.length),
          (r'.val[i]).val = (c : ℤ) * (r.val[i]).val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (prices prices' : Slice Std.I64) (c : ℕ)
        (h_len_ge : 1 ≤ prices.val.length) (h_len_le : prices.val.length ≤ 500)
        (h_entries : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000)
        (hc_pos : 0 < c)
        (hc_bound : ∀ (i : ℕ) (hi : i < prices.val.length),
          (c : ℤ) * (prices.val[i]).val ≤ 1000)
        (h_len : prices'.val.length = prices.val.length)
        (h_entries' : ∀ (i : ℕ) (hi : i < prices.val.length),
          (prices'.val[i]).val = (c : ℤ) * (prices.val[i]).val)
        (r r' : alloc.vec.Vec Std.I64) (hr : Aegis.FinalPrices.final_prices prices = ok r)
        (hr' : Aegis.FinalPrices.final_prices prices' = ok r'), r'.val.length = r.val.length ∧
          ∀ (i : ℕ) (hi : i < prices.val.length) (hiR : i < r.val.length)
            (hiR' : i < r'.val.length),
            (r'.val[i]).val = (c : ℤ) * (r.val[i]).val) := by
    sorry

  end AegisSpec.FinalPrices
