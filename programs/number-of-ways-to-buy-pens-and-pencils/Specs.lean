import Aegis.WaysToBuyPensPencils.Code.Funs

/-!
# Specifications of `Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils`

LeetCode problem `number-of-ways-to-buy-pens-and-pencils`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.WaysToBuyPensPencils

def pairsWithin (total cost1 cost2 : ℤ) : Finset (ℕ × ℕ) :=
  ((Finset.range (total.toNat + 1)).product (Finset.range (total.toNat + 1))).filter
    (fun pq => (pq.1 : ℤ) * cost1 + (pq.2 : ℤ) * cost2 ≤ total)

def floorDiv (total cost1 : ℤ) : ℤ := Rat.floor ((total : ℚ) / (cost1 : ℚ))

def scaleI64 (k : ℤ) (x : Std.I64) : Std.I64 := ⟨BitVec.ofInt 64 (k * x.val)⟩

/-- The function returns a result r and r equals the number of ordered pairs (p, q) of nonnegative integers such that p*cost1 + q*cost2 <= total, where p is the number of pens and q is the number of pencils. Equivalently, r = |{(p,q) in Z_{>=0} x Z_{>=0} : p*cost1 + q*cost2 <= total}|.
  Preconditions: total, cost1, and cost2 are integers satisfying 1 <= total, cost1, cost2 <= 10^6. -/
theorem spec_1 (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6) :
    ∃ r : Std.I64,
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r ∧
        r.val = ((pairsWithin total.val cost1.val cost2.val).card : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6), ∃ r : Std.I64,
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r ∧
        r.val = ((pairsWithin total.val cost1.val cost2.val).card : ℤ)) := by
  sorry

/-- The function returns a result r; it does not fail. In particular, no arithmetic overflow, out-of-bounds access, or panic occurs.
  Preconditions: total, cost1, and cost2 are integers satisfying 1 <= total, cost1, cost2 <= 10^6. -/
theorem spec_2 (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6) :
    ∃ r : Std.I64,
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6), ∃ r : Std.I64,
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= floor(total/cost1) + floor(total/cost2) + 1, where floor(total/cost1) is the greatest integer p with p*cost1 <= total and floor(total/cost2) is the greatest integer q with q*cost2 <= total.
  Preconditions: total, cost1, and cost2 are integers satisfying 1 <= total, cost1, cost2 <= 10^6. -/
theorem spec_3 (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (r : Std.I64) :
    Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val ≥ floorDiv total.val cost1.val + floorDiv total.val cost2.val + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (r : Std.I64), Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val ≥ floorDiv total.val cost1.val + floorDiv total.val cost2.val + 1) := by
  sorry

/-- Whenever the function returns a result r, r <= (floor(total/cost1) + 1) * (floor(total/cost2) + 1).
  Preconditions: total, cost1, and cost2 are integers satisfying 1 <= total, cost1, cost2 <= 10^6. -/
theorem spec_4 (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (r : Std.I64) :
    Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val ≤ (floorDiv total.val cost1.val + 1) * (floorDiv total.val cost2.val + 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (r : Std.I64), Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val ≤ (floorDiv total.val cost1.val + 1) * (floorDiv total.val cost2.val + 1)) := by
  sorry

/-- Whenever the function returns a result r, r <= (total + 1) * (total + 2) / 2.
  Preconditions: total, cost1, and cost2 are integers satisfying 1 <= total, cost1, cost2 <= 10^6. -/
theorem spec_5 (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (r : Std.I64) :
    Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val ≤ (total.val + 1) * (total.val + 2) / 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (r : Std.I64), Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val ≤ (total.val + 1) * (total.val + 2) / 2) := by
  sorry

/-- Whenever the function returns a result r, r = floor(total/cost2) + 1, where floor(total/cost2) is the greatest integer q with q*cost2 <= total.
  Preconditions: total, cost1, and cost2 are integers satisfying 1 <= total, cost1, cost2 <= 10^6 and cost1 > total. -/
theorem spec_6 (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (hcost1_gt : cost1.val > total.val)
    (r : Std.I64) :
    Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val = floorDiv total.val cost2.val + 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (hcost1_gt : cost1.val > total.val)
    (r : Std.I64), Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val = floorDiv total.val cost2.val + 1) := by
  sorry

/-- Whenever the function returns a result r, r = floor(total/cost1) + 1, where floor(total/cost1) is the greatest integer p with p*cost1 <= total.
  Preconditions: total, cost1, and cost2 are integers satisfying 1 <= total, cost1, cost2 <= 10^6 and cost2 > total. -/
theorem spec_7 (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (hcost2_gt : cost2.val > total.val)
    (r : Std.I64) :
    Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val = floorDiv total.val cost1.val + 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (hcost2_gt : cost2.val > total.val)
    (r : Std.I64), Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val = floorDiv total.val cost1.val + 1) := by
  sorry

/-- Whenever the function returns a result r, r = (m + 1) * (m + 2) / 2.
  Preconditions: total, cost1, and cost2 are integers satisfying 1 <= total, cost1, cost2 <= 10^6 and cost1 = cost2. Let c = cost1 = cost2 and m = floor(total/c), the greatest integer s with s*c <= total. -/
theorem spec_8 (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (hcost_eq : cost1.val = cost2.val)
    (r : Std.I64) :
    Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val = (floorDiv total.val cost1.val + 1) * (floorDiv total.val cost1.val + 2) / 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (hcost_eq : cost1.val = cost2.val)
    (r : Std.I64), Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      r.val = (floorDiv total.val cost1.val + 1) * (floorDiv total.val cost1.val + 2) / 2) := by
  sorry

/-- Whenever the function returns r on (total, cost1, cost2) and returns r' on (total', cost1, cost2), we have r <= r'.
  Preconditions: total, total', cost1, and cost2 are integers satisfying 1 <= cost1, cost2 <= 10^6 and 1 <= total <= total' <= 10^6. -/
theorem spec_9 (total total' cost1 cost2 : Std.I64)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (htotal'_ub : total'.val ≤ 10 ^ 6)
    (hmono : total.val ≤ total'.val)
    (r r' : Std.I64) :
    Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total' cost1 cost2 = ok r' →
        r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (total total' cost1 cost2 : Std.I64)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (htotal'_ub : total'.val ≤ 10 ^ 6)
    (hmono : total.val ≤ total'.val)
    (r r' : Std.I64), Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total' cost1 cost2 = ok r' →
        r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns r on (total, cost1, cost2) and returns r' on (total, cost1', cost2), we have r >= r'.
  Preconditions: total, cost1, cost1', and cost2 are integers satisfying 1 <= total, cost2 <= 10^6 and 1 <= cost1 <= cost1' <= 10^6. -/
theorem spec_10 (total cost1 cost1' cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1'_ub : cost1'.val ≤ 10 ^ 6)
    (hmono : cost1.val ≤ cost1'.val)
    (r r' : Std.I64) :
    Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1' cost2 = ok r' →
        r.val ≥ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (total cost1 cost1' cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1'_ub : cost1'.val ≤ 10 ^ 6)
    (hmono : cost1.val ≤ cost1'.val)
    (r r' : Std.I64), Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1' cost2 = ok r' →
        r.val ≥ r'.val) := by
  sorry

/-- Whenever the function returns r on (total, cost1, cost2) and returns r' on (total, cost1, cost2'), we have r >= r'.
  Preconditions: total, cost1, cost2, and cost2' are integers satisfying 1 <= total, cost1 <= 10^6 and 1 <= cost2 <= cost2' <= 10^6. -/
theorem spec_11 (total cost1 cost2 cost2' : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2'_ub : cost2'.val ≤ 10 ^ 6)
    (hmono : cost2.val ≤ cost2'.val)
    (r r' : Std.I64) :
    Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2' = ok r' →
        r.val ≥ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (total cost1 cost2 cost2' : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2'_ub : cost2'.val ≤ 10 ^ 6)
    (hmono : cost2.val ≤ cost2'.val)
    (r r' : Std.I64), Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2' = ok r' →
        r.val ≥ r'.val) := by
  sorry

/-- Whenever the function returns r on (total, cost1, cost2) and returns r' on (total, cost2, cost1), we have r = r'.
  Preconditions: total, cost1, and cost2 are integers satisfying 1 <= total, cost1, cost2 <= 10^6. -/
theorem spec_12 (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (r r' : Std.I64) :
    Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost2 cost1 = ok r' →
        r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (total cost1 cost2 : Std.I64)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (r r' : Std.I64), Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost2 cost1 = ok r' →
        r.val = r'.val) := by
  sorry

/-- Whenever the function returns r on (total, cost1, cost2) and returns r' on (k*total, k*cost1, k*cost2), we have r = r'.
  Preconditions: total, cost1, cost2, and k are integers satisfying 1 <= total, cost1, cost2 <= 10^6, k >= 1, and 1 <= k*total, k*cost1, k*cost2 <= 10^6. -/
theorem spec_13 (total cost1 cost2 : Std.I64) (k : ℤ)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (hk_lb : 1 ≤ k)
    (hktotal_lb : 1 ≤ k * total.val) (hktotal_ub : k * total.val ≤ 10 ^ 6)
    (hkcost1_lb : 1 ≤ k * cost1.val) (hkcost1_ub : k * cost1.val ≤ 10 ^ 6)
    (hkcost2_lb : 1 ≤ k * cost2.val) (hkcost2_ub : k * cost2.val ≤ 10 ^ 6)
    (r r' : Std.I64) :
    Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils (scaleI64 k total) (scaleI64 k cost1)
          (scaleI64 k cost2) = ok r' →
        r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (total cost1 cost2 : Std.I64) (k : ℤ)
    (htotal_lb : 1 ≤ total.val) (htotal_ub : total.val ≤ 10 ^ 6)
    (hcost1_lb : 1 ≤ cost1.val) (hcost1_ub : cost1.val ≤ 10 ^ 6)
    (hcost2_lb : 1 ≤ cost2.val) (hcost2_ub : cost2.val ≤ 10 ^ 6)
    (hk_lb : 1 ≤ k)
    (hktotal_lb : 1 ≤ k * total.val) (hktotal_ub : k * total.val ≤ 10 ^ 6)
    (hkcost1_lb : 1 ≤ k * cost1.val) (hkcost1_ub : k * cost1.val ≤ 10 ^ 6)
    (hkcost2_lb : 1 ≤ k * cost2.val) (hkcost2_ub : k * cost2.val ≤ 10 ^ 6)
    (r r' : Std.I64), Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils total cost1 cost2 = ok r →
      Aegis.WaysToBuyPensPencils.ways_to_buy_pens_pencils (scaleI64 k total) (scaleI64 k cost1)
          (scaleI64 k cost2) = ok r' →
        r.val = r'.val) := by
  sorry

end AegisSpec.WaysToBuyPensPencils
