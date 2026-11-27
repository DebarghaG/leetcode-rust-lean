import Aegis.MinCostSetTime.Code.Funs

/-!
# Specifications of `Aegis.MinCostSetTime.min_cost_set_time`

LeetCode problem `minimum-cost-to-set-cooking-time`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinCostSetTime

  def IsDigitSeq (P : List Int) : Prop := ∀ d ∈ P, 0 ≤ d ∧ d ≤ 9

  def padTo4 (P : List Int) : List Int := List.replicate (4 - P.length) 0 ++ P

  def padDigit (P : List Int) (i : Nat) : Int := (padTo4 P).getD i 0

  def T (P : List Int) : Int :=
    60 * (10 * padDigit P 0 + padDigit P 1) + (10 * padDigit P 2 + padDigit P 3)

  def moveCount (startAt : Int) : List Int → Nat
    | [] => 0
    | d :: rest => (if d = startAt then 0 else 1) + moveCount d rest

  def cost (startAt moveCost pushCost : Int) (P : List Int) : Int :=
    pushCost * (P.length : Int) + moveCost * (moveCount startAt P : Int)

  def ind (p : Prop) [Decidable p] : Int := if p then 1 else 0

  /-- Let P range over all finite sequences of digits with length k such that 1 <= k <= 4 and each P[i] is in {0,1,...,9}. For such P, let D be the length-4 sequence obtained by prepending 4-k zeroes to P, and define T(P) = 60*(10*D[0]+D[1]) + (10*D[2]+D[3]) and C(P) = pushCost*k + moveCost*sum_{i=0}^{k-1} delta_i, where delta_0 = 1 if P[0] != startAt and 0 otherwise, and for i>0 delta_i = 1 if P[i] != P[i-1] and 0 otherwise. Then the function returns a result r and r is the minimum of C(P) over all such P with T(P)=targetSeconds.
    Preconditions: startAt, moveCost, pushCost, targetSeconds are integers with 0 <= startAt <= 9, 1 <= moveCost <= 100000, 1 <= pushCost <= 100000, and 1 <= targetSeconds <= 6039. -/
  theorem spec_1 (startAt moveCost pushCost targetSeconds : Std.I64)
      (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
      (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
      (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
      (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039) :
      ∃ r : Std.I64,
        Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r ∧
          (∀ P : List Int, 1 ≤ P.length → P.length ≤ 4 → IsDigitSeq P →
              T P = targetSeconds.val →
              r.val ≤ cost startAt.val moveCost.val pushCost.val P) ∧
          (∃ P : List Int, 1 ≤ P.length ∧ P.length ≤ 4 ∧ IsDigitSeq P ∧
              T P = targetSeconds.val ∧
              cost startAt.val moveCost.val pushCost.val P = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (startAt moveCost pushCost targetSeconds : Std.I64)
        (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
        (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
        (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
        (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039), ∃ r : Std.I64,
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r ∧
            (∀ P : List Int, 1 ≤ P.length → P.length ≤ 4 → IsDigitSeq P →
                T P = targetSeconds.val →
                r.val ≤ cost startAt.val moveCost.val pushCost.val P) ∧
            (∃ P : List Int, 1 ≤ P.length ∧ P.length ≤ 4 ∧ IsDigitSeq P ∧
                T P = targetSeconds.val ∧
                cost startAt.val moveCost.val pushCost.val P = r.val)) := by
    sorry

  /-- For every startAt, moveCost, pushCost, targetSeconds satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or perform an out-of-bounds access.
    Preconditions: startAt, moveCost, pushCost, targetSeconds are integers with 0 <= startAt <= 9, 1 <= moveCost <= 100000, 1 <= pushCost <= 100000, and 1 <= targetSeconds <= 6039. -/
  theorem spec_2 (startAt moveCost pushCost targetSeconds : Std.I64)
      (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
      (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
      (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
      (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039) :
      ∃ r : Std.I64,
        Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (startAt moveCost pushCost targetSeconds : Std.I64)
        (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
        (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
        (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
        (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039), ∃ r : Std.I64,
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every digit sequence P with length k, 1 <= k <= 4, each P[i] in {0,1,...,9}, and T(P)=targetSeconds, where T(P) is computed by prepending 4-k zeroes to P and interpreting the first two digits as minutes and the last two as seconds, the cost C(P) = pushCost*k + moveCost*sum_{i=0}^{k-1} delta_i satisfies C(P) >= r, with delta_0 = 1 if P[0] != startAt and 0 otherwise, and for i>0 delta_i = 1 if P[i] != P[i-1] and 0 otherwise.
    Preconditions: startAt, moveCost, pushCost, targetSeconds are integers with 0 <= startAt <= 9, 1 <= moveCost <= 100000, 1 <= pushCost <= 100000, and 1 <= targetSeconds <= 6039. -/
  theorem spec_3 (startAt moveCost pushCost targetSeconds : Std.I64)
      (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
      (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
      (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
      (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039) :
      ∀ r : Std.I64,
        Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r →
          ∀ P : List Int, 1 ≤ P.length → P.length ≤ 4 → IsDigitSeq P →
            T P = targetSeconds.val → r.val ≤ cost startAt.val moveCost.val pushCost.val P := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (startAt moveCost pushCost targetSeconds : Std.I64)
        (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
        (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
        (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
        (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039), ∀ r : Std.I64,
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r →
            ∀ P : List Int, 1 ≤ P.length → P.length ≤ 4 → IsDigitSeq P →
              T P = targetSeconds.val → r.val ≤ cost startAt.val moveCost.val pushCost.val P) := by
    sorry

  /-- Whenever the function returns a result r, there exists a digit sequence P of length k with 1 <= k <= 4 and each P[i] in {0,1,...,9} such that: after prepending 4-k zeroes to P, the first two digits m and the last two digits s satisfy 60*m+s = targetSeconds; and pushCost*k + moveCost*(indicator(P[0] != startAt) + sum_{i=1}^{k-1} indicator(P[i] != P[i-1])) = r, where indicator(true)=1 and indicator(false)=0.
    Preconditions: startAt, moveCost, pushCost, targetSeconds are integers with 0 <= startAt <= 9, 1 <= moveCost <= 100000, 1 <= pushCost <= 100000, and 1 <= targetSeconds <= 6039. -/
  theorem spec_4 (startAt moveCost pushCost targetSeconds : Std.I64)
      (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
      (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
      (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
      (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039) :
      ∀ r : Std.I64,
        Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r →
          ∃ P : List Int, 1 ≤ P.length ∧ P.length ≤ 4 ∧ IsDigitSeq P ∧
            T P = targetSeconds.val ∧ cost startAt.val moveCost.val pushCost.val P = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (startAt moveCost pushCost targetSeconds : Std.I64)
        (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
        (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
        (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
        (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039), ∀ r : Std.I64,
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r →
            ∃ P : List Int, 1 ≤ P.length ∧ P.length ≤ 4 ∧ IsDigitSeq P ∧
              T P = targetSeconds.val ∧ cost startAt.val moveCost.val pushCost.val P = r.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= pushCost.
    Preconditions: startAt, moveCost, pushCost, targetSeconds are integers with 0 <= startAt <= 9, 1 <= moveCost <= 100000, 1 <= pushCost <= 100000, and 1 <= targetSeconds <= 6039. -/
  theorem spec_5 (startAt moveCost pushCost targetSeconds : Std.I64)
      (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
      (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
      (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
      (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039) :
      ∀ r : Std.I64,
        Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r →
          pushCost.val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (startAt moveCost pushCost targetSeconds : Std.I64)
        (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
        (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
        (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
        (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039), ∀ r : Std.I64,
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r →
            pushCost.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, let m = min(99, floor(targetSeconds/60)) and s = targetSeconds - 60*m. Let D0 = floor(m/10), D1 = m mod 10, D2 = floor(s/10), D3 = s mod 10. Then r <= 4*pushCost + moveCost*(indicator(D0 != startAt) + indicator(D1 != D0) + indicator(D2 != D1) + indicator(D3 != D2)), where indicator(true)=1 and indicator(false)=0.
    Preconditions: startAt, moveCost, pushCost, targetSeconds are integers with 0 <= startAt <= 9, 1 <= moveCost <= 100000, 1 <= pushCost <= 100000, and 1 <= targetSeconds <= 6039. -/
  theorem spec_6 (startAt moveCost pushCost targetSeconds : Std.I64)
      (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
      (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
      (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
      (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039) :
      ∀ r : Std.I64,
        Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r →
          (let m := min 99 (targetSeconds.val / 60)
           let s := targetSeconds.val - 60 * m
           let d0 := m / 10
           let d1 := m % 10
           let d2 := s / 10
           let d3 := s % 10
           r.val ≤ 4 * pushCost.val +
             moveCost.val *
               (ind (d0 ≠ startAt.val) + ind (d1 ≠ d0) + ind (d2 ≠ d1) + ind (d3 ≠ d2))) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (startAt moveCost pushCost targetSeconds : Std.I64)
        (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
        (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
        (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
        (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039), ∀ r : Std.I64,
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r →
            (let m := min 99 (targetSeconds.val / 60)
             let s := targetSeconds.val - 60 * m
             let d0 := m / 10
             let d1 := m % 10
             let d2 := s / 10
             let d3 := s % 10
             r.val ≤ 4 * pushCost.val +
               moveCost.val *
                 (ind (d0 ≠ startAt.val) + ind (d1 ≠ d0) + ind (d2 ≠ d1) + ind (d3 ≠ d2)))) := by
    sorry

  /-- The function returns a result r and r = pushCost + (if startAt = targetSeconds then 0 else moveCost).
    Preconditions: startAt, moveCost, pushCost, targetSeconds are integers with 0 <= startAt <= 9, 1 <= moveCost <= 100000, 1 <= pushCost <= 100000, and 1 <= targetSeconds <= 9. -/
  theorem spec_7 (startAt moveCost pushCost targetSeconds : Std.I64)
      (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
      (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
      (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
      (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 9) :
      ∃ r : Std.I64,
        Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r ∧
          r.val = pushCost.val + (if startAt.val = targetSeconds.val then 0 else moveCost.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (startAt moveCost pushCost targetSeconds : Std.I64)
        (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
        (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
        (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
        (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 9), ∃ r : Std.I64,
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r ∧
            r.val = pushCost.val + (if startAt.val = targetSeconds.val then 0 else moveCost.val)) := by
    sorry

  /-- The function returns a result r and r = 4*pushCost + (if startAt = 9 then 0 else moveCost).
    Preconditions: startAt, moveCost, pushCost are integers with 0 <= startAt <= 9, 1 <= moveCost <= 100000, 1 <= pushCost <= 100000, and targetSeconds = 6039. -/
  theorem spec_8 (startAt moveCost pushCost targetSeconds : Std.I64)
      (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
      (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
      (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
      (htarget : targetSeconds.val = 6039) :
      ∃ r : Std.I64,
        Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r ∧
          r.val = 4 * pushCost.val + (if startAt.val = 9 then 0 else moveCost.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (startAt moveCost pushCost targetSeconds : Std.I64)
        (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
        (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
        (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
        (htarget : targetSeconds.val = 6039), ∃ r : Std.I64,
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r ∧
            r.val = 4 * pushCost.val + (if startAt.val = 9 then 0 else moveCost.val)) := by
    sorry

  /-- Let r1 be the result of min_cost_set_time(startAt, moveCost1, pushCost, targetSeconds) and let r2 be the result of min_cost_set_time(startAt, moveCost2, pushCost, targetSeconds). Then both calls return results and r1 <= r2.
    Preconditions: startAt, pushCost, targetSeconds, moveCost1, moveCost2 are integers with 0 <= startAt <= 9, 1 <= pushCost <= 100000, 1 <= targetSeconds <= 6039, and 1 <= moveCost1 <= moveCost2 <= 100000. -/
  theorem spec_9 (startAt pushCost targetSeconds moveCost1 moveCost2 : Std.I64)
      (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
      (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
      (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039)
      (hmoveCost1_lo : 1 ≤ moveCost1.val) (hmoveCost1_hi : moveCost1.val ≤ moveCost2.val)
      (hmoveCost2_hi : moveCost2.val ≤ 100000) :
      ∃ r1 r2 : Std.I64,
        Aegis.MinCostSetTime.min_cost_set_time startAt moveCost1 pushCost targetSeconds = ok r1 ∧
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost2 pushCost targetSeconds = ok r2 ∧
          r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (startAt pushCost targetSeconds moveCost1 moveCost2 : Std.I64)
        (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
        (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
        (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039)
        (hmoveCost1_lo : 1 ≤ moveCost1.val) (hmoveCost1_hi : moveCost1.val ≤ moveCost2.val)
        (hmoveCost2_hi : moveCost2.val ≤ 100000), ∃ r1 r2 : Std.I64,
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost1 pushCost targetSeconds = ok r1 ∧
            Aegis.MinCostSetTime.min_cost_set_time startAt moveCost2 pushCost targetSeconds = ok r2 ∧
            r1.val ≤ r2.val) := by
    sorry

  /-- Let r1 be the result of min_cost_set_time(startAt, moveCost, pushCost1, targetSeconds) and let r2 be the result of min_cost_set_time(startAt, moveCost, pushCost2, targetSeconds). Then both calls return results and r1 <= r2.
    Preconditions: startAt, moveCost, targetSeconds, pushCost1, pushCost2 are integers with 0 <= startAt <= 9, 1 <= moveCost <= 100000, 1 <= targetSeconds <= 6039, and 1 <= pushCost1 <= pushCost2 <= 100000. -/
  theorem spec_10 (startAt moveCost targetSeconds pushCost1 pushCost2 : Std.I64)
      (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
      (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
      (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039)
      (hpushCost1_lo : 1 ≤ pushCost1.val) (hpushCost1_hi : pushCost1.val ≤ pushCost2.val)
      (hpushCost2_hi : pushCost2.val ≤ 100000) :
      ∃ r1 r2 : Std.I64,
        Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost1 targetSeconds = ok r1 ∧
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost2 targetSeconds = ok r2 ∧
          r1.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (startAt moveCost targetSeconds pushCost1 pushCost2 : Std.I64)
        (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
        (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
        (htarget_lo : 1 ≤ targetSeconds.val) (htarget_hi : targetSeconds.val ≤ 6039)
        (hpushCost1_lo : 1 ≤ pushCost1.val) (hpushCost1_hi : pushCost1.val ≤ pushCost2.val)
        (hpushCost2_hi : pushCost2.val ≤ 100000), ∃ r1 r2 : Std.I64,
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost1 targetSeconds = ok r1 ∧
            Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost2 targetSeconds = ok r2 ∧
            r1.val ≤ r2.val) := by
    sorry

  /-- The function returns a result r and r = 4*pushCost + moveCost*(2 + (if startAt = 9 then 0 else 1)).
    Preconditions: startAt, moveCost, pushCost are integers with 0 <= startAt <= 9, 1 <= moveCost <= 100000, 1 <= pushCost <= 100000, and targetSeconds = 6000. -/
  theorem spec_11 (startAt moveCost pushCost targetSeconds : Std.I64)
      (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
      (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
      (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
      (htarget : targetSeconds.val = 6000) :
      ∃ r : Std.I64,
        Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r ∧
          r.val = 4 * pushCost.val +
            moveCost.val * (2 + (if startAt.val = 9 then 0 else 1)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (startAt moveCost pushCost targetSeconds : Std.I64)
        (hstartAt_lo : 0 ≤ startAt.val) (hstartAt_hi : startAt.val ≤ 9)
        (hmoveCost_lo : 1 ≤ moveCost.val) (hmoveCost_hi : moveCost.val ≤ 100000)
        (hpushCost_lo : 1 ≤ pushCost.val) (hpushCost_hi : pushCost.val ≤ 100000)
        (htarget : targetSeconds.val = 6000), ∃ r : Std.I64,
          Aegis.MinCostSetTime.min_cost_set_time startAt moveCost pushCost targetSeconds = ok r ∧
            r.val = 4 * pushCost.val +
              moveCost.val * (2 + (if startAt.val = 9 then 0 else 1))) := by
    sorry

  end AegisSpec.MinCostSetTime
