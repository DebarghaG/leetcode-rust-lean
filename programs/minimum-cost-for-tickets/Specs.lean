import Aegis.MincostTickets.Code.Funs

/-!
# Specifications of `Aegis.MincostTickets.mincost_tickets`

LeetCode problem `minimum-cost-for-tickets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Aeneas.Std.Result
open Aegis.MincostTickets

namespace AegisSpec.MincostTickets

def i64s (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

def StrictlyIncr (l : List Int) : Prop :=
  ∀ (i : Nat) (h : i + 1 < l.length), l.get ⟨i, Nat.lt_of_succ_lt h⟩ < l.get ⟨i + 1, h⟩

def headI : List Int → Int
  | [] => 0
  | x :: _ => x

def lastI : List Int → Int
  | [] => 0
  | [x] => x
  | _ :: y :: ys => lastI (y :: ys)

def spanOf (l : List Int) : Int := lastI l - headI l + 1

def ceilDiv (a b : Int) : Int := (a + b - 1) / b

def costOf (cs : List Int) (k : Nat) : Int := cs.getD k 0

def minCost3 (cs : List Int) : Int := min (costOf cs 0) (min (costOf cs 1) (costOf cs 2))

abbrev Ticket := Int × Nat

def IsTicketType (k : Nat) : Prop := k = 0 ∨ k = 1 ∨ k = 2

def lenOf (k : Nat) : Int :=
  match k with
  | 0 => 1
  | 1 => 7
  | _ => 30

def Covers (d : Int) (k : Nat) (x : Int) : Prop := d ≤ x ∧ x ≤ d + lenOf k - 1

def ValidTicket (d : Int) (k : Nat) : Prop := IsTicketType k ∧ 1 ≤ d ∧ d ≤ 365

def Feasible (ds : List Int) (P : Multiset Ticket) : Prop :=
  (∀ t ∈ P, ValidTicket t.1 t.2) ∧ ∀ x ∈ ds, ∃ t ∈ P, Covers t.1 t.2 x

def totalCost (cs : List Int) (P : Multiset Ticket) : Int :=
  (P.map (fun t => costOf cs t.2)).sum

def IsMinTicketCost (ds cs : List Int) (v : Int) : Prop :=
  (∃ P : Multiset Ticket, Feasible ds P ∧ totalCost cs P = v) ∧
    ∀ P : Multiset Ticket, Feasible ds P → v ≤ totalCost cs P

/-- Whenever mincost_tickets(days, costs) returns a result r, r is the minimum total cost over all finite multisets P of tickets such that: each ticket has a type k in {0,1,2} and a purchase day d with 1 <= d <= 365; a type-k ticket covers exactly those travel days x for which d <= x <= d + L_k - 1, where L_0=1, L_1=7, L_2=30; and every day days[i] with 0 <= i < len(days) is covered by at least one ticket in P. The total cost of P is the sum of costs[k] over all tickets (d,k) in P.
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000. -/
theorem spec_1 (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r) :
    IsMinTicketCost (i64s days) (i64s costs) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r), IsMinTicketCost (i64s days) (i64s costs) r.val) := by
  sorry

/-- For every input satisfying the preconditions, mincost_tickets(days, costs) returns a result r; it does not fail, panic, overflow, or go out of bounds.
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000. -/
theorem spec_2 (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000) :
    ∃ r : Std.I64, mincost_tickets days costs = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000), ∃ r : Std.I64, mincost_tickets days costs = ok r) := by
  sorry

/-- Whenever mincost_tickets(days, costs) returns r, r >= min(costs[0], costs[1], costs[2]).
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000. -/
theorem spec_3 (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r) :
    minCost3 (i64s costs) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r), minCost3 (i64s costs) ≤ r.val) := by
  sorry

/-- Let n = len(days), first = days[0], last = days[n-1], span = last - first + 1, K7 = ceil(span/7), and K30 = ceil(span/30). Whenever mincost_tickets(days, costs) returns r, r <= min(n*costs[0], K7*costs[1], K30*costs[2]).
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000. -/
theorem spec_4 (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r) :
    r.val ≤ min ((days.val.length : Int) * costOf (i64s costs) 0)
      (min (ceilDiv (spanOf (i64s days)) 7 * costOf (i64s costs) 1)
        (ceilDiv (spanOf (i64s days)) 30 * costOf (i64s costs) 2)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r), r.val ≤ min ((days.val.length : Int) * costOf (i64s costs) 0)
      (min (ceilDiv (spanOf (i64s days)) 7 * costOf (i64s costs) 1)
        (ceilDiv (spanOf (i64s days)) 30 * costOf (i64s costs) 2))) := by
  sorry

/-- Whenever mincost_tickets(days, costs) returns r, r = min(len(days)*costs[0], costs[1], costs[2]).
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000; days[len(days)-1] - days[0] <= 6. -/
theorem spec_5 (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hspan : lastI (i64s days) - headI (i64s days) ≤ 6)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r) :
    r.val = min ((days.val.length : Int) * costOf (i64s costs) 0) (minCost3 (i64s costs)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hspan : lastI (i64s days) - headI (i64s days) ≤ 6)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r), r.val = min ((days.val.length : Int) * costOf (i64s costs) 0) (minCost3 (i64s costs))) := by
  sorry

/-- Whenever mincost_tickets(days, costs) returns r, r = costs[2].
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000; days[len(days)-1] - days[0] <= 29; costs[2] <= costs[0]; costs[2] <= costs[1]. -/
theorem spec_6 (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hspan : lastI (i64s days) - headI (i64s days) ≤ 29)
    (hc2_le_c0 : costOf (i64s costs) 2 ≤ costOf (i64s costs) 0)
    (hc2_le_c1 : costOf (i64s costs) 2 ≤ costOf (i64s costs) 1)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r) :
    r.val = costOf (i64s costs) 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hspan : lastI (i64s days) - headI (i64s days) ≤ 29)
    (hc2_le_c0 : costOf (i64s costs) 2 ≤ costOf (i64s costs) 0)
    (hc2_le_c1 : costOf (i64s costs) 2 ≤ costOf (i64s costs) 1)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r), r.val = costOf (i64s costs) 2) := by
  sorry

/-- If mincost_tickets(days, costs) returns r and mincost_tickets(days, costs2) returns r2, then r <= r2.
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000; costs2 is any length-3 integer array with 1 <= costs2[j] <= 1000 for j=0,1,2 and costs[j] <= costs2[j] for j=0,1,2. -/
theorem spec_7 (days costs costs2 : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hcosts2_len : costs2.val.length = 3)
    (hcosts2_range : ∀ x ∈ i64s costs2, 1 ≤ x ∧ x ≤ 1000)
    (hcosts_le : ∀ j : Nat, j < 3 → costOf (i64s costs) j ≤ costOf (i64s costs2) j)
    (r r2 : Std.I64)
    (hr : mincost_tickets days costs = ok r)
    (hr2 : mincost_tickets days costs2 = ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (days costs costs2 : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hcosts2_len : costs2.val.length = 3)
    (hcosts2_range : ∀ x ∈ i64s costs2, 1 ≤ x ∧ x ≤ 1000)
    (hcosts_le : ∀ j : Nat, j < 3 → costOf (i64s costs) j ≤ costOf (i64s costs2) j)
    (r r2 : Std.I64)
    (hr : mincost_tickets days costs = ok r)
    (hr2 : mincost_tickets days costs2 = ok r2), r.val ≤ r2.val) := by
  sorry

/-- If mincost_tickets(days, costs) returns r and mincost_tickets(days2, costs) returns r2, then r <= r2.
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000; days2 is any list with 1 <= len(days2) <= 365, all entries in 1..365, strictly increasing, and every value occurring in days also occurs in days2. -/
theorem spec_8 (days days2 costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hdays2_len : 1 ≤ days2.val.length ∧ days2.val.length ≤ 365)
    (hdays2_range : ∀ x ∈ i64s days2, 1 ≤ x ∧ x ≤ 365)
    (hdays2_incr : StrictlyIncr (i64s days2))
    (hsubset : ∀ x ∈ i64s days, x ∈ i64s days2)
    (r r2 : Std.I64)
    (hr : mincost_tickets days costs = ok r)
    (hr2 : mincost_tickets days2 costs = ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (days days2 costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hdays2_len : 1 ≤ days2.val.length ∧ days2.val.length ≤ 365)
    (hdays2_range : ∀ x ∈ i64s days2, 1 ≤ x ∧ x ≤ 365)
    (hdays2_incr : StrictlyIncr (i64s days2))
    (hsubset : ∀ x ∈ i64s days, x ∈ i64s days2)
    (r r2 : Std.I64)
    (hr : mincost_tickets days costs = ok r)
    (hr2 : mincost_tickets days2 costs = ok r2), r.val ≤ r2.val) := by
  sorry

/-- If mincost_tickets(days, costs) returns r and mincost_tickets(days2, costs) returns r2, then r = r2.
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000; days2 is any list with len(days2)=len(days), all entries in 1..365, strictly increasing, and there is an integer k with days2[i] = days[i] + k for every 0 <= i < len(days). -/
theorem spec_9 (days days2 costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hdays2_len : days2.val.length = days.val.length)
    (hdays2_range : ∀ x ∈ i64s days2, 1 ≤ x ∧ x ≤ 365)
    (hdays2_incr : StrictlyIncr (i64s days2))
    (hshift : ∃ k : Int,
      (i64s days).zip (i64s days2) = (i64s days).map (fun x => (x, x + k)))
    (r r2 : Std.I64)
    (hr : mincost_tickets days costs = ok r)
    (hr2 : mincost_tickets days2 costs = ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (days days2 costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hdays2_len : days2.val.length = days.val.length)
    (hdays2_range : ∀ x ∈ i64s days2, 1 ≤ x ∧ x ≤ 365)
    (hdays2_incr : StrictlyIncr (i64s days2))
    (hshift : ∃ k : Int,
      (i64s days).zip (i64s days2) = (i64s days).map (fun x => (x, x + k)))
    (r r2 : Std.I64)
    (hr : mincost_tickets days costs = ok r)
    (hr2 : mincost_tickets days2 costs = ok r2), r.val = r2.val) := by
  sorry

/-- If mincost_tickets(days, costs) returns r and mincost_tickets(days, costs2) returns r2, then r2 = k*r.
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000; k is a positive integer and costs2 is a length-3 integer array with costs2[j] = k*costs[j] for j=0,1,2 and 1 <= costs2[j] <= 1000 for j=0,1,2. -/
theorem spec_10 (days costs costs2 : Slice Std.I64) (k : Int)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hk_pos : 0 < k)
    (hcosts2_len : costs2.val.length = 3)
    (hcosts2_eq : ∀ j : Nat, j < 3 → costOf (i64s costs2) j = k * costOf (i64s costs) j)
    (hcosts2_range : ∀ x ∈ i64s costs2, 1 ≤ x ∧ x ≤ 1000)
    (r r2 : Std.I64)
    (hr : mincost_tickets days costs = ok r)
    (hr2 : mincost_tickets days costs2 = ok r2) :
    r2.val = k * r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (days costs costs2 : Slice Std.I64) (k : Int)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hk_pos : 0 < k)
    (hcosts2_len : costs2.val.length = 3)
    (hcosts2_eq : ∀ j : Nat, j < 3 → costOf (i64s costs2) j = k * costOf (i64s costs) j)
    (hcosts2_range : ∀ x ∈ i64s costs2, 1 ≤ x ∧ x ≤ 1000)
    (r r2 : Std.I64)
    (hr : mincost_tickets days costs = ok r)
    (hr2 : mincost_tickets days costs2 = ok r2), r2.val = k * r.val) := by
  sorry

/-- Whenever mincost_tickets(days, costs) returns r, there exists a finite multiset P of tickets such that: each ticket is (d,k) with k in {0,1,2} and d equal to some days[i]; a ticket (d,k) covers a travel day x iff d <= x <= d + L_k - 1, where L_0=1, L_1=7, L_2=30; every day days[i] is covered by some ticket in P; the sum of costs[k] over (d,k) in P is exactly r; and the number of tickets in P is at most len(days).
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000. -/
theorem spec_11 (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r) :
    ∃ P : Multiset Ticket,
      Feasible (i64s days) P ∧
        (∀ t ∈ P, t.1 ∈ i64s days) ∧
        totalCost (i64s costs) P = r.val ∧
        P.card ≤ days.val.length := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r), ∃ P : Multiset Ticket,
      Feasible (i64s days) P ∧
        (∀ t ∈ P, t.1 ∈ i64s days) ∧
        totalCost (i64s costs) P = r.val ∧
        P.card ≤ days.val.length) := by
  sorry

/-- Whenever mincost_tickets(days, costs) returns r, r = len(days)*costs[0].
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000; costs[1] >= 7*costs[0]; costs[2] >= 30*costs[0]. -/
theorem spec_12 (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hc1_ge : 7 * costOf (i64s costs) 0 ≤ costOf (i64s costs) 1)
    (hc2_ge : 30 * costOf (i64s costs) 0 ≤ costOf (i64s costs) 2)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r) :
    r.val = (days.val.length : Int) * costOf (i64s costs) 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hc1_ge : 7 * costOf (i64s costs) 0 ≤ costOf (i64s costs) 1)
    (hc2_ge : 30 * costOf (i64s costs) 0 ≤ costOf (i64s costs) 2)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r), r.val = (days.val.length : Int) * costOf (i64s costs) 0) := by
  sorry

/-- Whenever mincost_tickets(days, costs) returns r, r = len(days) * min(costs[0], costs[1], costs[2]).
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000; for every i with 0 <= i < len(days)-1, days[i+1] - days[i] >= 30. -/
theorem spec_13 (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hgaps : ∀ (i : Nat) (h : i + 1 < (i64s days).length),
      (i64s days).get ⟨i + 1, h⟩ - (i64s days).get ⟨i, Nat.lt_of_succ_lt h⟩ ≥ 30)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r) :
    r.val = (days.val.length : Int) * minCost3 (i64s costs) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (hgaps : ∀ (i : Nat) (h : i + 1 < (i64s days).length),
      (i64s days).get ⟨i + 1, h⟩ - (i64s days).get ⟨i, Nat.lt_of_succ_lt h⟩ ≥ 30)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r), r.val = (days.val.length : Int) * minCost3 (i64s costs)) := by
  sorry

/-- Whenever mincost_tickets(days, costs) returns r, r <= len(days) * min(costs[0], costs[1], costs[2]).
  Preconditions: 1 <= len(days) <= 365; for every i with 0 <= i < len(days), 1 <= days[i] <= 365; for every i with 0 <= i < len(days)-1, days[i] < days[i+1]; len(costs) = 3; for every j with 0 <= j < 3, 1 <= costs[j] <= 1000. -/
theorem spec_14 (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r) :
    r.val ≤ (days.val.length : Int) * minCost3 (i64s costs) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (days costs : Slice Std.I64)
    (hdays_len : 1 ≤ days.val.length ∧ days.val.length ≤ 365)
    (hdays_range : ∀ x ∈ i64s days, 1 ≤ x ∧ x ≤ 365)
    (hdays_incr : StrictlyIncr (i64s days))
    (hcosts_len : costs.val.length = 3)
    (hcosts_range : ∀ x ∈ i64s costs, 1 ≤ x ∧ x ≤ 1000)
    (r : Std.I64) (hr : mincost_tickets days costs = ok r), r.val ≤ (days.val.length : Int) * minCost3 (i64s costs)) := by
  sorry

end AegisSpec.MincostTickets
