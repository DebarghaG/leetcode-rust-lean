import Aegis.TimeRequiredToBuy.Code.Funs

/-!
# Specifications of `Aegis.TimeRequiredToBuy.time_required_to_buy`

LeetCode problem `time-needed-to-buy-tickets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TimeRequiredToBuy

open Aeneas Aeneas.Std Result
open Aegis.TimeRequiredToBuy

def vals (tickets : Slice I64) : List Int := tickets.val.map fun x => x.val

def ticketAt (l : List Int) (i : Nat) : Int := (l[i]?).getD 0

def sumMin (l : List Int) (c : Int) : Int := (l.map fun x => min x c).sum

abbrev FifoQueue : Type := List (Nat × Int)

def fifoInitAux : Nat → List Int → FifoQueue
  | _, [] => []
  | i, c :: cs => (i, c) :: fifoInitAux (i + 1) cs

def fifoInit (l : List Int) : FifoQueue := fifoInitAux 0 l

def fifoStep : FifoQueue → FifoQueue
  | [] => []
  | (i, c) :: rest => if c ≤ 1 then rest else rest ++ [(i, c - 1)]

def fifoRun (q : FifoQueue) : Nat → FifoQueue
  | 0 => q
  | t + 1 => fifoStep (fifoRun q t)

def fifoRemaining (q : FifoQueue) (i : Nat) : Int :=
  ((q.filter fun p => p.1 = i).map fun p => p.2).sum

def ticketsBought (l : List Int) (i t : Nat) : Int :=
  fifoRemaining (fifoInit l) i - fifoRemaining (fifoRun (fifoInit l) t) i

def SameSidePerm (k : Nat) (l l' : List Int) : Prop :=
  l.length = l'.length ∧ k < l.length ∧ l[k]? = l'[k]? ∧
    (l.take k).Perm (l'.take k) ∧ (l.drop (k + 1)).Perm (l'.drop (k + 1))

/-- The function returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(tickets). Assume 1 <= n <= 100, 0 <= k < n, and for every i with 0 <= i < n, 1 <= tickets[i] <= 100. -/
theorem spec_1 (tickets : Slice I64) (k : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100) :
    ∃ r : I64, time_required_to_buy tickets k = ok r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (tickets : Slice I64) (k : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100), ∃ r : I64, time_required_to_buy tickets k = ok r) := by
  sorry

/-- The function returns a result r, and r = (sum_{i=0}^{k} min(tickets[i], tickets[k])) + (sum_{i=k+1}^{n-1} min(tickets[i], tickets[k]-1)). Empty sums are 0, and k is the 0-based starting position of the distinguished person.
  Preconditions: Let n = len(tickets). Assume 1 <= n <= 100, 0 <= k < n, and for every i with 0 <= i < n, 1 <= tickets[i] <= 100. -/
theorem spec_2 (tickets : Slice I64) (k : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100) :
    ∃ r : I64, time_required_to_buy tickets k = ok r ∧
      r.val = sumMin ((vals tickets).take (k.val.toNat + 1))
          (ticketAt (vals tickets) k.val.toNat) +
        sumMin ((vals tickets).drop (k.val.toNat + 1))
          (ticketAt (vals tickets) k.val.toNat - 1) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (tickets : Slice I64) (k : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100), ∃ r : I64, time_required_to_buy tickets k = ok r ∧
      r.val = sumMin ((vals tickets).take (k.val.toNat + 1))
          (ticketAt (vals tickets) k.val.toNat) +
        sumMin ((vals tickets).drop (k.val.toNat + 1))
          (ticketAt (vals tickets) k.val.toNat - 1)) := by
  sorry

/-- Whenever the function returns r, for every integer t with 0 <= t < r, after t seconds of the FIFO process (each second the person at the front buys one ticket and then either leaves if no tickets remain or rejoins the back) the person initially at index k has bought fewer than tickets[k] tickets.
  Preconditions: Let n = len(tickets). Assume 1 <= n <= 100, 0 <= k < n, and for every i with 0 <= i < n, 1 <= tickets[i] <= 100. -/
theorem spec_3 (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (h : time_required_to_buy tickets k = ok r) :
    ∀ t : Nat, (t : Int) < r.val →
      ticketsBought (vals tickets) k.val.toNat t < ticketAt (vals tickets) k.val.toNat := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (h : time_required_to_buy tickets k = ok r), ∀ t : Nat, (t : Int) < r.val →
      ticketsBought (vals tickets) k.val.toNat t < ticketAt (vals tickets) k.val.toNat) := by
  sorry

/-- Whenever the function returns r, r >= k + tickets[k].
  Preconditions: Let n = len(tickets). Assume 1 <= n <= 100, 0 <= k < n, and for every i with 0 <= i < n, 1 <= tickets[i] <= 100. -/
theorem spec_4 (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (h : time_required_to_buy tickets k = ok r) :
    r.val ≥ k.val + ticketAt (vals tickets) k.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (h : time_required_to_buy tickets k = ok r), r.val ≥ k.val + ticketAt (vals tickets) k.val.toNat) := by
  sorry

/-- Whenever the function returns r, r <= (k+1)*tickets[k] + (n-k-1)*(tickets[k]-1).
  Preconditions: Let n = len(tickets). Assume 1 <= n <= 100, 0 <= k < n, and for every i with 0 <= i < n, 1 <= tickets[i] <= 100. -/
theorem spec_5 (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (h : time_required_to_buy tickets k = ok r) :
    r.val ≤ (k.val + 1) * ticketAt (vals tickets) k.val.toNat +
      ((tickets.val.length : Int) - k.val - 1) *
        (ticketAt (vals tickets) k.val.toNat - 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (h : time_required_to_buy tickets k = ok r), r.val ≤ (k.val + 1) * ticketAt (vals tickets) k.val.toNat +
      ((tickets.val.length : Int) - k.val - 1) *
        (ticketAt (vals tickets) k.val.toNat - 1)) := by
  sorry

/-- Whenever the function returns r, r <= sum_{i=0}^{n-1} tickets[i].
  Preconditions: Let n = len(tickets). Assume 1 <= n <= 100, 0 <= k < n, and for every i with 0 <= i < n, 1 <= tickets[i] <= 100. -/
theorem spec_6 (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (h : time_required_to_buy tickets k = ok r) :
    r.val ≤ (vals tickets).sum := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (h : time_required_to_buy tickets k = ok r), r.val ≤ (vals tickets).sum) := by
  sorry

/-- Whenever the function returns r, r = k+1.
  Preconditions: Let n = len(tickets). Assume 1 <= n <= 100, 0 <= k < n, for every i with 0 <= i < n, 1 <= tickets[i] <= 100, and additionally tickets[k] = 1. -/
theorem spec_7 (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (htarget : ticketAt (vals tickets) k.val.toNat = 1)
    (h : time_required_to_buy tickets k = ok r) :
    r.val = k.val + 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (htarget : ticketAt (vals tickets) k.val.toNat = 1)
    (h : time_required_to_buy tickets k = ok r), r.val = k.val + 1) := by
  sorry

/-- Whenever the function returns r, r = (k+1)*tickets[k] + (n-k-1)*(tickets[k]-1).
  Preconditions: Let n = len(tickets). Assume 1 <= n <= 100, 0 <= k < n, for every i with 0 <= i < n, 1 <= tickets[i] <= 100, and additionally for every i with 0 <= i < n, tickets[i] >= tickets[k]. -/
theorem spec_8 (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (hge : ∀ i : Nat, i < tickets.val.length →
      ticketAt (vals tickets) i ≥ ticketAt (vals tickets) k.val.toNat)
    (h : time_required_to_buy tickets k = ok r) :
    r.val = (k.val + 1) * ticketAt (vals tickets) k.val.toNat +
      ((tickets.val.length : Int) - k.val - 1) *
        (ticketAt (vals tickets) k.val.toNat - 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (hge : ∀ i : Nat, i < tickets.val.length →
      ticketAt (vals tickets) i ≥ ticketAt (vals tickets) k.val.toNat)
    (h : time_required_to_buy tickets k = ok r), r.val = (k.val + 1) * ticketAt (vals tickets) k.val.toNat +
      ((tickets.val.length : Int) - k.val - 1) *
        (ticketAt (vals tickets) k.val.toNat - 1)) := by
  sorry

/-- Whenever the function returns r, r = sum_{i=0}^{n-1} tickets[i].
  Preconditions: Let n = len(tickets). Assume 1 <= n <= 100, 0 <= k < n, for every i with 0 <= i < n, 1 <= tickets[i] <= 100, and additionally for every i with 0 <= i <= k, tickets[i] <= tickets[k], and for every i with k < i < n, tickets[i] <= tickets[k]-1. -/
theorem spec_9 (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (hleft : ∀ i : Nat, i ≤ k.val.toNat → i < tickets.val.length →
      ticketAt (vals tickets) i ≤ ticketAt (vals tickets) k.val.toNat)
    (hright : ∀ i : Nat, k.val.toNat < i → i < tickets.val.length →
      ticketAt (vals tickets) i ≤ ticketAt (vals tickets) k.val.toNat - 1)
    (h : time_required_to_buy tickets k = ok r) :
    r.val = (vals tickets).sum := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (tickets : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (hleft : ∀ i : Nat, i ≤ k.val.toNat → i < tickets.val.length →
      ticketAt (vals tickets) i ≤ ticketAt (vals tickets) k.val.toNat)
    (hright : ∀ i : Nat, k.val.toNat < i → i < tickets.val.length →
      ticketAt (vals tickets) i ≤ ticketAt (vals tickets) k.val.toNat - 1)
    (h : time_required_to_buy tickets k = ok r), r.val = (vals tickets).sum) := by
  sorry

/-- For any index i with 0 <= i < n and i != k, and any integer v with tickets[i] <= v <= 100, let tickets' be tickets with tickets'[i] = v and all other entries unchanged. If either (i < k and tickets[i] >= tickets[k]) or (i > k and tickets[i] >= tickets[k]-1), then time_required_to_buy(tickets', k) = time_required_to_buy(tickets, k).
  Preconditions: Let n = len(tickets). Assume 1 <= n <= 100, 0 <= k < n, and for every i with 0 <= i < n, 1 <= tickets[i] <= 100. -/
theorem spec_10 (tickets tickets' : Slice I64) (k : I64) (i : Nat) (v : Int)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ j : Nat, j < tickets.val.length →
      1 ≤ ticketAt (vals tickets) j ∧ ticketAt (vals tickets) j ≤ 100)
    (hi : i < tickets.val.length) (hik : i ≠ k.val.toNat)
    (hv1 : ticketAt (vals tickets) i ≤ v) (hv2 : v ≤ 100)
    (hupd : vals tickets' = (vals tickets).set i v)
    (hcase : (i < k.val.toNat ∧
        ticketAt (vals tickets) i ≥ ticketAt (vals tickets) k.val.toNat) ∨
      (k.val.toNat < i ∧
        ticketAt (vals tickets) i ≥ ticketAt (vals tickets) k.val.toNat - 1)) :
    time_required_to_buy tickets' k = time_required_to_buy tickets k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (tickets tickets' : Slice I64) (k : I64) (i : Nat) (v : Int)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ j : Nat, j < tickets.val.length →
      1 ≤ ticketAt (vals tickets) j ∧ ticketAt (vals tickets) j ≤ 100)
    (hi : i < tickets.val.length) (hik : i ≠ k.val.toNat)
    (hv1 : ticketAt (vals tickets) i ≤ v) (hv2 : v ≤ 100)
    (hupd : vals tickets' = (vals tickets).set i v)
    (hcase : (i < k.val.toNat ∧
        ticketAt (vals tickets) i ≥ ticketAt (vals tickets) k.val.toNat) ∨
      (k.val.toNat < i ∧
        ticketAt (vals tickets) i ≥ ticketAt (vals tickets) k.val.toNat - 1)), time_required_to_buy tickets' k = time_required_to_buy tickets k) := by
  sorry

/-- Let tickets' be any array satisfying the same constraints and obtained from tickets by an arbitrary permutation of the entries at indices strictly less than k among themselves and/or an arbitrary permutation of the entries at indices strictly greater than k among themselves, while leaving the entry at index k unchanged. Then time_required_to_buy(tickets', k) = time_required_to_buy(tickets, k).
  Preconditions: Let n = len(tickets). Assume 1 <= n <= 100, 0 <= k < n, and for every i with 0 <= i < n, 1 <= tickets[i] <= 100. -/
theorem spec_11 (tickets tickets' : Slice I64) (k : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (hperm : SameSidePerm k.val.toNat (vals tickets) (vals tickets')) :
    time_required_to_buy tickets' k = time_required_to_buy tickets k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (tickets tickets' : Slice I64) (k : I64)
    (hlen : 1 ≤ tickets.val.length ∧ tickets.val.length ≤ 100)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (tickets.val.length : Int))
    (hbounds : ∀ i : Nat, i < tickets.val.length →
      1 ≤ ticketAt (vals tickets) i ∧ ticketAt (vals tickets) i ≤ 100)
    (hperm : SameSidePerm k.val.toNat (vals tickets) (vals tickets')), time_required_to_buy tickets' k = time_required_to_buy tickets k) := by
  sorry

/-- The function returns results r_a and r_b for inputs (a,k) and (b,k), respectively, and r_a <= r_b.
  Preconditions: Let n = len(a) = len(b). Assume 1 <= n <= 100, 0 <= k < n, for every i with 0 <= i < n, 1 <= a[i] <= 100 and 1 <= b[i] <= 100, and a[i] <= b[i] for every i with 0 <= i < n. -/
theorem spec_12 (a b : Slice I64) (k : I64)
    (hlena : 1 ≤ a.val.length ∧ a.val.length ≤ 100)
    (hlenb : b.val.length = a.val.length)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (a.val.length : Int))
    (hboundsa : ∀ i : Nat, i < a.val.length →
      1 ≤ ticketAt (vals a) i ∧ ticketAt (vals a) i ≤ 100)
    (hboundsb : ∀ i : Nat, i < b.val.length →
      1 ≤ ticketAt (vals b) i ∧ ticketAt (vals b) i ≤ 100)
    (hle : ∀ i : Nat, i < a.val.length → ticketAt (vals a) i ≤ ticketAt (vals b) i) :
    ∃ ra rb : I64, time_required_to_buy a k = ok ra ∧
      time_required_to_buy b k = ok rb ∧ ra.val ≤ rb.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (a b : Slice I64) (k : I64)
    (hlena : 1 ≤ a.val.length ∧ a.val.length ≤ 100)
    (hlenb : b.val.length = a.val.length)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (a.val.length : Int))
    (hboundsa : ∀ i : Nat, i < a.val.length →
      1 ≤ ticketAt (vals a) i ∧ ticketAt (vals a) i ≤ 100)
    (hboundsb : ∀ i : Nat, i < b.val.length →
      1 ≤ ticketAt (vals b) i ∧ ticketAt (vals b) i ≤ 100)
    (hle : ∀ i : Nat, i < a.val.length → ticketAt (vals a) i ≤ ticketAt (vals b) i), ∃ ra rb : I64, time_required_to_buy a k = ok ra ∧
      time_required_to_buy b k = ok rb ∧ ra.val ≤ rb.val) := by
  sorry

end AegisSpec.TimeRequiredToBuy
