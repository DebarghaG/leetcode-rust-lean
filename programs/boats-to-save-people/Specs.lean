import Aegis.NumRescueBoats.Code.Funs

/-!
# Specifications of `Aegis.NumRescueBoats.num_rescue_boats`

LeetCode problem `boats-to-save-people`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NumRescueBoats
  open scoped BigOperators

  namespace AegisSpec.NumRescueBoats

  def weight (people : Slice Std.I64) (i : ℕ) : ℤ :=
    (people.val.getD i (0#i64)).val

  def totalWeight (people : Slice Std.I64) : ℤ :=
    Finset.sum (Finset.range people.length) (fun i => weight people i)

  def IsBoatPlan (people : Slice Std.I64) (limit : ℤ) (k : ℕ) : Prop :=
    ∃ blocks : Finset (Finset ℕ),
      blocks.card = k ∧
      (∀ B ∈ blocks, B ⊆ Finset.range people.length) ∧
      (∀ B ∈ blocks, B.card = 1 ∨ B.card = 2) ∧
      (∀ B ∈ blocks, Finset.sum B (fun i => weight people i) ≤ limit) ∧
      (∀ i : ℕ, i < people.length → ∃! B : Finset ℕ, B ∈ blocks ∧ i ∈ B)

  def IsLeastBoatCount (people : Slice Std.I64) (limit : ℤ) (k : ℕ) : Prop :=
    IsBoatPlan people limit k ∧ ∀ j : ℕ, IsBoatPlan people limit j → k ≤ j

  /-- The function returns a result r, and r is the least integer k >= 0 for which there exists a boat plan with k boats. A boat plan with k boats is a partition of the index set {0,...,n-1} into k nonempty blocks B_1,...,B_k such that each block has size 1 or 2 and, for every block B, sum_{i in B} people[i] <= limit. Empty boats are not counted.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. -/
  theorem spec_1 (people : Slice Std.I64) (limit : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val) :
      ∃ r : Std.I64,
        num_rescue_boats people limit = ok r ∧
          IsLeastBoatCount people limit.val r.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (people : Slice Std.I64) (limit : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val), ∃ r : Std.I64,
          num_rescue_boats people limit = ok r ∧
            IsLeastBoatCount people limit.val r.val.toNat) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or go out of bounds.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. -/
  theorem spec_2 (people : Slice Std.I64) (limit : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val) :
      ∃ r : Std.I64, num_rescue_boats people limit = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (people : Slice Std.I64) (limit : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val), ∃ r : Std.I64, num_rescue_boats people limit = ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have r >= ceil(n/2), where ceil(n/2) = (n+1) div 2.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. -/
  theorem spec_3 (people : Slice Std.I64) (limit : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
      (r : Std.I64) (hr : num_rescue_boats people limit = ok r) :
      (((people.length + 1) / 2 : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (people : Slice Std.I64) (limit : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
        (r : Std.I64) (hr : num_rescue_boats people limit = ok r), (((people.length + 1) / 2 : ℕ) : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, we have r <= n.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. -/
  theorem spec_4 (people : Slice Std.I64) (limit : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
      (r : Std.I64) (hr : num_rescue_boats people limit = ok r) :
      r.val ≤ (people.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (people : Slice Std.I64) (limit : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
        (r : Std.I64) (hr : num_rescue_boats people limit = ok r), r.val ≤ (people.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, we have r >= ceil(S/limit), where S = sum_{i=0}^{n-1} people[i] and ceil(S/limit) = (S + limit - 1) div limit.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. -/
  theorem spec_5 (people : Slice Std.I64) (limit : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
      (r : Std.I64) (hr : num_rescue_boats people limit = ok r) :
      (totalWeight people + limit.val - 1) / limit.val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (people : Slice Std.I64) (limit : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
        (r : Std.I64) (hr : num_rescue_boats people limit = ok r), (totalWeight people + limit.val - 1) / limit.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, we have r >= H, where H is the number of indices i with 0 <= i < n and 2 * people[i] > limit.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. -/
  theorem spec_6 (people : Slice Std.I64) (limit : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
      (r : Std.I64) (hr : num_rescue_boats people limit = ok r) :
      (((Finset.range people.length).filter
          (fun i => 2 * weight people i > limit.val)).card : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (people : Slice Std.I64) (limit : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
        (r : Std.I64) (hr : num_rescue_boats people limit = ok r), (((Finset.range people.length).filter
            (fun i => 2 * weight people i > limit.val)).card : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r = 1 if and only if n <= 2 and sum_{i=0}^{n-1} people[i] <= limit.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. -/
  theorem spec_7 (people : Slice Std.I64) (limit : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val) :
      ∃ r : Std.I64,
        num_rescue_boats people limit = ok r ∧
          (r.val = 1 ↔ people.length ≤ 2 ∧ totalWeight people ≤ limit.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (people : Slice Std.I64) (limit : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val), ∃ r : Std.I64,
          num_rescue_boats people limit = ok r ∧
            (r.val = 1 ↔ people.length ≤ 2 ∧ totalWeight people ≤ limit.val)) := by
    sorry

  /-- The function returns a result r, and r = n if and only if for every pair of distinct indices i,j with 0 <= i < j < n, people[i] + people[j] > limit.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. -/
  theorem spec_8 (people : Slice Std.I64) (limit : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val) :
      ∃ r : Std.I64,
        num_rescue_boats people limit = ok r ∧
          (r.val = (people.length : ℤ) ↔
            ∀ i j : ℕ, i < j → j < people.length →
              weight people i + weight people j > limit.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (people : Slice Std.I64) (limit : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val), ∃ r : Std.I64,
          num_rescue_boats people limit = ok r ∧
            (r.val = (people.length : ℤ) ↔
              ∀ i j : ℕ, i < j → j < people.length →
                weight people i + weight people j > limit.val)) := by
    sorry

  /-- Whenever the function returns a result r, we have r = ceil(n/2) = (n+1) div 2.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. Also, for every i,j with 0 <= i < j < n, people[i] + people[j] <= limit. -/
  theorem spec_9 (people : Slice Std.I64) (limit : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
      (hpairs : ∀ i j : ℕ, i < j → j < people.length →
        weight people i + weight people j ≤ limit.val)
      (r : Std.I64) (hr : num_rescue_boats people limit = ok r) :
      r.val = (((people.length + 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (people : Slice Std.I64) (limit : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
        (hpairs : ∀ i j : ℕ, i < j → j < people.length →
          weight people i + weight people j ≤ limit.val)
        (r : Std.I64) (hr : num_rescue_boats people limit = ok r), r.val = (((people.length + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r: if 2 * w <= limit, then r = ceil(n/2) = (n+1) div 2; otherwise r = n.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. Also, there exists an integer w such that for every i with 0 <= i < n, people[i] = w. -/
  theorem spec_10 (people : Slice Std.I64) (limit : Std.I64) (w : ℤ)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
      (hconst : ∀ i : ℕ, i < people.length → weight people i = w)
      (r : Std.I64) (hr : num_rescue_boats people limit = ok r) :
      (2 * w ≤ limit.val → r.val = (((people.length + 1) / 2 : ℕ) : ℤ)) ∧
        (¬ 2 * w ≤ limit.val → r.val = (people.length : ℤ)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (people : Slice Std.I64) (limit : Std.I64) (w : ℤ)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
        (hconst : ∀ i : ℕ, i < people.length → weight people i = w)
        (r : Std.I64) (hr : num_rescue_boats people limit = ok r), (2 * w ≤ limit.val → r.val = (((people.length + 1) / 2 : ℕ) : ℤ)) ∧
          (¬ 2 * w ≤ limit.val → r.val = (people.length : ℤ))) := by
    sorry

  /-- Whenever num_rescue_boats(people, limit) returns r and num_rescue_boats(people2, limit) returns r2, we have r = r2.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. Let people2 be another slice of length n such that 1 <= people2[i] <= limit for every 0 <= i < n, and the multiset of entries of people2 equals the multiset of entries of people; equivalently, there is a bijection p from {0,...,n-1} to {0,...,n-1} with people2[p(i)] = people[i] for every i. -/
  theorem spec_11 (people people2 : Slice Std.I64) (limit : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
      (hlen2 : people2.length = people.length)
      (hpeople2_pos : ∀ i : ℕ, i < people2.length → 1 ≤ weight people2 i)
      (hpeople2_le : ∀ i : ℕ, i < people2.length → weight people2 i ≤ limit.val)
      (hmultiset : (people.val.map (fun x => x.val)).Perm
        (people2.val.map (fun x => x.val)))
      (r r2 : Std.I64)
      (hr : num_rescue_boats people limit = ok r)
      (hr2 : num_rescue_boats people2 limit = ok r2) :
      r.val = r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (people people2 : Slice Std.I64) (limit : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
        (hlen2 : people2.length = people.length)
        (hpeople2_pos : ∀ i : ℕ, i < people2.length → 1 ≤ weight people2 i)
        (hpeople2_le : ∀ i : ℕ, i < people2.length → weight people2 i ≤ limit.val)
        (hmultiset : (people.val.map (fun x => x.val)).Perm
          (people2.val.map (fun x => x.val)))
        (r r2 : Std.I64)
        (hr : num_rescue_boats people limit = ok r)
        (hr2 : num_rescue_boats people2 limit = ok r2), r.val = r2.val) := by
    sorry

  /-- Whenever num_rescue_boats(people, limit1) returns r1 and num_rescue_boats(people, limit2) returns r2, we have r2 <= r1.
    Preconditions: Let n = len(people). We have 1 <= n <= 50000. Let limit1 and limit2 be integers with 1 <= limit1 <= limit2 <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit1. -/
  theorem spec_12 (people : Slice Std.I64) (limit1 limit2 : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
      (hlimit1_pos : 1 ≤ limit1.val) (hlimit_le : limit1.val ≤ limit2.val)
      (hlimit2_le : limit2.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit1.val)
      (r1 r2 : Std.I64)
      (hr1 : num_rescue_boats people limit1 = ok r1)
      (hr2 : num_rescue_boats people limit2 = ok r2) :
      r2.val ≤ r1.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (people : Slice Std.I64) (limit1 limit2 : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_le : people.length ≤ 50000)
        (hlimit1_pos : 1 ≤ limit1.val) (hlimit_le : limit1.val ≤ limit2.val)
        (hlimit2_le : limit2.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit1.val)
        (r1 r2 : Std.I64)
        (hr1 : num_rescue_boats people limit1 = ok r1)
        (hr2 : num_rescue_boats people limit2 = ok r2), r2.val ≤ r1.val) := by
    sorry

  /-- Whenever num_rescue_boats(people1, limit) returns r1 and num_rescue_boats(people2, limit) returns r2, we have r1 <= r2.
    Preconditions: Let n = len(people1) = len(people2) with 1 <= n <= 50000, and 1 <= limit <= 30000. For every i with 0 <= i < n, we have 1 <= people1[i] <= people2[i] <= limit. -/
  theorem spec_13 (people1 people2 : Slice Std.I64) (limit : Std.I64)
      (hn : people1.length = people2.length)
      (hn_pos : 1 ≤ people1.length) (hn_le : people1.length ≤ 50000)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people1.length → 1 ≤ weight people1 i)
      (hmono : ∀ i : ℕ, i < people1.length → weight people1 i ≤ weight people2 i)
      (hpeople2_le : ∀ i : ℕ, i < people1.length → weight people2 i ≤ limit.val)
      (r1 r2 : Std.I64)
      (hr1 : num_rescue_boats people1 limit = ok r1)
      (hr2 : num_rescue_boats people2 limit = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (people1 people2 : Slice Std.I64) (limit : Std.I64)
        (hn : people1.length = people2.length)
        (hn_pos : 1 ≤ people1.length) (hn_le : people1.length ≤ 50000)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people1.length → 1 ≤ weight people1 i)
        (hmono : ∀ i : ℕ, i < people1.length → weight people1 i ≤ weight people2 i)
        (hpeople2_le : ∀ i : ℕ, i < people1.length → weight people2 i ≤ limit.val)
        (r1 r2 : Std.I64)
        (hr1 : num_rescue_boats people1 limit = ok r1)
        (hr2 : num_rescue_boats people2 limit = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Whenever num_rescue_boats(people, limit) returns r and num_rescue_boats(people2, limit) returns r2, either r2 = r or r2 = r + 1.
    Preconditions: Let n = len(people) with 1 <= n <= 49999, 1 <= limit <= 30000, and for every i with 0 <= i < n, 1 <= people[i] <= limit. Let people2 be a slice of length n+1 such that people2[i] = people[i] for every 0 <= i < n and 1 <= people2[n] <= limit. -/
  theorem spec_14 (people people2 : Slice Std.I64) (limit : Std.I64)
      (hn_pos : 1 ≤ people.length) (hn_lt : people.length ≤ 49999)
      (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
      (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
      (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
      (hlen2 : people2.length = people.length + 1)
      (hagree : ∀ i : ℕ, i < people.length → weight people2 i = weight people i)
      (hlast_pos : 1 ≤ weight people2 people.length)
      (hlast_le : weight people2 people.length ≤ limit.val)
      (r r2 : Std.I64)
      (hr : num_rescue_boats people limit = ok r)
      (hr2 : num_rescue_boats people2 limit = ok r2) :
      r2.val = r.val ∨ r2.val = r.val + 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (people people2 : Slice Std.I64) (limit : Std.I64)
        (hn_pos : 1 ≤ people.length) (hn_lt : people.length ≤ 49999)
        (hlimit_pos : 1 ≤ limit.val) (hlimit_le : limit.val ≤ 30000)
        (hpeople_pos : ∀ i : ℕ, i < people.length → 1 ≤ weight people i)
        (hpeople_le : ∀ i : ℕ, i < people.length → weight people i ≤ limit.val)
        (hlen2 : people2.length = people.length + 1)
        (hagree : ∀ i : ℕ, i < people.length → weight people2 i = weight people i)
        (hlast_pos : 1 ≤ weight people2 people.length)
        (hlast_le : weight people2 people.length ≤ limit.val)
        (r r2 : Std.I64)
        (hr : num_rescue_boats people limit = ok r)
        (hr2 : num_rescue_boats people2 limit = ok r2), r2.val = r.val ∨ r2.val = r.val + 1) := by
    sorry

  end AegisSpec.NumRescueBoats
