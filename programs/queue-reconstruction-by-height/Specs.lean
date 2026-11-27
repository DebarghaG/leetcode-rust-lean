import Aegis.ReconstructQueue.Code.Funs

/-!
# Specifications of `Aegis.ReconstructQueue.reconstruct_queue`

LeetCode problem `queue-reconstruction-by-height`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.alloc.vec

namespace AegisSpec.ReconstructQueue

def heightOf (row : Vec I64) : Int :=
  match row.val with
  | h :: _ => h.val
  | [] => 0

def countOf (row : Vec I64) : Int :=
  match row.val with
  | _ :: k :: _ => k.val
  | _ => 0

def heightAt (rows : List (Vec I64)) (i : Nat) : Int :=
  match rows[i]? with
  | some row => heightOf row
  | none => 0

def countAt (rows : List (Vec I64)) (i : Nat) : Int :=
  match rows[i]? with
  | some row => countOf row
  | none => 0

def countGeBefore (rows : List (Vec I64)) (π : Nat → Nat) (j : Nat) (h : Int) : Nat :=
  ((List.range j).filter (fun i => decide (h ≤ heightAt rows (π i)))).length

def IsBijOn (n : Nat) (π : Nat → Nat) : Prop :=
  (∀ i, i < n → π i < n) ∧ ∀ i, i < n → ∃! j, j < n ∧ π j = i

def RowsLenTwo (r : Vec (Vec I64)) : Prop :=
  ∀ (j : Nat) (row : Vec I64), r.val[j]? = some row → row.val.length = 2

def IsReindexing (people : Slice (Vec I64)) (r : Vec (Vec I64)) (σ : Nat → Nat) : Prop :=
  ∀ j, j < r.val.length →
    heightAt r.val j = heightAt people.val (σ j) ∧
    countAt r.val j = countAt people.val (σ j)

def CountsOk (r : Vec (Vec I64)) : Prop :=
  ∀ j, j < r.val.length →
    (countGeBefore r.val (fun i => i) j (heightAt r.val j) : Int) = countAt r.val j

/-- reconstruct_queue(people) returns a result r (it does not fail) such that: (a) len(r) = n and for every j with 0 <= j < n, len(r[j]) = 2; (b) there is a bijection sigma : {0,...,n-1} -> {0,...,n-1} such that for every j with 0 <= j < n, r[j][0] = people[sigma(j)][0] and r[j][1] = people[sigma(j)][1]; (c) for every j with 0 <= j < n, if h = r[j][0] and k = r[j][1], then the number of indices i with 0 <= i < j and r[i][0] >= h is exactly k.
  Preconditions: Let n = len(people). Assume: 1 <= n <= 2000; for every i with 0 <= i < n, len(people[i]) = 2; writing people[i] = [h_i, k_i], 0 <= h_i <= 10^6 and 0 <= k_i < n; and there is a bijection pi : {0,...,n-1} -> {0,...,n-1} such that, setting q[j] = people[pi(j)] for 0 <= j < n, for every j the number of i with 0 <= i < j and q[i][0] >= q[j][0] equals q[j][1]. -/
theorem spec_1 (people : Slice (Vec I64))
    (hn1 : 1 ≤ people.val.length)
    (hn2 : people.val.length ≤ 2000)
    (hrow : ∀ (i : Nat) (row : Vec I64), people.val[i]? = some row → row.val.length = 2)
    (hbounds : ∀ i : Nat, i < people.val.length →
      0 ≤ heightAt people.val i ∧ heightAt people.val i ≤ 1000000 ∧
      0 ≤ countAt people.val i ∧ countAt people.val i < (people.val.length : Int))
    (hperm : ∃ π : Nat → Nat, IsBijOn people.val.length π ∧
      ∀ j, j < people.val.length →
        (countGeBefore people.val π j (heightAt people.val (π j)) : Int) =
          countAt people.val (π j)) :
    ∃ r : Vec (Vec I64),
      Aegis.ReconstructQueue.reconstruct_queue people = ok r ∧
      r.val.length = people.val.length ∧
      RowsLenTwo r ∧
      (∃ σ : Nat → Nat, IsBijOn people.val.length σ ∧ IsReindexing people r σ) ∧
      CountsOk r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (people : Slice (Vec I64))
    (hn1 : 1 ≤ people.val.length)
    (hn2 : people.val.length ≤ 2000)
    (hrow : ∀ (i : Nat) (row : Vec I64), people.val[i]? = some row → row.val.length = 2)
    (hbounds : ∀ i : Nat, i < people.val.length →
      0 ≤ heightAt people.val i ∧ heightAt people.val i ≤ 1000000 ∧
      0 ≤ countAt people.val i ∧ countAt people.val i < (people.val.length : Int))
    (hperm : ∃ π : Nat → Nat, IsBijOn people.val.length π ∧
      ∀ j, j < people.val.length →
        (countGeBefore people.val π j (heightAt people.val (π j)) : Int) =
          countAt people.val (π j)), ∃ r : Vec (Vec I64),
      Aegis.ReconstructQueue.reconstruct_queue people = ok r ∧
      r.val.length = people.val.length ∧
      RowsLenTwo r ∧
      (∃ σ : Nat → Nat, IsBijOn people.val.length σ ∧ IsReindexing people r σ) ∧
      CountsOk r) := by
  sorry

/-- reconstruct_queue(people) returns a result r; in particular it does not return an error, panic, or overflow.
  Preconditions: Let n = len(people). Assume: 1 <= n <= 2000; for every i with 0 <= i < n, len(people[i]) = 2; writing people[i] = [h_i, k_i], 0 <= h_i <= 10^6 and 0 <= k_i < n; and there is a bijection pi : {0,...,n-1} -> {0,...,n-1} such that, setting q[j] = people[pi(j)] for 0 <= j < n, for every j the number of i with 0 <= i < j and q[i][0] >= q[j][0] equals q[j][1]. -/
theorem spec_2 (people : Slice (Vec I64))
    (hn1 : 1 ≤ people.val.length)
    (hn2 : people.val.length ≤ 2000)
    (hrow : ∀ (i : Nat) (row : Vec I64), people.val[i]? = some row → row.val.length = 2)
    (hbounds : ∀ i : Nat, i < people.val.length →
      0 ≤ heightAt people.val i ∧ heightAt people.val i ≤ 1000000 ∧
      0 ≤ countAt people.val i ∧ countAt people.val i < (people.val.length : Int))
    (hperm : ∃ π : Nat → Nat, IsBijOn people.val.length π ∧
      ∀ j, j < people.val.length →
        (countGeBefore people.val π j (heightAt people.val (π j)) : Int) =
          countAt people.val (π j)) :
    ∃ r : Vec (Vec I64), Aegis.ReconstructQueue.reconstruct_queue people = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (people : Slice (Vec I64))
    (hn1 : 1 ≤ people.val.length)
    (hn2 : people.val.length ≤ 2000)
    (hrow : ∀ (i : Nat) (row : Vec I64), people.val[i]? = some row → row.val.length = 2)
    (hbounds : ∀ i : Nat, i < people.val.length →
      0 ≤ heightAt people.val i ∧ heightAt people.val i ≤ 1000000 ∧
      0 ≤ countAt people.val i ∧ countAt people.val i < (people.val.length : Int))
    (hperm : ∃ π : Nat → Nat, IsBijOn people.val.length π ∧
      ∀ j, j < people.val.length →
        (countGeBefore people.val π j (heightAt people.val (π j)) : Int) =
          countAt people.val (π j)), ∃ r : Vec (Vec I64), Aegis.ReconstructQueue.reconstruct_queue people = ok r) := by
  sorry

/-- reconstruct_queue(people) returns a result r such that len(r) = n, every r[j] for 0 <= j < n has length 2, and for every j with 0 <= j < n, 0 <= r[j][1] <= j.
  Preconditions: Let n = len(people). Assume: 1 <= n <= 2000; for every i with 0 <= i < n, len(people[i]) = 2; writing people[i] = [h_i, k_i], 0 <= h_i <= 10^6 and 0 <= k_i < n; and there is a bijection pi : {0,...,n-1} -> {0,...,n-1} such that, setting q[j] = people[pi(j)] for 0 <= j < n, for every j the number of i with 0 <= i < j and q[i][0] >= q[j][0] equals q[j][1]. -/
theorem spec_3 (people : Slice (Vec I64))
    (hn1 : 1 ≤ people.val.length)
    (hn2 : people.val.length ≤ 2000)
    (hrow : ∀ (i : Nat) (row : Vec I64), people.val[i]? = some row → row.val.length = 2)
    (hbounds : ∀ i : Nat, i < people.val.length →
      0 ≤ heightAt people.val i ∧ heightAt people.val i ≤ 1000000 ∧
      0 ≤ countAt people.val i ∧ countAt people.val i < (people.val.length : Int))
    (hperm : ∃ π : Nat → Nat, IsBijOn people.val.length π ∧
      ∀ j, j < people.val.length →
        (countGeBefore people.val π j (heightAt people.val (π j)) : Int) =
          countAt people.val (π j)) :
    ∃ r : Vec (Vec I64),
      Aegis.ReconstructQueue.reconstruct_queue people = ok r ∧
      r.val.length = people.val.length ∧
      RowsLenTwo r ∧
      (∀ j, j < people.val.length → 0 ≤ countAt r.val j ∧ countAt r.val j ≤ (j : Int)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (people : Slice (Vec I64))
    (hn1 : 1 ≤ people.val.length)
    (hn2 : people.val.length ≤ 2000)
    (hrow : ∀ (i : Nat) (row : Vec I64), people.val[i]? = some row → row.val.length = 2)
    (hbounds : ∀ i : Nat, i < people.val.length →
      0 ≤ heightAt people.val i ∧ heightAt people.val i ≤ 1000000 ∧
      0 ≤ countAt people.val i ∧ countAt people.val i < (people.val.length : Int))
    (hperm : ∃ π : Nat → Nat, IsBijOn people.val.length π ∧
      ∀ j, j < people.val.length →
        (countGeBefore people.val π j (heightAt people.val (π j)) : Int) =
          countAt people.val (π j)), ∃ r : Vec (Vec I64),
      Aegis.ReconstructQueue.reconstruct_queue people = ok r ∧
      r.val.length = people.val.length ∧
      RowsLenTwo r ∧
      (∀ j, j < people.val.length → 0 ≤ countAt r.val j ∧ countAt r.val j ≤ (j : Int))) := by
  sorry

/-- reconstruct_queue(people) returns a result r such that len(r) = n, every r[j] for 0 <= j < n has length 2, and for every i,j with 0 <= i < j < n and r[i][0] = r[j][0], we have r[i][1] < r[j][1].
  Preconditions: Let n = len(people). Assume: 1 <= n <= 2000; for every i with 0 <= i < n, len(people[i]) = 2; writing people[i] = [h_i, k_i], 0 <= h_i <= 10^6 and 0 <= k_i < n; and there is a bijection pi : {0,...,n-1} -> {0,...,n-1} such that, setting q[j] = people[pi(j)] for 0 <= j < n, for every j the number of i with 0 <= i < j and q[i][0] >= q[j][0] equals q[j][1]. -/
theorem spec_4 (people : Slice (Vec I64))
    (hn1 : 1 ≤ people.val.length)
    (hn2 : people.val.length ≤ 2000)
    (hrow : ∀ (i : Nat) (row : Vec I64), people.val[i]? = some row → row.val.length = 2)
    (hbounds : ∀ i : Nat, i < people.val.length →
      0 ≤ heightAt people.val i ∧ heightAt people.val i ≤ 1000000 ∧
      0 ≤ countAt people.val i ∧ countAt people.val i < (people.val.length : Int))
    (hperm : ∃ π : Nat → Nat, IsBijOn people.val.length π ∧
      ∀ j, j < people.val.length →
        (countGeBefore people.val π j (heightAt people.val (π j)) : Int) =
          countAt people.val (π j)) :
    ∃ r : Vec (Vec I64),
      Aegis.ReconstructQueue.reconstruct_queue people = ok r ∧
      r.val.length = people.val.length ∧
      RowsLenTwo r ∧
      (∀ i j, i < j → j < people.val.length →
        heightAt r.val i = heightAt r.val j → countAt r.val i < countAt r.val j) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (people : Slice (Vec I64))
    (hn1 : 1 ≤ people.val.length)
    (hn2 : people.val.length ≤ 2000)
    (hrow : ∀ (i : Nat) (row : Vec I64), people.val[i]? = some row → row.val.length = 2)
    (hbounds : ∀ i : Nat, i < people.val.length →
      0 ≤ heightAt people.val i ∧ heightAt people.val i ≤ 1000000 ∧
      0 ≤ countAt people.val i ∧ countAt people.val i < (people.val.length : Int))
    (hperm : ∃ π : Nat → Nat, IsBijOn people.val.length π ∧
      ∀ j, j < people.val.length →
        (countGeBefore people.val π j (heightAt people.val (π j)) : Int) =
          countAt people.val (π j)), ∃ r : Vec (Vec I64),
      Aegis.ReconstructQueue.reconstruct_queue people = ok r ∧
      r.val.length = people.val.length ∧
      RowsLenTwo r ∧
      (∀ i j, i < j → j < people.val.length →
        heightAt r.val i = heightAt r.val j → countAt r.val i < countAt r.val j)) := by
  sorry

/-- reconstruct_queue(people) returns a result r, reconstruct_queue(people') returns a result r', and r = r' (the two result vectors have the same length and the same entries at every index).
  Preconditions: Let n = len(people). Assume: 1 <= n <= 2000; for every i with 0 <= i < n, len(people[i]) = 2; writing people[i] = [h_i, k_i], 0 <= h_i <= 10^6 and 0 <= k_i < n; and there is a bijection pi : {0,...,n-1} -> {0,...,n-1} such that, setting q[j] = people[pi(j)] for 0 <= j < n, for every j the number of i with 0 <= i < j and q[i][0] >= q[j][0] equals q[j][1]. Let people' be another slice of vectors of length n such that there is a bijection tau : {0,...,n-1} -> {0,...,n-1} with people'[i] = people[tau(i)] for every i with 0 <= i < n. -/
theorem spec_5 (people people' : Slice (Vec I64))
    (hn1 : 1 ≤ people.val.length)
    (hn2 : people.val.length ≤ 2000)
    (hrow : ∀ (i : Nat) (row : Vec I64), people.val[i]? = some row → row.val.length = 2)
    (hbounds : ∀ i : Nat, i < people.val.length →
      0 ≤ heightAt people.val i ∧ heightAt people.val i ≤ 1000000 ∧
      0 ≤ countAt people.val i ∧ countAt people.val i < (people.val.length : Int))
    (hperm : ∃ π : Nat → Nat, IsBijOn people.val.length π ∧
      ∀ j, j < people.val.length →
        (countGeBefore people.val π j (heightAt people.val (π j)) : Int) =
          countAt people.val (π j))
    (h'len : people'.val.length = people.val.length)
    (hperm' : ∃ τ : Nat → Nat, IsBijOn people.val.length τ ∧
      ∀ i, i < people.val.length → people'.val[i]? = people.val[τ i]?) :
    ∃ r r' : Vec (Vec I64),
      Aegis.ReconstructQueue.reconstruct_queue people = ok r ∧
      Aegis.ReconstructQueue.reconstruct_queue people' = ok r' ∧
      r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (people people' : Slice (Vec I64))
    (hn1 : 1 ≤ people.val.length)
    (hn2 : people.val.length ≤ 2000)
    (hrow : ∀ (i : Nat) (row : Vec I64), people.val[i]? = some row → row.val.length = 2)
    (hbounds : ∀ i : Nat, i < people.val.length →
      0 ≤ heightAt people.val i ∧ heightAt people.val i ≤ 1000000 ∧
      0 ≤ countAt people.val i ∧ countAt people.val i < (people.val.length : Int))
    (hperm : ∃ π : Nat → Nat, IsBijOn people.val.length π ∧
      ∀ j, j < people.val.length →
        (countGeBefore people.val π j (heightAt people.val (π j)) : Int) =
          countAt people.val (π j))
    (h'len : people'.val.length = people.val.length)
    (hperm' : ∃ τ : Nat → Nat, IsBijOn people.val.length τ ∧
      ∀ i, i < people.val.length → people'.val[i]? = people.val[τ i]?), ∃ r r' : Vec (Vec I64),
      Aegis.ReconstructQueue.reconstruct_queue people = ok r ∧
      Aegis.ReconstructQueue.reconstruct_queue people' = ok r' ∧
      r = r') := by
  sorry

end AegisSpec.ReconstructQueue
