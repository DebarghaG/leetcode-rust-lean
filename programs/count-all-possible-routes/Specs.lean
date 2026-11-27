import Aegis.CountRoutes.Code.Funs

/-!
# Specifications of `Aegis.CountRoutes.count_routes`

LeetCode problem `count-all-possible-routes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountRoutes

  section

  def locAt (locs : List Std.I64) (i : Nat) : Int :=
    match locs[i]? with
    | some x => x.val
    | none => 0

  def locDist (locs : List Std.I64) (i j : Nat) : Nat := (locAt locs i - locAt locs j).natAbs

  def pathCost (locs : List Std.I64) : List Nat → Nat
    | [] => 0
    | [_] => 0
    | a :: b :: rest => locDist locs a b + pathCost locs (b :: rest)

  def AdjacentNe : List Nat → Prop
    | [] => True
    | [_] => True
    | a :: b :: rest => a ≠ b ∧ AdjacentNe (b :: rest)

  instance instDecidableAdjacentNe : ∀ c : List Nat, Decidable (AdjacentNe c)
    | [] => isTrue trivial
    | [_] => isTrue trivial
    | a :: b :: rest =>
      have : Decidable (AdjacentNe (b :: rest)) := instDecidableAdjacentNe (b :: rest)
      inferInstanceAs (Decidable (a ≠ b ∧ AdjacentNe (b :: rest)))

  def IsRoute (locs : List Std.I64) (start finish fuel : Nat) (c : List Nat) : Prop :=
    c.head? = some start ∧ c.getLast? = some finish ∧
      (∀ i ∈ c, i < locs.length) ∧ AdjacentNe c ∧ pathCost locs c ≤ fuel

  instance instDecidableIsRoute (locs : List Std.I64) (start finish fuel : Nat) (c : List Nat) :
      Decidable (IsRoute locs start finish fuel c) := by
    unfold IsRoute
    infer_instance

  def indexLists (n k : Nat) : Finset (List Nat) :=
    (Finset.univ : Finset (Fin k → Fin n)).image (fun f => (List.ofFn f).map Fin.val)

  def routeCount (locations : Slice Std.I64) (start finish fuel : Std.I64) : Nat :=
    (Finset.range (fuel.val.toNat + 1)).sum fun k =>
      (((indexLists locations.val.length (k + 1)).filter
        (fun c => IsRoute locations.val start.val.toNat finish.val.toNat
          fuel.val.toNat c)).card)

  def minSep (locs : List Std.I64) (i : Nat) : Option Nat :=
    ((List.range locs.length).filter (fun j => j ≠ i)).foldr
      (fun j acc =>
        some (match acc with
          | none => locDist locs j i
          | some m => min (locDist locs j i) m))
      none

  def betweenCount (locs : List Std.I64) (i j : Nat) : Nat :=
    ((List.range locs.length).filter (fun k =>
        k ≠ i ∧ k ≠ j ∧
          min (locAt locs i) (locAt locs j) < locAt locs k ∧
            locAt locs k < max (locAt locs i) (locAt locs j))).length

  def LocationsOK (locations : Slice Std.I64) : Prop :=
    2 ≤ locations.val.length ∧ locations.val.length ≤ 100 ∧
      (∀ x ∈ locations.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) ∧
        locations.val.Pairwise (fun a b => a.val ≠ b.val)

  def IndicesOK (locations : Slice Std.I64) (start finish fuel : Std.I64) : Prop :=
    0 ≤ start.val ∧ start.val < (locations.val.length : Int) ∧
      0 ≤ finish.val ∧ finish.val < (locations.val.length : Int) ∧
        1 ≤ fuel.val ∧ fuel.val ≤ 200

  def ValidInput (locations : Slice Std.I64) (start finish fuel : Std.I64) : Prop :=
    LocationsOK locations ∧ IndicesOK locations start finish fuel

  /-- Let n = len(locations) and M = 1000000007. A route is a finite sequence of indices c_0, ..., c_m for some m >= 0 such that c_0 = start, c_m = finish, every c_t satisfies 0 <= c_t < n, c_t != c_{t+1} for every 0 <= t < m, and sum_{t=1..m} |locations[c_t] - locations[c_{t-1}]| <= fuel. The case m = 0 is the one-term sequence (start) and is allowed exactly when start = finish. Let C be the number of such routes. The function returns a result r and r = C mod M, i.e., r is the unique integer with 0 <= r < M and C ≡ r (mod M).
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_1 (locations : Slice Std.I64) (start finish fuel : Std.I64)
      (h : ValidInput locations start finish fuel) :
      ∃ r : Std.I64,
        Aegis.CountRoutes.count_routes locations start finish fuel = ok r ∧
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            r.val = ((routeCount locations start finish fuel % 1000000007 : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (locations : Slice Std.I64) (start finish fuel : Std.I64)
        (h : ValidInput locations start finish fuel), ∃ r : Std.I64,
          Aegis.CountRoutes.count_routes locations start finish fuel = ok r ∧
            0 ≤ r.val ∧ r.val < 1000000007 ∧
              r.val = ((routeCount locations start finish fuel % 1000000007 : Nat) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail due to overflow, panic, or out-of-bounds access.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_2 (locations : Slice Std.I64) (start finish fuel : Std.I64)
      (h : ValidInput locations start finish fuel) :
      ∃ r : Std.I64, Aegis.CountRoutes.count_routes locations start finish fuel = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (locations : Slice Std.I64) (start finish fuel : Std.I64)
        (h : ValidInput locations start finish fuel), ∃ r : Std.I64, Aegis.CountRoutes.count_routes locations start finish fuel = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 1000000007.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_3 (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
      (h : ValidInput locations start finish fuel)
      (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r) :
      0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
        (h : ValidInput locations start finish fuel)
        (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r), 0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- Whenever the function returns a result r, if |locations[start] - locations[finish]| > fuel, then r = 0.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_4 (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
      (h : ValidInput locations start finish fuel)
      (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r)
      (hfar : |locAt locations.val start.val.toNat - locAt locations.val finish.val.toNat|
        > fuel.val) :
      r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
        (h : ValidInput locations start finish fuel)
        (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r)
        (hfar : |locAt locations.val start.val.toNat - locAt locations.val finish.val.toNat|
          > fuel.val), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, if for every j with 0 <= j < len(locations) and j != start we have |locations[j] - locations[start]| > fuel, then r = 1 when start = finish, and r = 0 when start != finish.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_5 (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
      (h : ValidInput locations start finish fuel)
      (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r)
      (hisolated : ∀ j, j < locations.val.length → j ≠ start.val.toNat →
        |locAt locations.val j - locAt locations.val start.val.toNat| > fuel.val) :
      (start.val = finish.val → r.val = 1) ∧ (start.val ≠ finish.val → r.val = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
        (h : ValidInput locations start finish fuel)
        (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r)
        (hisolated : ∀ j, j < locations.val.length → j ≠ start.val.toNat →
          |locAt locations.val j - locAt locations.val start.val.toNat| > fuel.val), (start.val = finish.val → r.val = 1) ∧ (start.val ≠ finish.val → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, if for every j with 0 <= j < len(locations) and j != finish we have |locations[j] - locations[finish]| > fuel, then r = 1 when start = finish, and r = 0 when start != finish.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_6 (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
      (h : ValidInput locations start finish fuel)
      (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r)
      (hisolated : ∀ j, j < locations.val.length → j ≠ finish.val.toNat →
        |locAt locations.val j - locAt locations.val finish.val.toNat| > fuel.val) :
      (start.val = finish.val → r.val = 1) ∧ (start.val ≠ finish.val → r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
        (h : ValidInput locations start finish fuel)
        (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r)
        (hisolated : ∀ j, j < locations.val.length → j ≠ finish.val.toNat →
          |locAt locations.val j - locAt locations.val finish.val.toNat| > fuel.val), (start.val = finish.val → r.val = 1) ∧ (start.val ≠ finish.val → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, if start = finish and fuel < 2 * min { |locations[j] - locations[start]| : 0 <= j < len(locations), j != start }, then r = 1.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_7 (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
      (h : ValidInput locations start finish fuel)
      (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r)
      (hsame : start.val = finish.val)
      (hmin : ∀ m, minSep locations.val start.val.toNat = some m → fuel.val < 2 * (m : Int)) :
      r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
        (h : ValidInput locations start finish fuel)
        (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r)
        (hsame : start.val = finish.val)
        (hmin : ∀ m, minSep locations.val start.val.toNat = some m → fuel.val < 2 * (m : Int)), r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, if for every pair of indices i, j with 0 <= i < j < len(locations) we have 2 * |locations[i] - locations[j]| > fuel, then r equals 1 when start = finish; if start != finish, then r equals 1 when |locations[start] - locations[finish]| <= fuel, and r equals 0 otherwise.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_8 (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
      (h : ValidInput locations start finish fuel)
      (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r)
      (hsep : ∀ i j, i < j → j < locations.val.length →
        2 * |locAt locations.val i - locAt locations.val j| > fuel.val) :
      (start.val = finish.val → r.val = 1) ∧
        (start.val ≠ finish.val →
          |locAt locations.val start.val.toNat - locAt locations.val finish.val.toNat|
              ≤ fuel.val → r.val = 1) ∧
          (start.val ≠ finish.val →
            |locAt locations.val start.val.toNat - locAt locations.val finish.val.toNat|
                > fuel.val → r.val = 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
        (h : ValidInput locations start finish fuel)
        (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r)
        (hsep : ∀ i j, i < j → j < locations.val.length →
          2 * |locAt locations.val i - locAt locations.val j| > fuel.val), (start.val = finish.val → r.val = 1) ∧
          (start.val ≠ finish.val →
            |locAt locations.val start.val.toNat - locAt locations.val finish.val.toNat|
                ≤ fuel.val → r.val = 1) ∧
            (start.val ≠ finish.val →
              |locAt locations.val start.val.toNat - locAt locations.val finish.val.toNat|
                  > fuel.val → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, if len(locations) = 2, let d = |locations[0] - locations[1]| and q = floor(fuel / d). If start != finish then r = floor((q + 1) / 2); if start = finish then r = floor(q / 2) + 1.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_9 (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
      (h : ValidInput locations start finish fuel)
      (hlen : locations.val.length = 2)
      (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r) :
      let d := locDist locations.val 0 1
      let q := fuel.val.toNat / d
      (start.val ≠ finish.val → r.val = (((q + 1) / 2 : Nat) : Int)) ∧
        (start.val = finish.val → r.val = ((q / 2 + 1 : Nat) : Int)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
        (h : ValidInput locations start finish fuel)
        (hlen : locations.val.length = 2)
        (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r), let d := locDist locations.val 0 1
        let q := fuel.val.toNat / d
        (start.val ≠ finish.val → r.val = (((q + 1) / 2 : Nat) : Int)) ∧
          (start.val = finish.val → r.val = ((q / 2 + 1 : Nat) : Int))) := by
    sorry

  /-- For every input satisfying the preconditions, consider the two calls count_routes locations start finish fuel and count_routes locations finish start fuel. Whenever these two calls both return results r1 and r2 respectively, r1 = r2.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_10 (locations : Slice Std.I64) (start finish fuel : Std.I64)
      (r1 r2 : Std.I64)
      (h : ValidInput locations start finish fuel)
      (h1 : Aegis.CountRoutes.count_routes locations start finish fuel = ok r1)
      (h2 : Aegis.CountRoutes.count_routes locations finish start fuel = ok r2) :
      r1.val = r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (locations : Slice Std.I64) (start finish fuel : Std.I64)
        (r1 r2 : Std.I64)
        (h : ValidInput locations start finish fuel)
        (h1 : Aegis.CountRoutes.count_routes locations start finish fuel = ok r1)
        (h2 : Aegis.CountRoutes.count_routes locations finish start fuel = ok r2), r1.val = r2.val) := by
    sorry

  /-- For every integer k and every slice other with len(other) = len(locations) such that other[i] = locations[i] + k for all 0 <= i < len(locations) and other also satisfies the same location-value constraints, whenever count_routes locations start finish fuel returns r1 and count_routes other start finish fuel returns r2, we have r1 = r2.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_11 (locations other : Slice Std.I64) (start finish fuel : Std.I64) (k : Int)
      (r1 r2 : Std.I64)
      (h : ValidInput locations start finish fuel)
      (hother : LocationsOK other)
      (hlen : other.val.length = locations.val.length)
      (hshift : ∀ i, i < locations.val.length →
        locAt other.val i = locAt locations.val i + k)
      (h1 : Aegis.CountRoutes.count_routes locations start finish fuel = ok r1)
      (h2 : Aegis.CountRoutes.count_routes other start finish fuel = ok r2) :
      r1.val = r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (locations other : Slice Std.I64) (start finish fuel : Std.I64) (k : Int)
        (r1 r2 : Std.I64)
        (h : ValidInput locations start finish fuel)
        (hother : LocationsOK other)
        (hlen : other.val.length = locations.val.length)
        (hshift : ∀ i, i < locations.val.length →
          locAt other.val i = locAt locations.val i + k)
        (h1 : Aegis.CountRoutes.count_routes locations start finish fuel = ok r1)
        (h2 : Aegis.CountRoutes.count_routes other start finish fuel = ok r2), r1.val = r2.val) := by
    sorry

  /-- For every permutation p of {0, ..., n-1}, where n = len(locations), define other[i] = locations[p(i)] for 0 <= i < n, and let s and f be the indices with p(s) = start and p(f) = finish. Whenever count_routes locations start finish fuel returns r1 and count_routes other s f fuel returns r2, we have r1 = r2.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_12 (locations other : Slice Std.I64) (start finish fuel s f : Std.I64)
      (r1 r2 : Std.I64)
      (h : ValidInput locations start finish fuel)
      (hother : LocationsOK other)
      (p : Equiv.Perm (Fin locations.val.length))
      (hperm : other.val.length = locations.val.length ∧
        ∀ i : Fin locations.val.length,
          locAt other.val i.val = locAt locations.val (p i).val)
      (hs : 0 ≤ s.val ∧ s.val.toNat < locations.val.length)
      (hf : 0 ≤ f.val ∧ f.val.toNat < locations.val.length)
      (hsp : (p ⟨s.val.toNat, hs.2⟩).val = start.val.toNat)
      (hfp : (p ⟨f.val.toNat, hf.2⟩).val = finish.val.toNat)
      (h1 : Aegis.CountRoutes.count_routes locations start finish fuel = ok r1)
      (h2 : Aegis.CountRoutes.count_routes other s f fuel = ok r2) :
      r1.val = r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (locations other : Slice Std.I64) (start finish fuel s f : Std.I64)
        (r1 r2 : Std.I64)
        (h : ValidInput locations start finish fuel)
        (hother : LocationsOK other)
        (p : Equiv.Perm (Fin locations.val.length))
        (hperm : other.val.length = locations.val.length ∧
          ∀ i : Fin locations.val.length,
            locAt other.val i.val = locAt locations.val (p i).val)
        (hs : 0 ≤ s.val ∧ s.val.toNat < locations.val.length)
        (hf : 0 ≤ f.val ∧ f.val.toNat < locations.val.length)
        (hsp : (p ⟨s.val.toNat, hs.2⟩).val = start.val.toNat)
        (hfp : (p ⟨f.val.toNat, hf.2⟩).val = finish.val.toNat)
        (h1 : Aegis.CountRoutes.count_routes locations start finish fuel = ok r1)
        (h2 : Aegis.CountRoutes.count_routes other s f fuel = ok r2), r1.val = r2.val) := by
    sorry

  /-- Whenever the function returns a result r, if start != finish and fuel = |locations[start] - locations[finish]|, let k be the number of indices i with 0 <= i < len(locations), i != start, i != finish, and min(locations[start], locations[finish]) < locations[i] < max(locations[start], locations[finish]). Then r = (2^k) mod 1000000007.
    Preconditions: len(locations) is between 2 and 100 inclusive; for every i with 0 <= i < len(locations), locations[i] is an integer with 1 <= locations[i] <= 1000000000; the values locations[i] are pairwise distinct; 0 <= start < len(locations); 0 <= finish < len(locations); 1 <= fuel <= 200. -/
  theorem spec_13 (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
      (h : ValidInput locations start finish fuel)
      (hne : start.val ≠ finish.val)
      (hfuel : fuel.val =
        |locAt locations.val start.val.toNat - locAt locations.val finish.val.toNat|)
      (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r) :
      r.val = (((2 ^ betweenCount locations.val start.val.toNat finish.val.toNat)
        % 1000000007 : Nat) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (locations : Slice Std.I64) (start finish fuel : Std.I64) (r : Std.I64)
        (h : ValidInput locations start finish fuel)
        (hne : start.val ≠ finish.val)
        (hfuel : fuel.val =
          |locAt locations.val start.val.toNat - locAt locations.val finish.val.toNat|)
        (hret : Aegis.CountRoutes.count_routes locations start finish fuel = ok r), r.val = (((2 ^ betweenCount locations.val start.val.toNat finish.val.toNat)
          % 1000000007 : Nat) : Int)) := by
    sorry

  end

  end AegisSpec.CountRoutes
