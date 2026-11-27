import Aegis.FindCheapestPrice.Code.Funs

/-!
# Specifications of `Aegis.FindCheapestPrice.find_cheapest_price`

LeetCode problem `cheapest-flights-within-k-stops`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindCheapestPrice (find_cheapest_price)

  namespace AegisSpec.FindCheapestPrice

  def flightFields (flights : Slice (alloc.vec.Vec I64)) (i : Nat) : List I64 :=
    ((flights.val[i]?).map (fun v => v.val)).getD []

  def flightField (flights : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
    (((flightFields flights i)[j]?).map (fun x => x.val)).getD 0

  def IsValidInput (n : I64) (flights : Slice (alloc.vec.Vec I64))
      (src dst k : I64) : Prop :=

    (1 ≤ n.val ∧ n.val ≤ 100) ∧

    ((flights.val.length : Int) ≤ n.val * (n.val - 1) / 2) ∧

    (∀ i : Nat, i < flights.val.length →
      (flightFields flights i).length = 3 ∧
      0 ≤ flightField flights i 0 ∧ flightField flights i 0 < n.val ∧
      0 ≤ flightField flights i 1 ∧ flightField flights i 1 < n.val ∧
      flightField flights i 0 ≠ flightField flights i 1 ∧
      1 ≤ flightField flights i 2 ∧ flightField flights i 2 ≤ 10000) ∧

    (∀ i j : Nat, i < flights.val.length → j < flights.val.length → i ≠ j →
      ¬ (flightField flights i 0 = flightField flights j 0 ∧
         flightField flights i 1 = flightField flights j 1)) ∧

    (0 ≤ src.val ∧ src.val < n.val) ∧
    (0 ≤ dst.val ∧ dst.val < n.val) ∧
    (src.val ≠ dst.val) ∧
    (0 ≤ k.val ∧ k.val < n.val)

  def IsRouteFromTo (flights : Slice (alloc.vec.Vec I64)) (src dst : Int) :
      List Nat → Prop
    | [] => False
    | [i] =>
        i < flights.val.length ∧
        flightField flights i 0 = src ∧ flightField flights i 1 = dst
    | i :: j :: rest =>
        i < flights.val.length ∧
        flightField flights i 0 = src ∧
        IsRouteFromTo flights (flightField flights i 1) dst (j :: rest)

  def ValidRoute (flights : Slice (alloc.vec.Vec I64)) (src dst : Int) (k : Nat)
      (r : List Nat) : Prop :=
    IsRouteFromTo flights src dst r ∧ r.length - 1 ≤ k

  def RoutePrice (flights : Slice (alloc.vec.Vec I64)) : List Nat → Int
    | [] => 0
    | i :: rest => flightField flights i 2 + RoutePrice flights rest

  def IsRoutePrice (flights : Slice (alloc.vec.Vec I64)) (src dst : Int) (k : Nat)
      (c : Int) : Prop :=
    ∃ r : List Nat, ValidRoute flights src dst k r ∧ RoutePrice flights r = c

  def IsRoutePriceUnbounded (flights : Slice (alloc.vec.Vec I64)) (src dst : Int)
      (c : Int) : Prop :=
    ∃ r : List Nat, IsRouteFromTo flights src dst r ∧ RoutePrice flights r = c

  def IsDirectFlightPrice (flights : Slice (alloc.vec.Vec I64)) (src dst : Int)
      (c : Int) : Prop :=
    ∃ i : Nat,
      i < flights.val.length ∧ flightField flights i 0 = src ∧
        flightField flights i 1 = dst ∧ flightField flights i 2 = c

  /-- Let a valid route from src to dst with at most k stops be a sequence of flight indices i_0, ..., i_{m-1} with m >= 1 and 0 <= i_j < len(flights) for every j with 0 <= j < m, such that flights[i_0][0] = src, flights[i_{m-1}][1] = dst, flights[i_j][1] = flights[i_{j+1}][0] for every j with 0 <= j < m-1, and m-1 <= k. Its total price is sum_{j=0}^{m-1} flights[i_j][2]. Let C be the set of all total prices of such valid routes. The function returns a result r and: if C is non-empty then r = min(C); if C is empty then r = -1.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_1 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k) :
      ∃ r : I64,
        find_cheapest_price n flights src dst k = ok r ∧
          ((∃ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c) →
            IsRoutePrice flights src.val dst.val k.val.toNat r.val ∧
              ∀ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c → r.val ≤ c) ∧
          ((¬ ∃ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c) → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k), ∃ r : I64,
          find_cheapest_price n flights src dst k = ok r ∧
            ((∃ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c) →
              IsRoutePrice flights src.val dst.val k.val.toNat r.val ∧
                ∀ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c → r.val ≤ c) ∧
            ((¬ ∃ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c) → r.val = -1)) := by
    sorry

  /-- The function returns a result r; it does not fail.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_2 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k) :
      ∃ r : I64, find_cheapest_price n flights src dst k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k), ∃ r : I64, find_cheapest_price n flights src dst k = ok r) := by
    sorry

  /-- The function returns a result r and r = -1 if and only if there is no valid route from src to dst with at most k stops, where valid route means a sequence of flight indices i_0, ..., i_{m-1} with m >= 1 and 0 <= i_j < len(flights), starting with a flight from src, ending with a flight into dst, consecutive flights connecting, and m-1 <= k.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_3 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k) :
      ∃ r : I64,
        find_cheapest_price n flights src dst k = ok r ∧
          (r.val = -1 ↔ ¬ ∃ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k), ∃ r : I64,
          find_cheapest_price n flights src dst k = ok r ∧
            (r.val = -1 ↔ ¬ ∃ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exists a valid route from src to dst with at most k stops whose total price is exactly r, where valid route means a sequence of flight indices i_0, ..., i_{m-1} with m >= 1 and 0 <= i_j < len(flights), starting with a flight from src, ending with a flight into dst, consecutive flights connecting, and m-1 <= k; its total price is the sum of the prices of its flights.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_4 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k) :
      ∀ r : I64, find_cheapest_price n flights src dst k = ok r → r.val ≠ -1 →
        IsRoutePrice flights src.val dst.val k.val.toNat r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k), ∀ r : I64, find_cheapest_price n flights src dst k = ok r → r.val ≠ -1 →
          IsRoutePrice flights src.val dst.val k.val.toNat r.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every valid route from src to dst with at most k stops and total price p, we have r <= p, where valid route and total price are defined by a sequence of flight indices i_0, ..., i_{m-1} with m >= 1, start src, end dst, consecutive flights connecting, m-1 <= k, and total price equal to the sum of the flight prices.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_5 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k) :
      ∀ r : I64, find_cheapest_price n flights src dst k = ok r → r.val ≠ -1 →
        ∀ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c → r.val ≤ c := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k), ∀ r : I64, find_cheapest_price n flights src dst k = ok r → r.val ≠ -1 →
          ∀ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c → r.val ≤ c) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= (k+1)*10000.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_6 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k) :
      ∀ r : I64, find_cheapest_price n flights src dst k = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (k.val + 1) * 10000) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k), ∀ r : I64, find_cheapest_price n flights src dst k = ok r →
          r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (k.val + 1) * 10000)) := by
    sorry

  /-- Whenever k = 0, the function returns a result r and: if there is an index i with 0 <= i < len(flights), flights[i][0] = src, and flights[i][1] = dst, then r is the minimum of flights[i][2] over all such i; otherwise r = -1.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_7 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k) (hk : k.val = 0) :
      ∃ r : I64,
        find_cheapest_price n flights src dst k = ok r ∧
          ((∃ c : Int, IsDirectFlightPrice flights src.val dst.val c) →
            IsDirectFlightPrice flights src.val dst.val r.val ∧
              ∀ c : Int, IsDirectFlightPrice flights src.val dst.val c → r.val ≤ c) ∧
          ((¬ ∃ c : Int, IsDirectFlightPrice flights src.val dst.val c) → r.val = -1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k) (hk : k.val = 0), ∃ r : I64,
          find_cheapest_price n flights src dst k = ok r ∧
            ((∃ c : Int, IsDirectFlightPrice flights src.val dst.val c) →
              IsDirectFlightPrice flights src.val dst.val r.val ∧
                ∀ c : Int, IsDirectFlightPrice flights src.val dst.val c → r.val ≤ c) ∧
            ((¬ ∃ c : Int, IsDirectFlightPrice flights src.val dst.val c) → r.val = -1)) := by
    sorry

  /-- Whenever the function returns a result r and there is an index i with 0 <= i < len(flights), flights[i][0] = src, and flights[i][1] = dst, then r != -1 and r <= flights[i][2].
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_8 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k) :
      ∀ r : I64, find_cheapest_price n flights src dst k = ok r →
        ∀ i : Nat, i < flights.val.length → flightField flights i 0 = src.val →
          flightField flights i 1 = dst.val → r.val ≠ -1 ∧ r.val ≤ flightField flights i 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k), ∀ r : I64, find_cheapest_price n flights src dst k = ok r →
          ∀ i : Nat, i < flights.val.length → flightField flights i 0 = src.val →
            flightField flights i 1 = dst.val → r.val ≠ -1 ∧ r.val ≤ flightField flights i 2) := by
    sorry

  /-- For every pair of integers k1 and k2 with 0 <= k1 <= k2 < n, whenever find_cheapest_price(n, flights, src, dst, k1) returns a result r1 and find_cheapest_price(n, flights, src, dst, k2) returns a result r2, if r1 != -1 then r2 != -1 and r2 <= r1.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k1 <= k2 < n. -/
  theorem spec_9 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k1 k2 : I64)
      (h1 : IsValidInput n flights src dst k1) (h2 : IsValidInput n flights src dst k2)
      (hk : k1.val ≤ k2.val) :
      ∀ r1 r2 : I64,
        find_cheapest_price n flights src dst k1 = ok r1 →
          find_cheapest_price n flights src dst k2 = ok r2 →
            r1.val ≠ -1 → r2.val ≠ -1 ∧ r2.val ≤ r1.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k1 k2 : I64)
        (h1 : IsValidInput n flights src dst k1) (h2 : IsValidInput n flights src dst k2)
        (hk : k1.val ≤ k2.val), ∀ r1 r2 : I64,
          find_cheapest_price n flights src dst k1 = ok r1 →
            find_cheapest_price n flights src dst k2 = ok r2 →
              r1.val ≠ -1 → r2.val ≠ -1 ∧ r2.val ≤ r1.val) := by
    sorry

  /-- For every list of flight triples flights' that is a permutation of flights, whenever find_cheapest_price(n, flights, src, dst, k) returns r and find_cheapest_price(n, flights', src, dst, k) returns r', we have r' = r.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n; flights' is a list of triples that is a permutation of flights (same multiset of triples). -/
  theorem spec_10 (n : I64) (flights flights' : Slice (alloc.vec.Vec I64))
      (src dst k : I64) (h : IsValidInput n flights src dst k)
      (hperm : List.Perm flights'.val flights.val) :
      ∀ r r' : I64,
        find_cheapest_price n flights src dst k = ok r →
          find_cheapest_price n flights' src dst k = ok r' → r'.val = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (flights flights' : Slice (alloc.vec.Vec I64))
        (src dst k : I64) (h : IsValidInput n flights src dst k)
        (hperm : List.Perm flights'.val flights.val), ∀ r r' : I64,
          find_cheapest_price n flights src dst k = ok r →
            find_cheapest_price n flights' src dst k = ok r' → r'.val = r.val) := by
    sorry

  /-- For every integer n' with n <= n' <= 100, whenever find_cheapest_price(n, flights, src, dst, k) returns r and find_cheapest_price(n', flights, src, dst, k) returns r', we have r' = r.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n; n' is an integer with n <= n' <= 100. -/
  theorem spec_11 (n n' : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k) (hn : n.val ≤ n'.val) (hn' : n'.val ≤ 100) :
      ∀ r r' : I64,
        find_cheapest_price n flights src dst k = ok r →
          find_cheapest_price n' flights src dst k = ok r' → r'.val = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n n' : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k) (hn : n.val ≤ n'.val) (hn' : n'.val ≤ 100), ∀ r r' : I64,
          find_cheapest_price n flights src dst k = ok r →
            find_cheapest_price n' flights src dst k = ok r' → r'.val = r.val) := by
    sorry

  /-- Whenever there is no index i with 0 <= i < len(flights) and flights[i][0] = src, the function returns a result r and r = -1.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_12 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k)
      (hsrc : ¬ ∃ i : Nat, i < flights.val.length ∧ flightField flights i 0 = src.val) :
      ∃ r : I64, find_cheapest_price n flights src dst k = ok r ∧ r.val = -1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k)
        (hsrc : ¬ ∃ i : Nat, i < flights.val.length ∧ flightField flights i 0 = src.val), ∃ r : I64, find_cheapest_price n flights src dst k = ok r ∧ r.val = -1) := by
    sorry

  /-- Whenever there is no index i with 0 <= i < len(flights) and flights[i][1] = dst, the function returns a result r and r = -1.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_13 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k)
      (hdst : ¬ ∃ i : Nat, i < flights.val.length ∧ flightField flights i 1 = dst.val) :
      ∃ r : I64, find_cheapest_price n flights src dst k = ok r ∧ r.val = -1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k)
        (hdst : ¬ ∃ i : Nat, i < flights.val.length ∧ flightField flights i 1 = dst.val), ∃ r : I64, find_cheapest_price n flights src dst k = ok r ∧ r.val = -1) := by
    sorry

  /-- Whenever k = n-1, the function returns a result r and r equals the minimum total price over all valid routes from src to dst with no restriction on the number of stops, or r = -1 if there is no such route. Here a valid route with no restriction is a sequence of flight indices i_0, ..., i_{m-1} with m >= 1 and 0 <= i_j < len(flights), starting with a flight from src, ending with a flight into dst, and consecutive flights connecting; its total price is the sum of the prices of its flights.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_14 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k) (hk : k.val = n.val - 1) :
      ∃ r : I64,
        find_cheapest_price n flights src dst k = ok r ∧
          ((∃ c : Int, IsRoutePriceUnbounded flights src.val dst.val c) →
            IsRoutePriceUnbounded flights src.val dst.val r.val ∧
              ∀ c : Int, IsRoutePriceUnbounded flights src.val dst.val c → r.val ≤ c) ∧
          ((¬ ∃ c : Int, IsRoutePriceUnbounded flights src.val dst.val c) → r.val = -1) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k) (hk : k.val = n.val - 1), ∃ r : I64,
          find_cheapest_price n flights src dst k = ok r ∧
            ((∃ c : Int, IsRoutePriceUnbounded flights src.val dst.val c) →
              IsRoutePriceUnbounded flights src.val dst.val r.val ∧
                ∀ c : Int, IsRoutePriceUnbounded flights src.val dst.val c → r.val ≤ c) ∧
            ((¬ ∃ c : Int, IsRoutePriceUnbounded flights src.val dst.val c) → r.val = -1)) := by
    sorry

  /-- Whenever there exists a valid route from src to dst with at most k stops and total price c, the function returns a result r with r != -1 and r <= c, where valid route and total price are defined by a sequence of flight indices i_0, ..., i_{m-1} with m >= 1, start src, end dst, consecutive flights connecting, m-1 <= k, and total price equal to the sum of the flight prices.
    Preconditions: 1 <= n <= 100; len(flights) <= n*(n-1)/2; for every i with 0 <= i < len(flights), len(flights[i]) = 3, 0 <= flights[i][0] < n, 0 <= flights[i][1] < n, flights[i][0] != flights[i][1], and 1 <= flights[i][2] <= 10000; no two distinct indices i and j with 0 <= i < len(flights) and 0 <= j < len(flights) have flights[i][0] = flights[j][0] and flights[i][1] = flights[j][1]; 0 <= src < n; 0 <= dst < n; src != dst; 0 <= k < n. -/
  theorem spec_15 (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
      (h : IsValidInput n flights src dst k) :
      ∀ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c →
        ∃ r : I64, find_cheapest_price n flights src dst k = ok r ∧ r.val ≠ -1 ∧ r.val ≤ c := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : I64) (flights : Slice (alloc.vec.Vec I64)) (src dst k : I64)
        (h : IsValidInput n flights src dst k), ∀ c : Int, IsRoutePrice flights src.val dst.val k.val.toNat c →
          ∃ r : I64, find_cheapest_price n flights src dst k = ok r ∧ r.val ≠ -1 ∧ r.val ≤ c) := by
    sorry

  end AegisSpec.FindCheapestPrice
