import Aegis.CheapestJump.Code.Funs

/-!
# Specifications of `Aegis.CheapestJump.cheapest_jump`

LeetCode problem `coin-path`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CheapestJump

  def vecInts (v : alloc.vec.Vec Aeneas.Std.I64) : List Int := v.val.map (fun x => x.val)

  def sliceInts (s : Slice Aeneas.Std.I64) : List Int := s.val.map (fun x => x.val)

  def seqUpTo (n : Nat) : List Int := (List.range' 1 n).map (fun k => (k : Int))

  def pathCost (c : List Int) (p : List Int) : Int :=
    (p.map (fun j => c.getD (j.toNat - 1) 0)).sum

  def LexLE (r q : List Int) : Prop :=
    r = q ∨
      (∃ j : Nat,
        j < min r.length q.length ∧
          (∀ i : Nat, i < j → r[i]? = q[i]?) ∧
          (∃ a b : Int, r[j]? = some a ∧ q[j]? = some b ∧ a < b)) ∨
      (r.length < q.length ∧ ∀ i : Nat, i < r.length → r[i]? = q[i]?)

  def IsValidPath (c : List Int) (maxJump : Int) (p : List Int) : Prop :=
    p ≠ [] ∧
      p.head? = some 1 ∧
      p.getLast? = some (c.length : Int) ∧
      (∀ (j : Nat) (v : Int), p[j]? = some v →
        1 ≤ v ∧ v ≤ (c.length : Int) ∧ c[v.toNat - 1]? ≠ some (-1)) ∧
      (∀ (j : Nat) (a b : Int), p[j]? = some a → p[j + 1]? = some b →
        1 ≤ b - a ∧ b - a ≤ maxJump)

  def IsMinCostPath (c : List Int) (maxJump : Int) (p : List Int) : Prop :=
    IsValidPath c maxJump p ∧
      ∀ q : List Int, IsValidPath c maxJump q → pathCost c p ≤ pathCost c q

  def IsOptimalPath (c : List Int) (maxJump : Int) (p : List Int) : Prop :=
    IsMinCostPath c maxJump p ∧
      ∀ q : List Int, IsValidPath c maxJump q → pathCost c q = pathCost c p → LexLE p q

  /-- Let n = len(coins). A sequence p of integers is a valid path if: len(p) >= 1; p[0] = 1; p[len(p)-1] = n; for all j with 0 <= j < len(p), 1 <= p[j] <= n and coins[p[j]-1] != -1; and for all j with 0 <= j < len(p)-1, 1 <= p[j+1] - p[j] <= maxJump. The cost of a valid path p is sum_{j=0}^{len(p)-1} coins[p[j]-1]. Let P be the set of all valid paths. If P is empty, then the function returns a result r and len(r) = 0. If P is not empty, let c = min_{p in P} cost(p). Then the function returns a result r such that r is a valid path, cost(r) = c, and for every q in P with cost(q) = c, r is lexicographically smaller than or equal to q, where the lexicographic order on integer sequences is: r <= q iff either r = q, or there exists an index j with 0 <= j < min(len(r), len(q)) such that for all i < j, r[i] = q[i] and r[j] < q[j], or (len(r) < len(q) and for all i < len(r), r[i] = q[i]).
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_1 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100) :
      ((∀ p : List Int, ¬ IsValidPath (sliceInts coins) maxJump.val p) →
          ∃ r : alloc.vec.Vec Aeneas.Std.I64,
            Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧ (vecInts r).length = 0) ∧
        ((∃ p : List Int, IsValidPath (sliceInts coins) maxJump.val p) →
          ∃ r : alloc.vec.Vec Aeneas.Std.I64,
            Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧
              IsOptimalPath (sliceInts coins) maxJump.val (vecInts r)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100), ((∀ p : List Int, ¬ IsValidPath (sliceInts coins) maxJump.val p) →
            ∃ r : alloc.vec.Vec Aeneas.Std.I64,
              Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧ (vecInts r).length = 0) ∧
          ((∃ p : List Int, IsValidPath (sliceInts coins) maxJump.val p) →
            ∃ r : alloc.vec.Vec Aeneas.Std.I64,
              Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧
                IsOptimalPath (sliceInts coins) maxJump.val (vecInts r))) := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_2 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100) :
      ∃ r : alloc.vec.Vec Aeneas.Std.I64, Aegis.CheapestJump.cheapest_jump coins maxJump = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100), ∃ r : alloc.vec.Vec Aeneas.Std.I64, Aegis.CheapestJump.cheapest_jump coins maxJump = ok r) := by
    sorry

  /-- Let n = len(coins). Let P be the set of valid paths as defined in spec_1. The function returns r such that len(r) = 0 if and only if P is empty.
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_3 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100) :
      ∃ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧
          ((vecInts r).length = 0 ↔ ∀ p : List Int, ¬ IsValidPath (sliceInts coins) maxJump.val p) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100), ∃ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧
            ((vecInts r).length = 0 ↔ ∀ p : List Int, ¬ IsValidPath (sliceInts coins) maxJump.val p)) := by
    sorry

  /-- If the returned r is non-empty, then r[0] = 1 and r[len(r)-1] = n, where n = len(coins).
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_4 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
          (vecInts r).head? = some 1 ∧
            (vecInts r)[(vecInts r).length - 1]? = some (coins.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
            (vecInts r).head? = some 1 ∧
              (vecInts r)[(vecInts r).length - 1]? = some (coins.val.length : Int)) := by
    sorry

  /-- If the returned r is non-empty, then for every j with 0 <= j < len(r)-1, r[j] < r[j+1].
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_5 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
          ∀ (j : Nat) (a b : Int),
            (vecInts r)[j]? = some a → (vecInts r)[j + 1]? = some b → a < b := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
            ∀ (j : Nat) (a b : Int),
              (vecInts r)[j]? = some a → (vecInts r)[j + 1]? = some b → a < b) := by
    sorry

  /-- If the returned r is non-empty, then for every j with 0 <= j < len(r)-1, 1 <= r[j+1] - r[j] <= maxJump.
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_6 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
          ∀ (j : Nat) (a b : Int), (vecInts r)[j]? = some a → (vecInts r)[j + 1]? = some b →
            1 ≤ b - a ∧ b - a ≤ maxJump.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
            ∀ (j : Nat) (a b : Int), (vecInts r)[j]? = some a → (vecInts r)[j + 1]? = some b →
              1 ≤ b - a ∧ b - a ≤ maxJump.val) := by
    sorry

  /-- If the returned r is non-empty, then for every j with 0 <= j < len(r), 1 <= r[j] <= n and coins[r[j]-1] != -1, where n = len(coins).
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_7 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
          ∀ (j : Nat) (v : Int), (vecInts r)[j]? = some v →
            1 ≤ v ∧ v ≤ (coins.val.length : Int) ∧ (sliceInts coins)[v.toNat - 1]? ≠ some (-1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
            ∀ (j : Nat) (v : Int), (vecInts r)[j]? = some v →
              1 ≤ v ∧ v ≤ (coins.val.length : Int) ∧ (sliceInts coins)[v.toNat - 1]? ≠ some (-1)) := by
    sorry

  /-- If the returned r is non-empty, then for every valid path q (as defined in spec_1), cost(r) <= cost(q), where cost(p) = sum_{j=0}^{len(p)-1} coins[p[j]-1].
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_8 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
          ∀ q : List Int, IsValidPath (sliceInts coins) maxJump.val q →
            pathCost (sliceInts coins) (vecInts r) ≤ pathCost (sliceInts coins) q := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
            ∀ q : List Int, IsValidPath (sliceInts coins) maxJump.val q →
              pathCost (sliceInts coins) (vecInts r) ≤ pathCost (sliceInts coins) q) := by
    sorry

  /-- If the returned r is non-empty, then for every valid path q (as defined in spec_1) with cost(q) = cost(r), r is lexicographically smaller than or equal to q, where the lexicographic order on integer sequences is: r <= q iff either r = q, or there exists an index j with 0 <= j < min(len(r), len(q)) such that for all i < j, r[i] = q[i] and r[j] < q[j], or (len(r) < len(q) and for all i < len(r), r[i] = q[i]).
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_9 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
          ∀ q : List Int, IsValidPath (sliceInts coins) maxJump.val q →
            pathCost (sliceInts coins) q = pathCost (sliceInts coins) (vecInts r) →
              LexLE (vecInts r) q := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
            ∀ q : List Int, IsValidPath (sliceInts coins) maxJump.val q →
              pathCost (sliceInts coins) q = pathCost (sliceInts coins) (vecInts r) →
                LexLE (vecInts r) q) := by
    sorry

  /-- If the returned r is non-empty, then 1 <= len(r) <= n, where n = len(coins).
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_10 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
          1 ≤ (vecInts r).length ∧ (vecInts r).length ≤ coins.val.length := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
            1 ≤ (vecInts r).length ∧ (vecInts r).length ≤ coins.val.length) := by
    sorry

  /-- If len(coins) = 1, then the function returns r = [1].
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_11 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100)
      (hsingle : coins.val.length = 1) :
      ∃ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧ vecInts r = [1] := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100)
        (hsingle : coins.val.length = 1), ∃ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧ vecInts r = [1]) := by
    sorry

  /-- If len(coins) >= 1 and coins[len(coins)-1] = -1, then the function returns r with len(r) = 0.
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_12 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100)
      (hlast : (sliceInts coins)[(sliceInts coins).length - 1]? = some (-1)) :
      ∃ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧ (vecInts r).length = 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100)
        (hlast : (sliceInts coins)[(sliceInts coins).length - 1]? = some (-1)), ∃ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧ (vecInts r).length = 0) := by
    sorry

  /-- If maxJump = 1, then: if there exists an index i with 0 <= i < len(coins) and coins[i] = -1, the function returns r with len(r) = 0; otherwise, the function returns r = [1, 2, ..., len(coins)] (the sequence of all integers from 1 to n).
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_13 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100)
      (hmax : maxJump.val = 1) :
      ((∃ i : Nat, i < coins.val.length ∧ (sliceInts coins)[i]? = some (-1)) →
          ∃ r : alloc.vec.Vec Aeneas.Std.I64,
            Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧ (vecInts r).length = 0) ∧
        ((¬ ∃ i : Nat, i < coins.val.length ∧ (sliceInts coins)[i]? = some (-1)) →
          ∃ r : alloc.vec.Vec Aeneas.Std.I64,
            Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧
              vecInts r = seqUpTo coins.val.length) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100)
        (hmax : maxJump.val = 1), ((∃ i : Nat, i < coins.val.length ∧ (sliceInts coins)[i]? = some (-1)) →
            ∃ r : alloc.vec.Vec Aeneas.Std.I64,
              Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧ (vecInts r).length = 0) ∧
          ((¬ ∃ i : Nat, i < coins.val.length ∧ (sliceInts coins)[i]? = some (-1)) →
            ∃ r : alloc.vec.Vec Aeneas.Std.I64,
              Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧
                vecInts r = seqUpTo coins.val.length)) := by
    sorry

  /-- If len(coins) >= 2 and maxJump >= len(coins)-1 and coins[len(coins)-1] != -1, then the returned r is non-empty and cost(r) = coins[0] + coins[len(coins)-1], where cost is as defined in spec_1.
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_14 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100)
      (hlen_two : 2 ≤ coins.val.length)
      (hreach : (coins.val.length : Int) - 1 ≤ maxJump.val)
      (hlast : (sliceInts coins)[(sliceInts coins).length - 1]? ≠ some (-1)) :
      ∃ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧ vecInts r ≠ [] ∧
          pathCost (sliceInts coins) (vecInts r) =
            (sliceInts coins).headD 0 + (sliceInts coins).getLastD 0 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100)
        (hlen_two : 2 ≤ coins.val.length)
        (hreach : (coins.val.length : Int) - 1 ≤ maxJump.val)
        (hlast : (sliceInts coins)[(sliceInts coins).length - 1]? ≠ some (-1)), ∃ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r ∧ vecInts r ≠ [] ∧
            pathCost (sliceInts coins) (vecInts r) =
              (sliceInts coins).headD 0 + (sliceInts coins).getLastD 0) := by
    sorry

  /-- If the returned r is non-empty, then cost(r) >= coins[0] + (if len(coins) > 1 then coins[len(coins)-1] else 0), where cost is as defined in spec_1.
    Preconditions: len(coins) >= 1, len(coins) <= 1000, for all i with 0 <= i < len(coins), -1 <= coins[i] <= 100, coins[0] != -1, 1 <= maxJump <= 100. -/
  theorem spec_15 (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
      (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
      (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
      (hfirst : (sliceInts coins)[0]? ≠ some (-1))
      (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
          pathCost (sliceInts coins) (vecInts r) ≥
            (sliceInts coins).headD 0 +
              (if 1 < coins.val.length then (sliceInts coins).getLastD 0 else 0) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (coins : Slice Aeneas.Std.I64) (maxJump : Aeneas.Std.I64)
        (hlen_pos : 1 ≤ coins.val.length) (hlen_bound : coins.val.length ≤ 1000)
        (hcoins : ∀ v : Int, v ∈ sliceInts coins → -1 ≤ v ∧ v ≤ 100)
        (hfirst : (sliceInts coins)[0]? ≠ some (-1))
        (hjump : 1 ≤ maxJump.val ∧ maxJump.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.CheapestJump.cheapest_jump coins maxJump = ok r → vecInts r ≠ [] →
            pathCost (sliceInts coins) (vecInts r) ≥
              (sliceInts coins).headD 0 +
                (if 1 < coins.val.length then (sliceInts coins).getLastD 0 else 0)) := by
    sorry

  end AegisSpec.CheapestJump
