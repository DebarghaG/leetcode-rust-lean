import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `minimum-cost-to-buy-apples`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Classical

  namespace AegisSpec.MinCost

  def roadCoords (r : alloc.vec.Vec Aeneas.Std.I64) : List ℤ :=
    r.val.map (fun x => x.val)

  def roadData (roads : Slice (alloc.vec.Vec Aeneas.Std.I64)) : List (List ℤ) :=
    roads.val.map roadCoords

  def appleAt (appleCost : Slice Aeneas.Std.I64) (j : ℤ) : ℤ :=
    (appleCost.val.getD ((j - 1).toNat) 0#i64).val

  def resultAt (r : alloc.vec.Vec Aeneas.Std.I64) (i : ℤ) : ℤ :=
    (r.val.getD ((i - 1).toNat) 0#i64).val

  def Ends (R : List (List ℤ)) (t : ℕ) (x y : ℤ) : Prop :=
    ∃ w : ℤ, R[t]? = some [x, y, w] ∨ R[t]? = some [y, x, w]

  def NoMultiedge (R : List (List ℤ)) : Prop :=
    ∀ (t₁ t₂ : ℕ) (x y : ℤ), Ends R t₁ x y → Ends R t₂ x y → t₁ = t₂

  def Edge (R : List (List ℤ)) (x y : ℤ) (w : ℕ) : Prop :=
    ∃ t : ℕ, R[t]? = some [x, y, (w : ℤ)] ∨ R[t]? = some [y, x, (w : ℤ)]

  inductive Walk (R : List (List ℤ)) : ℤ → ℤ → ℕ → Prop where
    | nil (u : ℤ) : Walk R u u 0
    | step {u v x : ℤ} {w c : ℕ} : Edge R u v w → Walk R v x c → Walk R u x (w + c)

  def Reachable (R : List (List ℤ)) (u v : ℤ) : Prop :=
    ∃ c : ℕ, Walk R u v c

  noncomputable def dist (R : List (List ℤ)) (u v : ℤ) : ℕ :=
    if h : ∃ c : ℕ, Walk R u v c then Nat.find h else 0

  noncomputable def trip (R : List (List ℤ)) (appleCost : Slice Aeneas.Std.I64) (k : ℤ)
      (i j : ℤ) : ℤ :=
    (1 + k) * ((dist R i j : ℤ)) + appleAt appleCost j

  /-- The function returns a result r, len(r) = n, and for every city i with 1 <= i <= n, r[i-1] equals the minimum of (1+k)*d(i,j) + appleCost[j-1] over all cities j with 1 <= j <= n that are reachable from i in the undirected graph whose edges are the roads; here d(u,v) is the least total road cost of any route from city u to city v, with d(u,u)=0. Equivalently, r[i-1] is the least possible total cost of starting at city i, traveling to some city j, buying exactly one apple there for appleCost[j-1], and returning to i while every road cost on the return trip is multiplied by k.
    Preconditions: Problem constraints hold: 2 <= n <= 1000; roads is a list of length m with 1 <= m <= 2000; each roads[t] is a 3-element vector [a_t,b_t,c_t] with 1 <= a_t,b_t <= n, a_t != b_t, and 1 <= c_t <= 100000; no unordered pair of cities occurs as the endpoints of two different roads; appleCost has length n and 1 <= appleCost[j] <= 100000 for every 0 <= j < n; 1 <= k <= 100. -/
  theorem spec_1
      (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
        (roadData roads)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData roads))
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∃ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n roads appleCost k = ok r ∧
        r.val.length = n.val.toNat ∧
        (∀ i : ℤ, 1 ≤ i → i ≤ n.val →
          (∃ j : ℤ, 1 ≤ j ∧ j ≤ n.val ∧ Reachable (roadData roads) i j ∧
            resultAt r i = trip (roadData roads) appleCost k.val i j) ∧
          (∀ j : ℤ, 1 ≤ j → j ≤ n.val → Reachable (roadData roads) i j →
            resultAt r i ≤ trip (roadData roads) appleCost k.val i j)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
          (roadData roads)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData roads))
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∃ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n roads appleCost k = ok r ∧
          r.val.length = n.val.toNat ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ n.val →
            (∃ j : ℤ, 1 ≤ j ∧ j ≤ n.val ∧ Reachable (roadData roads) i j ∧
              resultAt r i = trip (roadData roads) appleCost k.val i j) ∧
            (∀ j : ℤ, 1 ≤ j → j ≤ n.val → Reachable (roadData roads) i j →
              resultAt r i ≤ trip (roadData roads) appleCost k.val i j))) := by
    sorry

  /-- The function returns a result r; in particular, under these preconditions it does not fail (no arithmetic overflow, panic, or out-of-bounds access).
    Preconditions: Problem constraints hold: 2 <= n <= 1000; roads is a list of length m with 1 <= m <= 2000; each roads[t] is a 3-element vector [a_t,b_t,c_t] with 1 <= a_t,b_t <= n, a_t != b_t, and 1 <= c_t <= 100000; no unordered pair of cities occurs as the endpoints of two different roads; appleCost has length n and 1 <= appleCost[j] <= 100000 for every 0 <= j < n; 1 <= k <= 100. -/
  theorem spec_2
      (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
        (roadData roads)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData roads))
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∃ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n roads appleCost k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
          (roadData roads)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData roads))
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∃ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n roads appleCost k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = n.
    Preconditions: Problem constraints hold: 2 <= n <= 1000; roads is a list of length m with 1 <= m <= 2000; each roads[t] is a 3-element vector [a_t,b_t,c_t] with 1 <= a_t,b_t <= n, a_t != b_t, and 1 <= c_t <= 100000; no unordered pair of cities occurs as the endpoints of two different roads; appleCost has length n and 1 <= appleCost[j] <= 100000 for every 0 <= j < n; 1 <= k <= 100. -/
  theorem spec_3
      (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
        (roadData roads)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData roads))
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n roads appleCost k = ok r → r.val.length = n.val.toNat := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
          (roadData roads)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData roads))
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n roads appleCost k = ok r → r.val.length = n.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i <= n, 1 <= r[i-1] <= appleCost[i-1].
    Preconditions: Problem constraints hold: 2 <= n <= 1000; roads is a list of length m with 1 <= m <= 2000; each roads[t] is a 3-element vector [a_t,b_t,c_t] with 1 <= a_t,b_t <= n, a_t != b_t, and 1 <= c_t <= 100000; no unordered pair of cities occurs as the endpoints of two different roads; appleCost has length n and 1 <= appleCost[j] <= 100000 for every 0 <= j < n; 1 <= k <= 100. -/
  theorem spec_4
      (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
        (roadData roads)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData roads))
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n roads appleCost k = ok r →
        ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
          1 ≤ resultAt r i ∧ resultAt r i ≤ appleAt appleCost i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
          (roadData roads)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData roads))
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n roads appleCost k = ok r →
          ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
            1 ≤ resultAt r i ∧ resultAt r i ≤ appleAt appleCost i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i <= n there exists a city j with 1 <= j <= n such that j is reachable from i (there exists a route from i to j using roads) and r[i-1] = (1+k)*d(i,j) + appleCost[j-1], where d(i,j) is the least total road cost of any route from i to j.
    Preconditions: Problem constraints hold: 2 <= n <= 1000; roads is a list of length m with 1 <= m <= 2000; each roads[t] is a 3-element vector [a_t,b_t,c_t] with 1 <= a_t,b_t <= n, a_t != b_t, and 1 <= c_t <= 100000; no unordered pair of cities occurs as the endpoints of two different roads; appleCost has length n and 1 <= appleCost[j] <= 100000 for every 0 <= j < n; 1 <= k <= 100. -/
  theorem spec_5
      (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
        (roadData roads)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData roads))
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n roads appleCost k = ok r →
        ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
          ∃ j : ℤ, 1 ≤ j ∧ j ≤ n.val ∧ Reachable (roadData roads) i j ∧
            resultAt r i = trip (roadData roads) appleCost k.val i j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
          (roadData roads)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData roads))
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n roads appleCost k = ok r →
          ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
            ∃ j : ℤ, 1 ≤ j ∧ j ≤ n.val ∧ Reachable (roadData roads) i j ∧
              resultAt r i = trip (roadData roads) appleCost k.val i j) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i <= n and every city j with 1 <= j <= n that is reachable from i (there exists a route from i to j using roads), r[i-1] <= (1+k)*d(i,j) + appleCost[j-1], where d(i,j) is the least total road cost of any route from i to j.
    Preconditions: Problem constraints hold: 2 <= n <= 1000; roads is a list of length m with 1 <= m <= 2000; each roads[t] is a 3-element vector [a_t,b_t,c_t] with 1 <= a_t,b_t <= n, a_t != b_t, and 1 <= c_t <= 100000; no unordered pair of cities occurs as the endpoints of two different roads; appleCost has length n and 1 <= appleCost[j] <= 100000 for every 0 <= j < n; 1 <= k <= 100. -/
  theorem spec_6
      (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
        (roadData roads)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData roads))
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n roads appleCost k = ok r →
        ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
          ∀ j : ℤ, 1 ≤ j → j ≤ n.val → Reachable (roadData roads) i j →
            resultAt r i ≤ trip (roadData roads) appleCost k.val i j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
          (roadData roads)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData roads))
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n roads appleCost k = ok r →
          ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
            ∀ j : ℤ, 1 ≤ j → j ≤ n.val → Reachable (roadData roads) i j →
              resultAt r i ≤ trip (roadData roads) appleCost k.val i j) := by
    sorry

  /-- Whenever the function returns a result r, for every city i with 1 <= i <= n, r[i-1] = appleCost[i-1] if and only if for every city j reachable from i (there exists a route from i to j using roads), appleCost[i-1] <= (1+k)*d(i,j) + appleCost[j-1], where d(i,j) is the least total road cost of any route from i to j.
    Preconditions: Problem constraints hold: 2 <= n <= 1000; roads is a list of length m with 1 <= m <= 2000; each roads[t] is a 3-element vector [a_t,b_t,c_t] with 1 <= a_t,b_t <= n, a_t != b_t, and 1 <= c_t <= 100000; no unordered pair of cities occurs as the endpoints of two different roads; appleCost has length n and 1 <= appleCost[j] <= 100000 for every 0 <= j < n; 1 <= k <= 100. -/
  theorem spec_7
      (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
        (roadData roads)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData roads))
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n roads appleCost k = ok r →
        ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
          (resultAt r i = appleAt appleCost i ↔
            ∀ j : ℤ, 1 ≤ j → j ≤ n.val → Reachable (roadData roads) i j →
              appleAt appleCost i ≤ trip (roadData roads) appleCost k.val i j) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
          (roadData roads)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData roads))
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n roads appleCost k = ok r →
          ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
            (resultAt r i = appleAt appleCost i ↔
              ∀ j : ℤ, 1 ≤ j → j ≤ n.val → Reachable (roadData roads) i j →
                appleAt appleCost i ≤ trip (roadData roads) appleCost k.val i j)) := by
    sorry

  /-- Whenever the function returns a result r, for every city i with 1 <= i <= n such that for every t with 0 <= t < len(roads), roads[t][0] != i and roads[t][1] != i, it holds that r[i-1] = appleCost[i-1].
    Preconditions: Problem constraints hold: 2 <= n <= 1000; roads is a list of length m with 1 <= m <= 2000; each roads[t] is a 3-element vector [a_t,b_t,c_t] with 1 <= a_t,b_t <= n, a_t != b_t, and 1 <= c_t <= 100000; no unordered pair of cities occurs as the endpoints of two different roads; appleCost has length n and 1 <= appleCost[j] <= 100000 for every 0 <= j < n; 1 <= k <= 100. -/
  theorem spec_8
      (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
        (roadData roads)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData roads))
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n roads appleCost k = ok r →
        ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
          (∀ (t : ℕ) (a b c : ℤ),
              (roadData roads)[t]? = some [a, b, c] → a ≠ i ∧ b ≠ i) →
            resultAt r i = appleAt appleCost i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
          (roadData roads)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData roads))
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n roads appleCost k = ok r →
          ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
            (∀ (t : ℕ) (a b c : ℤ),
                (roadData roads)[t]? = some [a, b, c] → a ≠ i ∧ b ≠ i) →
              resultAt r i = appleAt appleCost i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i <= n, r[i-1] = c.
    Preconditions: Problem constraints hold: 2 <= n <= 1000; roads is a list of length m with 1 <= m <= 2000; each roads[t] is a 3-element vector [a_t,b_t,c_t] with 1 <= a_t,b_t <= n, a_t != b_t, and 1 <= c_t <= 100000; no unordered pair of cities occurs as the endpoints of two different roads; appleCost has length n; 1 <= k <= 100. Additionally, there exists an integer c with 1 <= c <= 100000 such that appleCost[j] = c for every j with 0 <= j < n. -/
  theorem spec_9
      (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (c : ℤ)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c' : ℤ,
        (roadData roads)[t]? = some [a, b, c'] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c' ∧ c' ≤ 100000)
      (h_simple : NoMultiedge (roadData roads))
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_c_lo : 1 ≤ c) (h_c_hi : c ≤ 100000)
      (h_apple_const : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        appleCost.val[j].val = c)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∀ r : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n roads appleCost k = ok r →
        ∀ i : ℤ, 1 ≤ i → i ≤ n.val → resultAt r i = c := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (c : ℤ)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c' : ℤ,
          (roadData roads)[t]? = some [a, b, c'] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c' ∧ c' ≤ 100000)
        (h_simple : NoMultiedge (roadData roads))
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_c_lo : 1 ≤ c) (h_c_hi : c ≤ 100000)
        (h_apple_const : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          appleCost.val[j].val = c)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n roads appleCost k = ok r →
          ∀ i : ℤ, 1 ≤ i → i ≤ n.val → resultAt r i = c) := by
    sorry

  /-- Whenever the function returns results r1 and r2 on these two inputs, for every i with 1 <= i <= n, r1[i-1] <= r2[i-1].
    Preconditions: Two runs satisfy the problem constraints with the same n, roads, and appleCost, and with multipliers k1 and k2 such that 1 <= k1 <= k2 <= 100. -/
  theorem spec_10
      (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k1 k2 : Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
        (roadData roads)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData roads))
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
      (h_k1_lo : 1 ≤ k1.val) (h_k1_hi : k1.val ≤ 100)
      (h_k2_lo : 1 ≤ k2.val) (h_k2_hi : k2.val ≤ 100)
      (h_k_le : k1.val ≤ k2.val) :
      ∀ r1 r2 : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n roads appleCost k1 = ok r1 →
        Aegis.MinCost.min_cost n roads appleCost k2 = ok r2 →
        ∀ i : ℤ, 1 ≤ i → i ≤ n.val → resultAt r1 i ≤ resultAt r2 i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k1 k2 : Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
          (roadData roads)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData roads))
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
        (h_k1_lo : 1 ≤ k1.val) (h_k1_hi : k1.val ≤ 100)
        (h_k2_lo : 1 ≤ k2.val) (h_k2_hi : k2.val ≤ 100)
        (h_k_le : k1.val ≤ k2.val), ∀ r1 r2 : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n roads appleCost k1 = ok r1 →
          Aegis.MinCost.min_cost n roads appleCost k2 = ok r2 →
          ∀ i : ℤ, 1 ≤ i → i ≤ n.val → resultAt r1 i ≤ resultAt r2 i) := by
    sorry

  /-- Whenever the function returns results rA and rB on these two inputs, for every i with 1 <= i <= n, rA[i-1] <= rB[i-1].
    Preconditions: Two runs satisfy the problem constraints with the same n, roads, and k, and with apple cost arrays A and B, both of length n, such that A[j] <= B[j] for every j with 0 <= j < n. -/
  theorem spec_11
      (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (k : Aeneas.Std.I64) (A B : Slice Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
        (roadData roads)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData roads))
      (h_A_len : A.val.length = n.val.toNat)
      (h_A_bounds : ∀ (j : ℕ) (hj : j < A.val.length),
        1 ≤ A.val[j].val ∧ A.val[j].val ≤ 100000)
      (h_B_len : B.val.length = n.val.toNat)
      (h_B_bounds : ∀ (j : ℕ) (hj : j < B.val.length),
        1 ≤ B.val[j].val ∧ B.val[j].val ≤ 100000)
      (h_A_le_B : ∀ j : ℤ, 1 ≤ j → j ≤ n.val → appleAt A j ≤ appleAt B j)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∀ rA rB : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n roads A k = ok rA →
        Aegis.MinCost.min_cost n roads B k = ok rB →
        ∀ i : ℤ, 1 ≤ i → i ≤ n.val → resultAt rA i ≤ resultAt rB i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (roads : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (k : Aeneas.Std.I64) (A B : Slice Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ roads.val.length) (h_m_hi : roads.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData roads).length → ∃ a b c : ℤ,
          (roadData roads)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData roads))
        (h_A_len : A.val.length = n.val.toNat)
        (h_A_bounds : ∀ (j : ℕ) (hj : j < A.val.length),
          1 ≤ A.val[j].val ∧ A.val[j].val ≤ 100000)
        (h_B_len : B.val.length = n.val.toNat)
        (h_B_bounds : ∀ (j : ℕ) (hj : j < B.val.length),
          1 ≤ B.val[j].val ∧ B.val[j].val ≤ 100000)
        (h_A_le_B : ∀ j : ℤ, 1 ≤ j → j ≤ n.val → appleAt A j ≤ appleAt B j)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∀ rA rB : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n roads A k = ok rA →
          Aegis.MinCost.min_cost n roads B k = ok rB →
          ∀ i : ℤ, 1 ≤ i → i ≤ n.val → resultAt rA i ≤ resultAt rB i) := by
    sorry

  /-- Whenever the function returns results r and r' on these two inputs, for every i with 1 <= i <= n, r[i-1] <= r'[i-1].
    Preconditions: Two runs satisfy the problem constraints with the same n, k, and appleCost, and with road lists R and R' of the same length m such that for every t with 0 <= t < m, R[t] = [a_t,b_t,c_t] and R'[t] = [a_t,b_t,c'_t] with 1 <= c_t <= c'_t <= 100000, and neither list has a repeated unordered endpoint pair. -/
  theorem spec_12
      (n : Aeneas.Std.I64) (R R' : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ R.val.length) (h_m_hi : R.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData R).length → ∃ a b c : ℤ,
        (roadData R)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData R))
      (h_m'_lo : 1 ≤ R'.val.length) (h_m'_hi : R'.val.length ≤ 2000)
      (h_road' : ∀ t : ℕ, t < (roadData R').length → ∃ a b c : ℤ,
        (roadData R')[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple' : NoMultiedge (roadData R'))
      (h_same_len : R.val.length = R'.val.length)
      (h_pointwise : ∀ t : ℕ, t < (roadData R).length → ∃ a b c c' : ℤ,
        (roadData R)[t]? = some [a, b, c] ∧ (roadData R')[t]? = some [a, b, c'] ∧
          1 ≤ c ∧ c ≤ c' ∧ c' ≤ 100000)
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∀ r r' : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n R appleCost k = ok r →
        Aegis.MinCost.min_cost n R' appleCost k = ok r' →
        ∀ i : ℤ, 1 ≤ i → i ≤ n.val → resultAt r i ≤ resultAt r' i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (R R' : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ R.val.length) (h_m_hi : R.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData R).length → ∃ a b c : ℤ,
          (roadData R)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData R))
        (h_m'_lo : 1 ≤ R'.val.length) (h_m'_hi : R'.val.length ≤ 2000)
        (h_road' : ∀ t : ℕ, t < (roadData R').length → ∃ a b c : ℤ,
          (roadData R')[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple' : NoMultiedge (roadData R'))
        (h_same_len : R.val.length = R'.val.length)
        (h_pointwise : ∀ t : ℕ, t < (roadData R).length → ∃ a b c c' : ℤ,
          (roadData R)[t]? = some [a, b, c] ∧ (roadData R')[t]? = some [a, b, c'] ∧
            1 ≤ c ∧ c ≤ c' ∧ c' ≤ 100000)
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∀ r r' : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n R appleCost k = ok r →
          Aegis.MinCost.min_cost n R' appleCost k = ok r' →
          ∀ i : ℤ, 1 ≤ i → i ≤ n.val → resultAt r i ≤ resultAt r' i) := by
    sorry

  /-- Whenever the function returns results r and r' on these two inputs, len(r)=len(r')=n and r[i-1] = r'[i-1] for every i with 1 <= i <= n.
    Preconditions: Two runs satisfy the problem constraints with the same n, appleCost, and k, and with road lists R and R' that are permutations of one another (they have the same multiset of 3-element roads). -/
  theorem spec_13
      (n : Aeneas.Std.I64) (R R' : Slice (alloc.vec.Vec Aeneas.Std.I64))
      (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
      (h_m_lo : 1 ≤ R.val.length) (h_m_hi : R.val.length ≤ 2000)
      (h_road : ∀ t : ℕ, t < (roadData R).length → ∃ a b c : ℤ,
        (roadData R)[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple : NoMultiedge (roadData R))
      (h_m'_lo : 1 ≤ R'.val.length) (h_m'_hi : R'.val.length ≤ 2000)
      (h_road' : ∀ t : ℕ, t < (roadData R').length → ∃ a b c : ℤ,
        (roadData R')[t]? = some [a, b, c] ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
      (h_simple' : NoMultiedge (roadData R'))
      (h_perm : (roadData R).Perm (roadData R'))
      (h_apple_len : appleCost.val.length = n.val.toNat)
      (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
        1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100) :
      ∀ r r' : alloc.vec.Vec Aeneas.Std.I64,
        Aegis.MinCost.min_cost n R appleCost k = ok r →
        Aegis.MinCost.min_cost n R' appleCost k = ok r' →
        r.val.length = n.val.toNat ∧ r'.val.length = n.val.toNat ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ n.val → resultAt r i = resultAt r' i) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (R R' : Slice (alloc.vec.Vec Aeneas.Std.I64))
        (appleCost : Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 1000)
        (h_m_lo : 1 ≤ R.val.length) (h_m_hi : R.val.length ≤ 2000)
        (h_road : ∀ t : ℕ, t < (roadData R).length → ∃ a b c : ℤ,
          (roadData R)[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple : NoMultiedge (roadData R))
        (h_m'_lo : 1 ≤ R'.val.length) (h_m'_hi : R'.val.length ≤ 2000)
        (h_road' : ∀ t : ℕ, t < (roadData R').length → ∃ a b c : ℤ,
          (roadData R')[t]? = some [a, b, c] ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b ∧ 1 ≤ c ∧ c ≤ 100000)
        (h_simple' : NoMultiedge (roadData R'))
        (h_perm : (roadData R).Perm (roadData R'))
        (h_apple_len : appleCost.val.length = n.val.toNat)
        (h_apple_bounds : ∀ (j : ℕ) (hj : j < appleCost.val.length),
          1 ≤ appleCost.val[j].val ∧ appleCost.val[j].val ≤ 100000)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 100), ∀ r r' : alloc.vec.Vec Aeneas.Std.I64,
          Aegis.MinCost.min_cost n R appleCost k = ok r →
          Aegis.MinCost.min_cost n R' appleCost k = ok r' →
          r.val.length = n.val.toNat ∧ r'.val.length = n.val.toNat ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ n.val → resultAt r i = resultAt r' i)) := by
    sorry

  end AegisSpec.MinCost
