import Aegis.FilterRestaurants.Code.Funs

/-!
# Specifications of `Aegis.FilterRestaurants.filter_restaurants`

LeetCode problem `filter-restaurants-by-vegan-friendly-price-and-distance`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FilterRestaurants

  def vecGet (r : alloc.vec.Vec Std.I64) (k : Nat) : Int :=
    match r.val[k]? with
    | some x => x.val
    | none => 0

  def fieldAt (rows : Slice (alloc.vec.Vec Std.I64)) (i k : Nat) : Int :=
    match rows.val[i]? with
    | some row => vecGet row k
    | none => 0

  def idOf (rows : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int := fieldAt rows i 0

  def ratingOf (rows : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int := fieldAt rows i 1

  def veganOf (rows : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int := fieldAt rows i 2

  def priceOf (rows : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int := fieldAt rows i 3

  def distOf (rows : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int := fieldAt rows i 4

  def Occurs (r : alloc.vec.Vec Std.I64) (x : Int) : Prop :=
    ∃ k, k < r.val.length ∧ vecGet r k = x

  def OccursExactlyOnce (r : alloc.vec.Vec Std.I64) (x : Int) : Prop :=
    ∃ k, k < r.val.length ∧ vecGet r k = x ∧
      ∀ l, l < r.val.length → vecGet r l = x → l = k

  def InE (rows : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64) (i : Nat) : Prop :=
    i < rows.val.length ∧ priceOf rows i ≤ maxPrice.val ∧
      distOf rows i ≤ maxDistance.val ∧ (veganFriendly.val = 0 ∨ veganOf rows i = 1)

  noncomputable def E (rows : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64) : Finset Nat := by
    classical
    exact (Finset.range rows.val.length).filter
      (fun i => InE rows veganFriendly maxPrice maxDistance i)

  structure InputOK (rows : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64) : Prop where

    rows_len_lo : 1 ≤ rows.val.length

    rows_len_hi : rows.val.length ≤ 10000

    row_len : ∀ (i : Nat) (h : i < rows.val.length), (rows.val[i]).val.length = 5

    id_bounds : ∀ i, i < rows.val.length → 1 ≤ idOf rows i ∧ idOf rows i ≤ 100000

    rating_bounds : ∀ i, i < rows.val.length → 1 ≤ ratingOf rows i ∧ ratingOf rows i ≤ 100000

    vegan_bounds : ∀ i, i < rows.val.length → veganOf rows i = 0 ∨ veganOf rows i = 1

    price_bounds : ∀ i, i < rows.val.length → 1 ≤ priceOf rows i ∧ priceOf rows i ≤ 100000

    dist_bounds : ∀ i, i < rows.val.length → 1 ≤ distOf rows i ∧ distOf rows i ≤ 100000

    ids_distinct : ∀ i j, i < rows.val.length → j < rows.val.length →
      idOf rows i = idOf rows j → i = j

    veganFriendly_bounds : veganFriendly.val = 0 ∨ veganFriendly.val = 1

    maxPrice_bounds : 1 ≤ maxPrice.val ∧ maxPrice.val ≤ 100000

    maxDistance_bounds : 1 ≤ maxDistance.val ∧ maxDistance.val ≤ 100000

  /-- Define E = { i | 0 <= i < len(rows), price_i <= maxPrice, dist_i <= maxDistance, and (veganFriendly = 0 or vf_i = 1) }. The function returns a result r (it does not fail) such that: (a) len(r) = |E|; (b) for every k with 0 <= k < len(r), there is i in E with r[k] = id_i; (c) for every i in E, id_i occurs exactly once in r; (d) for every a,b with 0 <= a < b < len(r), if i,j are the unique indices with id_i = r[a] and id_j = r[b], then rating_i > rating_j, or rating_i = rating_j and id_i > id_j.
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_1
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∃ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r ∧
        r.val.length = (E restaurants veganFriendly maxPrice maxDistance).card ∧
        (∀ k, k < r.val.length →
          ∃ i, InE restaurants veganFriendly maxPrice maxDistance i ∧
            vecGet r k = idOf restaurants i) ∧
        (∀ i, InE restaurants veganFriendly maxPrice maxDistance i →
          OccursExactlyOnce r (idOf restaurants i)) ∧
        (∀ a b i j, a < b → b < r.val.length →
          i < restaurants.val.length → j < restaurants.val.length →
          vecGet r a = idOf restaurants i → vecGet r b = idOf restaurants j →
          ratingOf restaurants i > ratingOf restaurants j ∨
            (ratingOf restaurants i = ratingOf restaurants j ∧
              idOf restaurants i > idOf restaurants j)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∃ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r ∧
          r.val.length = (E restaurants veganFriendly maxPrice maxDistance).card ∧
          (∀ k, k < r.val.length →
            ∃ i, InE restaurants veganFriendly maxPrice maxDistance i ∧
              vecGet r k = idOf restaurants i) ∧
          (∀ i, InE restaurants veganFriendly maxPrice maxDistance i →
            OccursExactlyOnce r (idOf restaurants i)) ∧
          (∀ a b i j, a < b → b < r.val.length →
            i < restaurants.val.length → j < restaurants.val.length →
            vecGet r a = idOf restaurants i → vecGet r b = idOf restaurants j →
            ratingOf restaurants i > ratingOf restaurants j ∨
              (ratingOf restaurants i = ratingOf restaurants j ∧
                idOf restaurants i > idOf restaurants j))) := by
    sorry

  /-- Whenever the preconditions hold, the function returns a result r and does not fail: there is no panic, no out-of-bounds access, and no arithmetic overflow.
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_2
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∃ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∃ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r) := by
    sorry

  /-- Let E = { i | 0 <= i < len(rows), price_i <= maxPrice, dist_i <= maxDistance, and (veganFriendly = 0 or vf_i = 1) }. Whenever the function returns r, len(r) = |E|.
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_3
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        r.val.length = (E restaurants veganFriendly maxPrice maxDistance).card := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          r.val.length = (E restaurants veganFriendly maxPrice maxDistance).card) := by
    sorry

  /-- Let E = { i | 0 <= i < len(rows), price_i <= maxPrice, dist_i <= maxDistance, and (veganFriendly = 0 or vf_i = 1) }. Whenever the function returns r, for every k with 0 <= k < len(r), there exists i in E such that r[k] = id_i.
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_4
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        ∀ k, k < r.val.length →
          ∃ i, InE restaurants veganFriendly maxPrice maxDistance i ∧
            vecGet r k = idOf restaurants i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          ∀ k, k < r.val.length →
            ∃ i, InE restaurants veganFriendly maxPrice maxDistance i ∧
              vecGet r k = idOf restaurants i) := by
    sorry

  /-- Let E = { i | 0 <= i < len(rows), price_i <= maxPrice, dist_i <= maxDistance, and (veganFriendly = 0 or vf_i = 1) }. Whenever the function returns r, for every i in E there exists k with 0 <= k < len(r) and r[k] = id_i.
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_5
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        ∀ i, InE restaurants veganFriendly maxPrice maxDistance i →
          Occurs r (idOf restaurants i) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          ∀ i, InE restaurants veganFriendly maxPrice maxDistance i →
            Occurs r (idOf restaurants i)) := by
    sorry

  /-- For any value x occurring in r, let ratingOf(x) be rating_i for the unique i with id_i = x. Whenever the function returns r, for every a,b with 0 <= a < b < len(r), ratingOf(r[a]) >= ratingOf(r[b]).
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_6
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        ∀ a b i j, a < b → b < r.val.length →
          i < restaurants.val.length → j < restaurants.val.length →
          vecGet r a = idOf restaurants i → vecGet r b = idOf restaurants j →
          ratingOf restaurants i ≥ ratingOf restaurants j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          ∀ a b i j, a < b → b < r.val.length →
            i < restaurants.val.length → j < restaurants.val.length →
            vecGet r a = idOf restaurants i → vecGet r b = idOf restaurants j →
            ratingOf restaurants i ≥ ratingOf restaurants j) := by
    sorry

  /-- For any value x occurring in r, let ratingOf(x) be rating_i for the unique i with id_i = x. Whenever the function returns r, for every a,b with 0 <= a < b < len(r), if ratingOf(r[a]) = ratingOf(r[b]), then r[a] > r[b].
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_7
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        ∀ a b i j, a < b → b < r.val.length →
          i < restaurants.val.length → j < restaurants.val.length →
          vecGet r a = idOf restaurants i → vecGet r b = idOf restaurants j →
          ratingOf restaurants i = ratingOf restaurants j → vecGet r a > vecGet r b := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          ∀ a b i j, a < b → b < r.val.length →
            i < restaurants.val.length → j < restaurants.val.length →
            vecGet r a = idOf restaurants i → vecGet r b = idOf restaurants j →
            ratingOf restaurants i = ratingOf restaurants j → vecGet r a > vecGet r b) := by
    sorry

  /-- Whenever the function returns r, for every a,b with 0 <= a < b < len(r), r[a] != r[b].
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_8
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        ∀ a b, a < b → b < r.val.length → vecGet r a ≠ vecGet r b := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          ∀ a b, a < b → b < r.val.length → vecGet r a ≠ vecGet r b) := by
    sorry

  /-- For any value x occurring in r, let priceOf(x) be price_i for the unique i with id_i = x. Whenever the function returns r, for every k with 0 <= k < len(r), priceOf(r[k]) <= maxPrice.
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_9
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        ∀ k, k < r.val.length →
          ∀ i, i < restaurants.val.length → vecGet r k = idOf restaurants i →
            priceOf restaurants i ≤ maxPrice.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          ∀ k, k < r.val.length →
            ∀ i, i < restaurants.val.length → vecGet r k = idOf restaurants i →
              priceOf restaurants i ≤ maxPrice.val) := by
    sorry

  /-- For any value x occurring in r, let distOf(x) be dist_i for the unique i with id_i = x. Whenever the function returns r, for every k with 0 <= k < len(r), distOf(r[k]) <= maxDistance.
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_10
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        ∀ k, k < r.val.length →
          ∀ i, i < restaurants.val.length → vecGet r k = idOf restaurants i →
            distOf restaurants i ≤ maxDistance.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          ∀ k, k < r.val.length →
            ∀ i, i < restaurants.val.length → vecGet r k = idOf restaurants i →
              distOf restaurants i ≤ maxDistance.val) := by
    sorry

  /-- For any value x occurring in r, let vfOf(x) be vf_i for the unique i with id_i = x. Whenever the function returns r and veganFriendly = 1, for every k with 0 <= k < len(r), vfOf(r[k]) = 1.
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_11
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        veganFriendly.val = 1 →
          ∀ k, k < r.val.length →
            ∀ i, i < restaurants.val.length → vecGet r k = idOf restaurants i →
              veganOf restaurants i = 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          veganFriendly.val = 1 →
            ∀ k, k < r.val.length →
              ∀ i, i < restaurants.val.length → vecGet r k = idOf restaurants i →
                veganOf restaurants i = 1) := by
    sorry

  /-- Whenever the function returns r and veganFriendly = 0, for every i with 0 <= i < len(rows), price_i <= maxPrice, and dist_i <= maxDistance, id_i occurs in r.
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_12
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        veganFriendly.val = 0 →
          ∀ i, i < restaurants.val.length → priceOf restaurants i ≤ maxPrice.val →
            distOf restaurants i ≤ maxDistance.val → Occurs r (idOf restaurants i) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          veganFriendly.val = 0 →
            ∀ i, i < restaurants.val.length → priceOf restaurants i ≤ maxPrice.val →
              distOf restaurants i ≤ maxDistance.val → Occurs r (idOf restaurants i)) := by
    sorry

  /-- Whenever the function returns r, len(r) = 0 if and only if there is no i with 0 <= i < len(rows), price_i <= maxPrice, dist_i <= maxDistance, and (veganFriendly = 0 or vf_i = 1).
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_13
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        (r.val.length = 0 ↔
          ¬ ∃ i, InE restaurants veganFriendly maxPrice maxDistance i) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          (r.val.length = 0 ↔
            ¬ ∃ i, InE restaurants veganFriendly maxPrice maxDistance i)) := by
    sorry

  /-- Let E = { i | 0 <= i < len(rows), price_i <= maxPrice, dist_i <= maxDistance, and (veganFriendly = 0 or vf_i = 1) }. Whenever the function returns r and len(r) > 0, let i be the unique index with id_i = r[0]. Then rating_i is maximum among { rating_j | j in E }, and among all j in E with rating_j = rating_i, id_i is maximum.
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_14
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        0 < r.val.length →
          ∀ i, i < restaurants.val.length → idOf restaurants i = vecGet r 0 →
            (∀ j, InE restaurants veganFriendly maxPrice maxDistance j →
              ratingOf restaurants j ≤ ratingOf restaurants i) ∧
            (∀ j, InE restaurants veganFriendly maxPrice maxDistance j →
              ratingOf restaurants j = ratingOf restaurants i →
                idOf restaurants j ≤ idOf restaurants i) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          0 < r.val.length →
            ∀ i, i < restaurants.val.length → idOf restaurants i = vecGet r 0 →
              (∀ j, InE restaurants veganFriendly maxPrice maxDistance j →
                ratingOf restaurants j ≤ ratingOf restaurants i) ∧
              (∀ j, InE restaurants veganFriendly maxPrice maxDistance j →
                ratingOf restaurants j = ratingOf restaurants i →
                  idOf restaurants j ≤ idOf restaurants i)) := by
    sorry

  /-- Let E = { i | 0 <= i < len(rows), price_i <= maxPrice, dist_i <= maxDistance, and (veganFriendly = 0 or vf_i = 1) }. Whenever the function returns r, for any i,j in E and any a,b with 0 <= a,b < len(r), r[a] = id_i, and r[b] = id_j, the following hold: if rating_i > rating_j then a < b; and if rating_i = rating_j and id_i > id_j then a < b.
    Preconditions: Let rows = restaurants. Assume the problem constraints: 1 <= len(rows) <= 10000; for every i with 0 <= i < len(rows), len(rows[i]) = 5 and rows[i] has the form [id_i, rating_i, vf_i, price_i, dist_i] with 1 <= id_i, rating_i, price_i, dist_i <= 100000 and vf_i in {0,1}; all id_i are pairwise distinct; veganFriendly in {0,1}; and 1 <= maxPrice, maxDistance <= 100000. -/
  theorem spec_15
      (restaurants : Slice (alloc.vec.Vec Std.I64))
      (veganFriendly maxPrice maxDistance : Std.I64)
      (h : InputOK restaurants veganFriendly maxPrice maxDistance) :
      ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
            maxDistance = ok r →
        ∀ i j, InE restaurants veganFriendly maxPrice maxDistance i →
          InE restaurants veganFriendly maxPrice maxDistance j →
          ∀ a b, a < r.val.length → b < r.val.length →
            vecGet r a = idOf restaurants i → vecGet r b = idOf restaurants j →
            (ratingOf restaurants i > ratingOf restaurants j → a < b) ∧
            (ratingOf restaurants i = ratingOf restaurants j →
              idOf restaurants i > idOf restaurants j → a < b) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (restaurants : Slice (alloc.vec.Vec Std.I64))
        (veganFriendly maxPrice maxDistance : Std.I64)
        (h : InputOK restaurants veganFriendly maxPrice maxDistance), ∀ r, Aegis.FilterRestaurants.filter_restaurants restaurants veganFriendly maxPrice
              maxDistance = ok r →
          ∀ i j, InE restaurants veganFriendly maxPrice maxDistance i →
            InE restaurants veganFriendly maxPrice maxDistance j →
            ∀ a b, a < r.val.length → b < r.val.length →
              vecGet r a = idOf restaurants i → vecGet r b = idOf restaurants j →
              (ratingOf restaurants i > ratingOf restaurants j → a < b) ∧
              (ratingOf restaurants i = ratingOf restaurants j →
                idOf restaurants i > idOf restaurants j → a < b)) := by
    sorry

  end AegisSpec.FilterRestaurants
