import Aegis.CorpFlightBookings.Code.Funs

/-!
# Specifications of `Aegis.CorpFlightBookings.corp_flight_bookings`

LeetCode problem `corporate-flight-bookings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CorpFlightBookings

  def rows (bookings : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
    bookings.val.map (fun v => v.val)

  def row (bookings : Slice (alloc.vec.Vec I64)) (k : ℕ) : List ℤ :=
    (rows bookings).getD k []

  def rowFirst (r : List ℤ) : ℤ := r.getD 0 0

  def rowLast (r : List ℤ) : ℤ := r.getD 1 0

  def rowSeats (r : List ℤ) : ℤ := r.getD 2 0

  def ansAt (r : alloc.vec.Vec I64) (j : ℕ) : ℤ :=
    (r.val.map (fun x => x.val)).getD j 0

  def coverSum (bookings : Slice (alloc.vec.Vec I64)) (f : ℤ) : ℤ :=
    ∑ k ∈ Finset.range bookings.val.length,
      if rowFirst (row bookings k) ≤ f ∧ f ≤ rowLast (row bookings k)
      then rowSeats (row bookings k) else 0

  def startSum (bookings : Slice (alloc.vec.Vec I64)) (f : ℤ) : ℤ :=
    ∑ k ∈ Finset.range bookings.val.length,
      if rowFirst (row bookings k) = f then rowSeats (row bookings k) else 0

  def endSum (bookings : Slice (alloc.vec.Vec I64)) (f : ℤ) : ℤ :=
    ∑ k ∈ Finset.range bookings.val.length,
      if rowLast (row bookings k) = f then rowSeats (row bookings k) else 0

  def totalSeats (bookings : Slice (alloc.vec.Vec I64)) : ℤ :=
    ∑ k ∈ Finset.range bookings.val.length, rowSeats (row bookings k)

  def weightedSeats (bookings : Slice (alloc.vec.Vec I64)) : ℤ :=
    ∑ k ∈ Finset.range bookings.val.length,
      rowSeats (row bookings k) * (rowLast (row bookings k) - rowFirst (row bookings k) + 1)

  def totalAns (r : alloc.vec.Vec I64) : ℤ :=
    ∑ j ∈ Finset.range r.val.length, ansAt r j

  def Covers (bookings : Slice (alloc.vec.Vec I64)) (f : ℤ) : Prop :=
    ∃ k : ℕ, k < bookings.val.length ∧
      rowFirst (row bookings k) ≤ f ∧ f ≤ rowLast (row bookings k)

  def RowsOK (bookings : Slice (alloc.vec.Vec I64)) (n : I64) : Prop :=
    ∀ k : ℕ, k < bookings.val.length →
      (row bookings k).length = 3 ∧
      1 ≤ rowFirst (row bookings k) ∧
      rowFirst (row bookings k) ≤ rowLast (row bookings k) ∧
      rowLast (row bookings k) ≤ n.val ∧
      1 ≤ rowSeats (row bookings k) ∧
      rowSeats (row bookings k) ≤ 10000

  /-- Whenever the function returns a result r, len(r)=n and, for every j with 0 <= j < n, r[j] = sum over k with 0 <= k < len(bookings) and f_k <= j+1 <= l_k of s_k, where f_k=bookings[k][0], l_k=bookings[k][1], s_k=bookings[k][2].
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. These bounds imply every total seat count is at most 2*10^8, so all mathematical sums below lie in i64 range. -/
  theorem spec_1 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n)
      (r : alloc.vec.Vec I64)
      (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r) :
      (r.val.length : ℤ) = n.val ∧
        ∀ j : ℕ, (j : ℤ) < n.val → ansAt r j = coverSum bookings ((j : ℤ) + 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n)
        (r : alloc.vec.Vec I64)
        (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r), (r.val.length : ℤ) = n.val ∧
          ∀ j : ℕ, (j : ℤ) < n.val → ansAt r j = coverSum bookings ((j : ℤ) + 1)) := by
    sorry

  /-- The function returns a result r (it does not fail) on every input satisfying the preconditions.
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. -/
  theorem spec_2 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n), ∃ r : alloc.vec.Vec I64,
          Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=n, for every j with 0 <= j < n, r[j] >= 0.
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. -/
  theorem spec_3 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n)
      (r : alloc.vec.Vec I64)
      (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
      (hlen : (r.val.length : ℤ) = n.val) :
      ∀ j : ℕ, (j : ℤ) < n.val → 0 ≤ ansAt r j := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n)
        (r : alloc.vec.Vec I64)
        (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
        (hlen : (r.val.length : ℤ) = n.val), ∀ j : ℕ, (j : ℤ) < n.val → 0 ≤ ansAt r j) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=n, for every j with 0 <= j < n, r[j] <= sum over k with 0 <= k < len(bookings) of bookings[k][2].
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. -/
  theorem spec_4 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n)
      (r : alloc.vec.Vec I64)
      (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
      (hlen : (r.val.length : ℤ) = n.val) :
      ∀ j : ℕ, (j : ℤ) < n.val → ansAt r j ≤ totalSeats bookings := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n)
        (r : alloc.vec.Vec I64)
        (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
        (hlen : (r.val.length : ℤ) = n.val), ∀ j : ℕ, (j : ℤ) < n.val → ansAt r j ≤ totalSeats bookings) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=n, for every k with 0 <= k < len(bookings) and every flight f with bookings[k][0] <= f <= bookings[k][1], we have r[f-1] >= bookings[k][2].
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. -/
  theorem spec_5 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n)
      (r : alloc.vec.Vec I64)
      (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
      (hlen : (r.val.length : ℤ) = n.val) :
      ∀ k : ℕ, k < bookings.val.length →
        ∀ f : ℕ, 1 ≤ f →
          rowFirst (row bookings k) ≤ (f : ℤ) → (f : ℤ) ≤ rowLast (row bookings k) →
          rowSeats (row bookings k) ≤ ansAt r (f - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n)
        (r : alloc.vec.Vec I64)
        (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
        (hlen : (r.val.length : ℤ) = n.val), ∀ k : ℕ, k < bookings.val.length →
          ∀ f : ℕ, 1 ≤ f →
            rowFirst (row bookings k) ≤ (f : ℤ) → (f : ℤ) ≤ rowLast (row bookings k) →
            rowSeats (row bookings k) ≤ ansAt r (f - 1)) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=n, for every flight f with 1 <= f <= n, r[f-1] > 0 if and only if there exists k with 0 <= k < len(bookings) such that bookings[k][0] <= f <= bookings[k][1].
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. -/
  theorem spec_6 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n)
      (r : alloc.vec.Vec I64)
      (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
      (hlen : (r.val.length : ℤ) = n.val) :
      ∀ f : ℕ, 1 ≤ f → (f : ℤ) ≤ n.val →
        (0 < ansAt r (f - 1) ↔ Covers bookings (f : ℤ)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n)
        (r : alloc.vec.Vec I64)
        (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
        (hlen : (r.val.length : ℤ) = n.val), ∀ f : ℕ, 1 ≤ f → (f : ℤ) ≤ n.val →
          (0 < ansAt r (f - 1) ↔ Covers bookings (f : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=n, r[0] = sum over k with 0 <= k < len(bookings) and bookings[k][0] = 1 of bookings[k][2].
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. -/
  theorem spec_7 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n)
      (r : alloc.vec.Vec I64)
      (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
      (hlen : (r.val.length : ℤ) = n.val) :
      ansAt r 0 = startSum bookings 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n)
        (r : alloc.vec.Vec I64)
        (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
        (hlen : (r.val.length : ℤ) = n.val), ansAt r 0 = startSum bookings 1) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=n, r[n-1] = sum over k with 0 <= k < len(bookings) and bookings[k][1] = n of bookings[k][2].
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. -/
  theorem spec_8 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n)
      (r : alloc.vec.Vec I64)
      (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
      (hlen : (r.val.length : ℤ) = n.val) :
      ansAt r (n.val.toNat - 1) = endSum bookings n.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n)
        (r : alloc.vec.Vec I64)
        (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
        (hlen : (r.val.length : ℤ) = n.val), ansAt r (n.val.toNat - 1) = endSum bookings n.val) := by
    sorry

  /-- For every split of bookings into two nonempty contiguous parts P and Q with bookings = P ++ Q, if the function returns r on bookings, rP on P, and rQ on Q, and len(r)=len(rP)=len(rQ)=n, then for every j with 0 <= j < n, r[j] = rP[j] + rQ[j].
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. -/
  theorem spec_9 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n)
      (P Q : Slice (alloc.vec.Vec I64))
      (hsplit : bookings.val = P.val ++ Q.val)
      (hP_ne : 1 ≤ P.val.length) (hQ_ne : 1 ≤ Q.val.length)
      (r rP rQ : alloc.vec.Vec I64)
      (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
      (hrP : Aegis.CorpFlightBookings.corp_flight_bookings P n = ok rP)
      (hrQ : Aegis.CorpFlightBookings.corp_flight_bookings Q n = ok rQ)
      (hlen : (r.val.length : ℤ) = n.val)
      (hlenP : (rP.val.length : ℤ) = n.val)
      (hlenQ : (rQ.val.length : ℤ) = n.val) :
      ∀ j : ℕ, (j : ℤ) < n.val → ansAt r j = ansAt rP j + ansAt rQ j := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n)
        (P Q : Slice (alloc.vec.Vec I64))
        (hsplit : bookings.val = P.val ++ Q.val)
        (hP_ne : 1 ≤ P.val.length) (hQ_ne : 1 ≤ Q.val.length)
        (r rP rQ : alloc.vec.Vec I64)
        (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
        (hrP : Aegis.CorpFlightBookings.corp_flight_bookings P n = ok rP)
        (hrQ : Aegis.CorpFlightBookings.corp_flight_bookings Q n = ok rQ)
        (hlen : (r.val.length : ℤ) = n.val)
        (hlenP : (rP.val.length : ℤ) = n.val)
        (hlenQ : (rQ.val.length : ℤ) = n.val), ∀ j : ℕ, (j : ℤ) < n.val → ansAt r j = ansAt rP j + ansAt rQ j) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=n, for every j with 0 <= j < n-1, r[j+1] - r[j] = (sum over k with 0 <= k < len(bookings) and bookings[k][0] = j+2 of bookings[k][2]) - (sum over k with 0 <= k < len(bookings) and bookings[k][1] = j+1 of bookings[k][2]).
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. -/
  theorem spec_10 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n)
      (r : alloc.vec.Vec I64)
      (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
      (hlen : (r.val.length : ℤ) = n.val) :
      ∀ j : ℕ, (j : ℤ) < n.val - 1 →
        ansAt r (j + 1) - ansAt r j =
          startSum bookings ((j : ℤ) + 2) - endSum bookings ((j : ℤ) + 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n)
        (r : alloc.vec.Vec I64)
        (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
        (hlen : (r.val.length : ℤ) = n.val), ∀ j : ℕ, (j : ℤ) < n.val - 1 →
          ansAt r (j + 1) - ansAt r j =
            startSum bookings ((j : ℤ) + 2) - endSum bookings ((j : ℤ) + 1)) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=n, sum over j with 0 <= j < n of r[j] = sum over k with 0 <= k < len(bookings) of bookings[k][2] * (bookings[k][1] - bookings[k][0] + 1).
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. -/
  theorem spec_11 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n)
      (r : alloc.vec.Vec I64)
      (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
      (hlen : (r.val.length : ℤ) = n.val) :
      totalAns r = weightedSeats bookings := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n)
        (r : alloc.vec.Vec I64)
        (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
        (hlen : (r.val.length : ℤ) = n.val), totalAns r = weightedSeats bookings) := by
    sorry

  /-- For every permutation bookings' of the rows of bookings (same length and same multiset of three-element rows), if the function returns r on bookings and r' on bookings' and len(r)=len(r')=n, then for every j with 0 <= j < n, r[j] = r'[j].
    Preconditions: n is an integer with 1 <= n <= 20000; bookings is a slice of vectors with 1 <= len(bookings) <= 20000; for every k with 0 <= k < len(bookings), len(bookings[k]) = 3, and, writing f_k = bookings[k][0], l_k = bookings[k][1], s_k = bookings[k][2], we have 1 <= f_k <= l_k <= n and 1 <= s_k <= 10000. -/
  theorem spec_12 (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
      (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
      (hrows : RowsOK bookings n)
      (bookings' : Slice (alloc.vec.Vec I64))
      (hperm : (rows bookings').Perm (rows bookings))
      (r r' : alloc.vec.Vec I64)
      (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
      (hr' : Aegis.CorpFlightBookings.corp_flight_bookings bookings' n = ok r')
      (hlen : (r.val.length : ℤ) = n.val)
      (hlen' : (r'.val.length : ℤ) = n.val) :
      ∀ j : ℕ, (j : ℤ) < n.val → ansAt r j = ansAt r' j := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (bookings : Slice (alloc.vec.Vec I64)) (n : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 20000)
        (hb_lo : 1 ≤ bookings.val.length) (hb_hi : bookings.val.length ≤ 20000)
        (hrows : RowsOK bookings n)
        (bookings' : Slice (alloc.vec.Vec I64))
        (hperm : (rows bookings').Perm (rows bookings))
        (r r' : alloc.vec.Vec I64)
        (hr : Aegis.CorpFlightBookings.corp_flight_bookings bookings n = ok r)
        (hr' : Aegis.CorpFlightBookings.corp_flight_bookings bookings' n = ok r')
        (hlen : (r.val.length : ℤ) = n.val)
        (hlen' : (r'.val.length : ℤ) = n.val), ∀ j : ℕ, (j : ℤ) < n.val → ansAt r j = ansAt r' j) := by
    sorry

  end AegisSpec.CorpFlightBookings
