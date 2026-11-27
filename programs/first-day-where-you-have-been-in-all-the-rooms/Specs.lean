import Aegis.FirstDayBeenInAllRooms.Code.Funs

/-!
# Specifications of `Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms`

LeetCode problem `first-day-where-you-have-been-in-all-the-rooms`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FirstDayBeenInAllRooms

def values (nextVisit : Slice I64) : List ℤ :=
  nextVisit.val.map (fun x => x.val)

def nextRoom (nv : List ℤ) (n : ℕ) (cnt : ℕ → ℕ) (r : ℕ) : ℕ :=
  if cnt r % 2 = 1 then (nv.getD r 0).toNat else (r + 1) % n

def stepState (nv : List ℤ) (n : ℕ) (s : ℕ × (ℕ → ℕ)) : ℕ × (ℕ → ℕ) :=
  let r := s.1
  let cnt := s.2
  let r' := nextRoom nv n cnt r
  (r', fun j => cnt j + if j = r' then 1 else 0)

def initState : ℕ × (ℕ → ℕ) :=
  (0, fun j => if j = 0 then 1 else 0)

def roomSeq (nv : List ℤ) (n : ℕ) : ℕ → ℕ :=
  fun d => ((stepState nv n)^[d] initState).1

def visitCount (nv : List ℤ) (n : ℕ) (d j : ℕ) : ℕ :=
  ((stepState nv n)^[d] initState).2 j

def Visited (a : ℕ → ℕ) (j d : ℕ) : Prop :=
  ∃ k, k ≤ d ∧ a k = j

def AllVisited (a : ℕ → ℕ) (n d : ℕ) : Prop :=
  ∀ j, j < n → Visited a j d

def IsFirstCoverDay (a : ℕ → ℕ) (n d : ℕ) : Prop :=
  AllVisited a n d ∧ ∀ d', d' < d → ¬ AllVisited a n d'

def IsFirstVisitDay (a : ℕ → ℕ) (j d : ℕ) : Prop :=
  a d = j ∧ ∀ d', d' < d → a d' ≠ j

/-- Define the infinite room sequence (a_d) by a_0 = 0, and for each d >= 0, if the number of indices k with 0 <= k <= d and a_k = a_d is odd, set a_{d+1} = nextVisit[a_d]; otherwise set a_{d+1} = (a_d + 1) mod n. Let D be the least day d >= 0 such that for every room j with 0 <= j < n there exists k with 0 <= k <= d and a_k = j. Then the function returns a result r (it does not fail) and r = D mod 1000000007, with 0 <= r < 1000000007.
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, and for every i with 0 <= i < n, 0 <= nextVisit[i] <= i. -/
theorem spec_1 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)) :
    ∀ D : ℕ,
      IsFirstCoverDay (roomSeq (values nextVisit) nextVisit.val.length)
          nextVisit.val.length D →
        ∃ r : I64,
          Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
            r.val = (D : ℤ) % 1000000007 ∧ 0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)), ∀ D : ℕ,
      IsFirstCoverDay (roomSeq (values nextVisit) nextVisit.val.length)
          nextVisit.val.length D →
        ∃ r : I64,
          Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
            r.val = (D : ℤ) % 1000000007 ∧ 0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, no out-of-bounds access, and no arithmetic overflow).
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, and for every i with 0 <= i < n, 0 <= nextVisit[i] <= i. -/
theorem spec_2 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)) :
    ∃ r : I64, Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)), ∃ r : I64, Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < 1000000007.
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, and for every i with 0 <= i < n, 0 <= nextVisit[i] <= i. -/
theorem spec_3 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)) :
    ∀ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)), ∀ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r →
        0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- Let D be the least day on which every room 0..n-1 has been visited. Whenever the function returns a result r, r = D mod 1000000007 and D >= 2*(n-1).
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, and for every i with 0 <= i < n, 0 <= nextVisit[i] <= i. -/
theorem spec_4 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)) :
    ∀ D : ℕ,
      IsFirstCoverDay (roomSeq (values nextVisit) nextVisit.val.length)
          nextVisit.val.length D →
        ∀ r : I64,
          Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r →
            r.val = (D : ℤ) % 1000000007 ∧
              2 * ((nextVisit.val.length : ℤ) - 1) ≤ (D : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)), ∀ D : ℕ,
      IsFirstCoverDay (roomSeq (values nextVisit) nextVisit.val.length)
          nextVisit.val.length D →
        ∀ r : I64,
          Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r →
            r.val = (D : ℤ) % 1000000007 ∧
              2 * ((nextVisit.val.length : ℤ) - 1) ≤ (D : ℤ)) := by
  sorry

/-- Let D be the least day on which every room 0..n-1 has been visited. Then the room visited on day D is n-1, and equivalently D is the least day d on which room n-1 is visited. For the returned value r, r = D mod 1000000007.
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, and for every i with 0 <= i < n, 0 <= nextVisit[i] <= i. -/
theorem spec_5 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)) :
    ∀ D : ℕ,
      IsFirstCoverDay (roomSeq (values nextVisit) nextVisit.val.length)
          nextVisit.val.length D →
        roomSeq (values nextVisit) nextVisit.val.length D = nextVisit.val.length - 1 ∧
          (∀ d : ℕ,
            IsFirstVisitDay (roomSeq (values nextVisit) nextVisit.val.length)
                (nextVisit.val.length - 1) d ↔
              d = D) ∧
          ∀ r : I64,
            Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r →
              r.val = (D : ℤ) % 1000000007 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)), ∀ D : ℕ,
      IsFirstCoverDay (roomSeq (values nextVisit) nextVisit.val.length)
          nextVisit.val.length D →
        roomSeq (values nextVisit) nextVisit.val.length D = nextVisit.val.length - 1 ∧
          (∀ d : ℕ,
            IsFirstVisitDay (roomSeq (values nextVisit) nextVisit.val.length)
                (nextVisit.val.length - 1) d ↔
              d = D) ∧
          ∀ r : I64,
            Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r →
              r.val = (D : ℤ) % 1000000007) := by
  sorry

/-- The function returns r = 2.
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, for every i with 0 <= i < n, 0 <= nextVisit[i] <= i, and n = 2. -/
theorem spec_6 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ))
    (hlen : nextVisit.val.length = 2) :
    ∃ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
        r.val = 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ))
    (hlen : nextVisit.val.length = 2), ∃ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
        r.val = 2) := by
  sorry

/-- The function returns r = 2*(n-1).
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, and for every i with 0 <= i < n, nextVisit[i] = i. -/
theorem spec_7 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hconst : ∀ i : ℕ, i < nextVisit.val.length → (values nextVisit).getD i 0 = (i : ℤ)) :
    ∃ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
        r.val = 2 * ((nextVisit.val.length : ℤ) - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hconst : ∀ i : ℕ, i < nextVisit.val.length → (values nextVisit).getD i 0 = (i : ℤ)), ∃ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
        r.val = 2 * ((nextVisit.val.length : ℤ) - 1)) := by
  sorry

/-- The function returns r = (2^n - 2) mod 1000000007, i.e. r is the unique integer with 0 <= r < 1000000007 and r ≡ 2^n - 2 (mod 1000000007).
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, and for every i with 0 <= i < n, nextVisit[i] = 0. -/
theorem spec_8 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hconst : ∀ i : ℕ, i < nextVisit.val.length → (values nextVisit).getD i 0 = 0) :
    ∃ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          r.val = ((2 : ℤ) ^ nextVisit.val.length - 2) % 1000000007 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hconst : ∀ i : ℕ, i < nextVisit.val.length → (values nextVisit).getD i 0 = 0), ∃ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          r.val = ((2 : ℤ) ^ nextVisit.val.length - 2) % 1000000007) := by
  sorry

/-- The function returns r = 6.
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, for every i with 0 <= i < n, 0 <= nextVisit[i] <= i, and in addition n = 3 and nextVisit[1] = 0. -/
theorem spec_9 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ))
    (hlen : nextVisit.val.length = 3)
    (h1 : (values nextVisit).getD 1 0 = 0) :
    ∃ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
        r.val = 6 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ))
    (hlen : nextVisit.val.length = 3)
    (h1 : (values nextVisit).getD 1 0 = 0), ∃ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
        r.val = 6) := by
  sorry

/-- The function returns r = 4.
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, for every i with 0 <= i < n, 0 <= nextVisit[i] <= i, and in addition n = 3 and nextVisit[1] = 1. -/
theorem spec_10 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ))
    (hlen : nextVisit.val.length = 3)
    (h1 : (values nextVisit).getD 1 0 = 1) :
    ∃ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
        r.val = 4 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ))
    (hlen : nextVisit.val.length = 3)
    (h1 : (values nextVisit).getD 1 0 = 1), ∃ r : I64,
      Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r ∧
        r.val = 4) := by
  sorry

/-- Let j be any integer with 0 <= j <= n-1, and let nextVisit' be the slice with nextVisit'[i] = nextVisit[i] for 0 <= i < n-1 and nextVisit'[n-1] = j. Whenever first_day_been_in_all_rooms(nextVisit) returns r and first_day_been_in_all_rooms(nextVisit') returns r', we have r = r'.
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, and for every i with 0 <= i < n, 0 <= nextVisit[i] <= i. -/
theorem spec_11 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)) :
    ∀ (j : ℤ) (nextVisit' : Slice I64),
      0 ≤ j → j ≤ (nextVisit.val.length : ℤ) - 1 →
        values nextVisit' = List.set (values nextVisit) (nextVisit.val.length - 1) j →
          ∀ r r' : I64,
            Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r →
              Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit' = ok r' →
                r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)), ∀ (j : ℤ) (nextVisit' : Slice I64),
      0 ≤ j → j ≤ (nextVisit.val.length : ℤ) - 1 →
        values nextVisit' = List.set (values nextVisit) (nextVisit.val.length - 1) j →
          ∀ r r' : I64,
            Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r →
              Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit' = ok r' →
                r = r') := by
  sorry

/-- Let D be the least day on which every room 0..n-1 has been visited. Whenever the function returns a result r, r = D mod 1000000007 and D <= 2^n - 2.
  Preconditions: Let n = len(nextVisit). Assume n >= 2, n <= 100000, and for every i with 0 <= i < n, 0 <= nextVisit[i] <= i. -/
theorem spec_12 (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)) :
    ∀ D : ℕ,
      IsFirstCoverDay (roomSeq (values nextVisit) nextVisit.val.length)
          nextVisit.val.length D →
        ∀ r : I64,
          Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r →
            r.val = (D : ℤ) % 1000000007 ∧
              (D : ℤ) ≤ (2 : ℤ) ^ nextVisit.val.length - 2 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nextVisit : Slice I64)
    (hn2 : 2 ≤ nextVisit.val.length)
    (hnu : nextVisit.val.length ≤ 100000)
    (hpre : ∀ i : ℕ, i < nextVisit.val.length →
      0 ≤ (values nextVisit).getD i 0 ∧ (values nextVisit).getD i 0 ≤ (i : ℤ)), ∀ D : ℕ,
      IsFirstCoverDay (roomSeq (values nextVisit) nextVisit.val.length)
          nextVisit.val.length D →
        ∀ r : I64,
          Aegis.FirstDayBeenInAllRooms.first_day_been_in_all_rooms nextVisit = ok r →
            r.val = (D : ℤ) % 1000000007 ∧
              (D : ℤ) ≤ (2 : ℤ) ^ nextVisit.val.length - 2) := by
  sorry

end AegisSpec.FirstDayBeenInAllRooms
