import Aegis.CatchMaximumAmountofPeople.Code.Funs

/-!
# Specifications of `Aegis.CatchMaximumAmountofPeople.catch_maximum_amountof_people`

LeetCode problem `maximum-number-of-people-that-can-be-caught-in-tag`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CatchMaximumAmountofPeople

  open Aegis.CatchMaximumAmountofPeople

  abbrev entry (t : List Std.I64) (i : ℕ) : Option ℤ := (t[i]?).map (fun x => x.val)

  abbrev IsOne (t : List Std.I64) (i : ℕ) : Prop := entry t i = some 1

  abbrev IsZero (t : List Std.I64) (i : ℕ) : Prop := entry t i = some 0

  def IsBinary (t : List Std.I64) : Prop := ∀ x ∈ t, x.val = 0 ∨ x.val = 1

  abbrev IsCatchPair (t : List Std.I64) (dist : ℤ) (i j : ℕ) : Prop :=
    i < t.length ∧ j < t.length ∧ IsOne t i ∧ IsZero t j ∧ |(i : ℤ) - (j : ℤ)| ≤ dist

  def IsCatchingAssignment (t : List Std.I64) (dist : ℤ) (M : Finset (ℕ × ℕ)) : Prop :=
    (∀ p ∈ M, IsCatchPair t dist p.1 p.2) ∧
      (M.image (fun p => p.1)).card = M.card ∧
      (M.image (fun p => p.2)).card = M.card

  def IsCatchingAssignmentIn (t : List Std.I64) (dist : ℤ) (s : Finset ℕ)
      (M : Finset (ℕ × ℕ)) : Prop :=
    IsCatchingAssignment t dist M ∧ ∀ p ∈ M, p.1 ∈ s ∧ p.2 ∈ s

  noncomputable def maxCatchIn (t : List Std.I64) (dist : ℤ) (s : Finset ℕ) : ℕ := by
    classical
    exact (Finset.range (t.length + 1)).sup
      (fun k => if ∃ M : Finset (ℕ × ℕ), IsCatchingAssignmentIn t dist s M ∧ M.card = k
        then k else 0)

  noncomputable def maxCatch (t : List Std.I64) (dist : ℤ) : ℕ :=
    maxCatchIn t dist (Finset.range t.length)

  def ones (t : List Std.I64) : ℕ :=
    ((Finset.range t.length).filter (fun i => IsOne t i)).card

  def zeros (t : List Std.I64) : ℕ :=
    ((Finset.range t.length).filter (fun j => IsZero t j)).card

  def reachable (t : List Std.I64) (dist : ℤ) : ℕ :=
    ((Finset.range t.length).filter (fun j =>
      IsZero t j ∧ ∃ i ∈ Finset.range t.length, IsOne t i ∧ |(i : ℤ) - (j : ℤ)| ≤ dist)).card

  def revTeam (t : List Std.I64) : List Std.I64 := t.reverse

  /-- Let n = len(team). A catch pair is a pair (i, j) of indices with 0 <= i < n, 0 <= j < n, team[i] = 1, team[j] = 0, and |i - j| <= dist (absolute value of the integer difference i - j). A catching assignment is a set M of catch pairs such that no two pairs of M have the same first component and no two pairs of M have the same second component (equivalently: each person who is "it" catches at most one person, and each person who is not "it" is caught at most once). The function returns a result r, and r is the maximum possible size of a catching assignment: there exists a catching assignment M with |M| = r, and every catching assignment M' satisfies |M'| <= r.
    Preconditions: len(team) >= 1, every element of team is 0 or 1, and 1 <= dist <= len(team) (so dist >= 0). -/
  theorem spec_1 (team : Slice Std.I64) (dist : Std.I64)
      (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)) :
      ∃ r, catch_maximum_amountof_people team dist = ok r ∧
        (∃ M : Finset (ℕ × ℕ),
          IsCatchingAssignment team.val dist.val M ∧ (M.card : ℤ) = r.val) ∧
        (∀ M : Finset (ℕ × ℕ),
          IsCatchingAssignment team.val dist.val M → (M.card : ℤ) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64)
        (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)), ∃ r, catch_maximum_amountof_people team dist = ok r ∧
          (∃ M : Finset (ℕ × ℕ),
            IsCatchingAssignment team.val dist.val M ∧ (M.card : ℤ) = r.val) ∧
          (∀ M : Finset (ℕ × ℕ),
            IsCatchingAssignment team.val dist.val M → (M.card : ℤ) ≤ r.val)) := by
    sorry

  /-- Let ones = the number of indices i with 0 <= i < len(team) and team[i] = 1, and zeros = the number of indices j with 0 <= j < len(team) and team[j] = 0. The function returns a result r with 0 <= r <= min(ones, zeros).
    Preconditions: len(team) >= 1, every element of team is 0 or 1, and 1 <= dist <= len(team). -/
  theorem spec_2 (team : Slice Std.I64) (dist : Std.I64)
      (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)) :
      ∃ r, catch_maximum_amountof_people team dist = ok r ∧
        0 ≤ r.val ∧ r.val ≤ ((min (ones team.val) (zeros team.val) : ℕ) : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64)
        (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)), ∃ r, catch_maximum_amountof_people team dist = ok r ∧
          0 ≤ r.val ∧ r.val ≤ ((min (ones team.val) (zeros team.val) : ℕ) : ℤ)) := by
    sorry

  /-- The function returns the result r = 0.
    Preconditions: len(team) >= 1, every element of team is 0 or 1, 1 <= dist <= len(team), and team[i] = 0 for every i with 0 <= i < len(team) (there is no person who is "it"). -/
  theorem spec_3 (team : Slice Std.I64) (dist : Std.I64)
      (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ))
      (h_all_zero : ∀ i, i < team.val.length → IsZero team.val i) :
      ∃ r, catch_maximum_amountof_people team dist = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64)
        (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ))
        (h_all_zero : ∀ i, i < team.val.length → IsZero team.val i), ∃ r, catch_maximum_amountof_people team dist = ok r ∧ r.val = 0) := by
    sorry

  /-- Let n = len(team). The returned value r satisfies: r = 0 if and only if there is no pair of indices (i, j) with 0 <= i < n, 0 <= j < n, team[i] = 1, team[j] = 0 and |i - j| <= dist. Equivalently, r >= 1 if and only if some person who is "it" is within distance dist of some person who is not "it".
    Preconditions: len(team) >= 1, every element of team is 0 or 1, and 1 <= dist <= len(team). -/
  theorem spec_4 (team : Slice Std.I64) (dist : Std.I64)
      (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)) :
      ∃ r, catch_maximum_amountof_people team dist = ok r ∧
        (r.val = 0 ↔ ¬ ∃ i j, IsCatchPair team.val dist.val i j) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64)
        (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)), ∃ r, catch_maximum_amountof_people team dist = ok r ∧
          (r.val = 0 ↔ ¬ ∃ i j, IsCatchPair team.val dist.val i j)) := by
    sorry

  /-- Let r be the returned value. Then there exist r distinct indices j_1, ..., j_r with 0 <= j_k < len(team) and team[j_k] = 0, and r distinct indices i_1, ..., i_r with 0 <= i_k < len(team) and team[i_k] = 1, such that |i_k - j_k| <= dist for every k with 1 <= k <= r. (In other words, r distinct people who are not "it" can simultaneously be caught, each by a distinct person who is "it" within distance dist.)
    Preconditions: len(team) >= 1, every element of team is 0 or 1, and 1 <= dist <= len(team). -/
  theorem spec_5 (team : Slice Std.I64) (dist : Std.I64)
      (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)) :
      ∃ r, catch_maximum_amountof_people team dist = ok r ∧
        ∃ M : Finset (ℕ × ℕ), (M.card : ℤ) = r.val ∧
          (∀ p ∈ M, p.1 < team.val.length ∧ p.2 < team.val.length ∧
            IsOne team.val p.1 ∧ IsZero team.val p.2 ∧
            |(p.1 : ℤ) - (p.2 : ℤ)| ≤ dist.val) ∧
          (M.image (fun p => p.1)).card = M.card ∧
          (M.image (fun p => p.2)).card = M.card := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64)
        (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)), ∃ r, catch_maximum_amountof_people team dist = ok r ∧
          ∃ M : Finset (ℕ × ℕ), (M.card : ℤ) = r.val ∧
            (∀ p ∈ M, p.1 < team.val.length ∧ p.2 < team.val.length ∧
              IsOne team.val p.1 ∧ IsZero team.val p.2 ∧
              |(p.1 : ℤ) - (p.2 : ℤ)| ≤ dist.val) ∧
            (M.image (fun p => p.1)).card = M.card ∧
            (M.image (fun p => p.2)).card = M.card) := by
    sorry

  /-- Let n = len(team) and let reachable = the number of indices j with 0 <= j < n, team[j] = 0, for which there exists an index i with 0 <= i < n, team[i] = 1 and |i - j| <= dist. The returned value r satisfies r <= reachable.
    Preconditions: len(team) >= 1, every element of team is 0 or 1, and 1 <= dist <= len(team). -/
  theorem spec_6 (team : Slice Std.I64) (dist : Std.I64)
      (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)) :
      ∃ r, catch_maximum_amountof_people team dist = ok r ∧
        r.val ≤ ((reachable team.val dist.val : ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64)
        (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)), ∃ r, catch_maximum_amountof_people team dist = ok r ∧
          r.val ≤ ((reachable team.val dist.val : ℕ) : ℤ)) := by
    sorry

  /-- Let ones = the number of indices i with team[i] = 1 and zeros = the number of indices j with team[j] = 0. The function returns the result r = min(ones, zeros).
    Preconditions: len(team) >= 1, every element of team is 0 or 1, and 1 <= dist <= len(team), and additionally dist >= len(team) - 1. -/
  theorem spec_7 (team : Slice Std.I64) (dist : Std.I64)
      (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ))
      (h_dist_large : (team.val.length : ℤ) - 1 ≤ dist.val) :
      ∃ r, catch_maximum_amountof_people team dist = ok r ∧
        r.val = ((min (ones team.val) (zeros team.val) : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64)
        (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ))
        (h_dist_large : (team.val.length : ℤ) - 1 ≤ dist.val), ∃ r, catch_maximum_amountof_people team dist = ok r ∧
          r.val = ((min (ones team.val) (zeros team.val) : ℕ) : ℤ)) := by
    sorry

  /-- Let n = len(team) and let rev be the array of length n defined by rev[i] = team[n - 1 - i] for 0 <= i < n (the order of all people is reversed). Then the maximum number of people who can be caught from rev with the same distance dist is equal to the returned value r for team.
    Preconditions: len(team) >= 1, every element of team is 0 or 1, and 1 <= dist <= len(team). -/
  theorem spec_8 (team : Slice Std.I64) (dist : Std.I64)
      (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)) :
      ∃ r, catch_maximum_amountof_people team dist = ok r ∧
        ((maxCatch (revTeam team.val) dist.val : ℕ) : ℤ) = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64)
        (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)), ∃ r, catch_maximum_amountof_people team dist = ok r ∧
          ((maxCatch (revTeam team.val) dist.val : ℕ) : ℤ) = r.val) := by
    sorry

  /-- Let r be the returned value for distance dist. For every integer dist' with dist <= dist' <= len(team), the maximum number of people who can be caught from the same array team with distance dist' is at least r.
    Preconditions: len(team) >= 1, every element of team is 0 or 1, and 1 <= dist <= len(team). -/
  theorem spec_9 (team : Slice Std.I64) (dist : Std.I64)
      (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)) :
      ∀ dist' : ℤ, dist.val ≤ dist' → dist' ≤ (team.val.length : ℤ) →
        ∃ r, catch_maximum_amountof_people team dist = ok r ∧
          r.val ≤ ((maxCatch team.val dist' : ℕ) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64)
        (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)), ∀ dist' : ℤ, dist.val ≤ dist' → dist' ≤ (team.val.length : ℤ) →
          ∃ r, catch_maximum_amountof_people team dist = ok r ∧
            r.val ≤ ((maxCatch team.val dist' : ℕ) : ℤ)) := by
    sorry

  /-- Let i be that unique index with team[i] = 1. The function returns r = 1 if there exists an index j with 0 <= j < len(team), team[j] = 0 and |i - j| <= dist; otherwise it returns r = 0.
    Preconditions: len(team) >= 1, every element of team is 0 or 1, 1 <= dist <= len(team), and there is exactly one index i with 0 <= i < len(team) and team[i] = 1. -/
  theorem spec_10 (team : Slice Std.I64) (dist : Std.I64)
      (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ))
      (h_unique : ∃ i, i < team.val.length ∧ IsOne team.val i ∧
        ∀ i', i' < team.val.length → IsOne team.val i' → i' = i) :
      ∃ r, catch_maximum_amountof_people team dist = ok r ∧
        ∀ i, i < team.val.length → IsOne team.val i →
          ((∃ j, j < team.val.length ∧ IsZero team.val j ∧
              |(i : ℤ) - (j : ℤ)| ≤ dist.val) → r.val = 1) ∧
          (¬ (∃ j, j < team.val.length ∧ IsZero team.val j ∧
              |(i : ℤ) - (j : ℤ)| ≤ dist.val) → r.val = 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64)
        (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ))
        (h_unique : ∃ i, i < team.val.length ∧ IsOne team.val i ∧
          ∀ i', i' < team.val.length → IsOne team.val i' → i' = i), ∃ r, catch_maximum_amountof_people team dist = ok r ∧
          ∀ i, i < team.val.length → IsOne team.val i →
            ((∃ j, j < team.val.length ∧ IsZero team.val j ∧
                |(i : ℤ) - (j : ℤ)| ≤ dist.val) → r.val = 1) ∧
            (¬ (∃ j, j < team.val.length ∧ IsZero team.val j ∧
                |(i : ℤ) - (j : ℤ)| ≤ dist.val) → r.val = 0)) := by
    sorry

  /-- The function returns a result r (i.e. it does not fail by overflow, out-of-bounds access, or panic) for every input satisfying the preconditions; moreover 0 <= r <= len(team) <= 100000, so the returned value fits in a 64-bit integer.
    Preconditions: len(team) >= 1, len(team) <= 100000, every element of team is 0 or 1, and 1 <= dist <= len(team). -/
  theorem spec_11 (team : Slice Std.I64) (dist : Std.I64)
      (h_len : 1 ≤ team.val.length) (h_len_le : team.val.length ≤ 100000)
      (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)) :
      ∃ r, catch_maximum_amountof_people team dist = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (team.val.length : ℤ) ∧ r.val ≤ (100000 : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64)
        (h_len : 1 ≤ team.val.length) (h_len_le : team.val.length ≤ 100000)
        (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ)), ∃ r, catch_maximum_amountof_people team dist = ok r ∧
          0 ≤ r.val ∧ r.val ≤ (team.val.length : ℤ) ∧ r.val ≤ (100000 : ℤ)) := by
    sorry

  /-- Let n = len(team) and let p be an index with 0 <= p < n - 1 such that no catch crosses the cut between p and p + 1, i.e. for all indices i, j with 0 <= i < n, 0 <= j < n, team[i] = 1, team[j] = 0, it is not the case that (i <= p and j > p and j - i <= dist) and it is not the case that (i > p and j <= p and i - j <= dist). Let r_left be the maximum number of pairwise-disjoint catch pairs (i, j) with i <= p and j <= p (within the left part), and r_right the maximum number of pairwise-disjoint catch pairs with i > p and j > p (within the right part), where a catch pair (i, j) means team[i] = 1, team[j] = 0 and |i - j| <= dist. Then the returned value satisfies r = r_left + r_right.
    Preconditions: len(team) >= 1, every element of team is 0 or 1, and 1 <= dist <= len(team). -/
  theorem spec_12 (team : Slice Std.I64) (dist : Std.I64) (p : ℕ)
      (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
      (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ))
      (h_p : p < team.val.length - 1)
      (h_cut : ∀ i j, i < team.val.length → j < team.val.length →
        IsOne team.val i → IsZero team.val j →
          ¬ (i ≤ p ∧ p < j ∧ ((j : ℤ) - (i : ℤ)) ≤ dist.val) ∧
          ¬ (p < i ∧ j ≤ p ∧ ((i : ℤ) - (j : ℤ)) ≤ dist.val)) :
      ∃ r, catch_maximum_amountof_people team dist = ok r ∧
        r.val = ((maxCatchIn team.val dist.val (Finset.range (p + 1)) : ℕ) : ℤ) +
          ((maxCatchIn team.val dist.val
            (Finset.range team.val.length \ Finset.range (p + 1)) : ℕ) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (team : Slice Std.I64) (dist : Std.I64) (p : ℕ)
        (h_len : 1 ≤ team.val.length) (h_bin : IsBinary team.val)
        (h_dist_lo : 1 ≤ dist.val) (h_dist_hi : dist.val ≤ (team.val.length : ℤ))
        (h_p : p < team.val.length - 1)
        (h_cut : ∀ i j, i < team.val.length → j < team.val.length →
          IsOne team.val i → IsZero team.val j →
            ¬ (i ≤ p ∧ p < j ∧ ((j : ℤ) - (i : ℤ)) ≤ dist.val) ∧
            ¬ (p < i ∧ j ≤ p ∧ ((i : ℤ) - (j : ℤ)) ≤ dist.val)), ∃ r, catch_maximum_amountof_people team dist = ok r ∧
          r.val = ((maxCatchIn team.val dist.val (Finset.range (p + 1)) : ℕ) : ℤ) +
            ((maxCatchIn team.val dist.val
              (Finset.range team.val.length \ Finset.range (p + 1)) : ℕ) : ℤ)) := by
    sorry

  end AegisSpec.CatchMaximumAmountofPeople
