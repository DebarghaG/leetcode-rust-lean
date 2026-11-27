import Aegis.NumTeams.Code.Funs

/-!
# Specifications of `Aegis.NumTeams.num_teams`

LeetCode problem `count-number-of-teams`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumTeams

  def len (a : Slice Std.I64) : ℕ := a.val.length

  def valAt (a : Slice Std.I64) (i : ℕ) : ℤ := (a.val.getD i default).val

  def isTeam (x y z : ℤ) : Prop := (x < y ∧ y < z) ∨ (x > y ∧ y > z)

  instance isTeam.instDecidable (x y z : ℤ) : Decidable (isTeam x y z) := by
    unfold isTeam; infer_instance

  def consecCount (a : Slice Std.I64) : ℕ :=
    ∑ i ∈ Finset.range (len a),
      if i + 2 < len a ∧ isTeam (valAt a i) (valAt a (i + 1)) (valAt a (i + 2)) then 1 else 0

  def teamCount (a : Slice Std.I64) : ℕ :=
    ∑ i ∈ Finset.range (len a), ∑ j ∈ Finset.range (len a), ∑ k ∈ Finset.range (len a),
      if i < j ∧ j < k ∧ isTeam (valAt a i) (valAt a j) (valAt a k) then 1 else 0

  def StrictInc (a : Slice Std.I64) : Prop := ∀ i j, i < j → j < len a → valAt a i < valAt a j

  def StrictDec (a : Slice Std.I64) : Prop := ∀ i j, i < j → j < len a → valAt a i > valAt a j

  def IsRev (b a : Slice Std.I64) : Prop :=
    len b = len a ∧ ∀ i, i < len b → valAt b i = valAt a (len a - 1 - i)

  def InRange (a : Slice Std.I64) : Prop :=
    ∀ i, i < len a → 1 ≤ valAt a i ∧ valAt a i ≤ 100000

  def PairwiseDistinct (a : Slice Std.I64) : Prop :=
    ∀ i j, i < j → j < len a → valAt a i ≠ valAt a j

  def Precond (a : Slice Std.I64) : Prop :=
    3 ≤ len a ∧ len a ≤ 1000 ∧ InRange a ∧ PairwiseDistinct a

  def leftLess (a : Slice Std.I64) (j : ℕ) : ℕ :=
    ((Finset.range j).filter (fun i => valAt a i < valAt a j)).card

  def leftGreater (a : Slice Std.I64) (j : ℕ) : ℕ :=
    ((Finset.range j).filter (fun i => valAt a i > valAt a j)).card

  def rightLess (a : Slice Std.I64) (j : ℕ) : ℕ :=
    ((Finset.range (len a)).filter (fun k => j < k ∧ valAt a k < valAt a j)).card

  def rightGreater (a : Slice Std.I64) (j : ℕ) : ℕ :=
    ((Finset.range (len a)).filter (fun k => j < k ∧ valAt a k > valAt a j)).card

  def decompCount (a : Slice Std.I64) : ℕ :=
    ∑ j ∈ Finset.range (len a),
      (leftLess a j * rightGreater a j + leftGreater a j * rightLess a j)

  /-- num_teams(rating) returns a result r, and r equals the number of index triples (i, j, k) with 0 <= i < j < k < n such that either rating[i] < rating[j] < rating[k] or rating[i] > rating[j] > rating[k]. Equivalently, r = |{ (i,j,k) : 0 <= i < j < k < n and ((rating[i] < rating[j] and rating[j] < rating[k]) or (rating[i] > rating[j] and rating[j] > rating[k])) }|.
    Preconditions: Let n = len(rating). The preconditions are: 3 <= n <= 1000; for every i with 0 <= i < n, 1 <= rating[i] <= 100000; and for all 0 <= i < j < n, rating[i] != rating[j]. -/
  theorem spec_1 (rating : Slice Std.I64) (h : Precond rating) :
      ∃ r, Aegis.NumTeams.num_teams rating = ok r ∧ r.val = (teamCount rating : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (rating : Slice Std.I64) (h : Precond rating), ∃ r, Aegis.NumTeams.num_teams rating = ok r ∧ r.val = (teamCount rating : ℤ)) := by
    sorry

  /-- For every rating satisfying the preconditions, num_teams(rating) returns a result r; in particular, the function never fails, overflows, or panics on any input in the precondition set.
    Preconditions: Let n = len(rating). The preconditions are: 3 <= n <= 1000; for every i with 0 <= i < n, 1 <= rating[i] <= 100000; and for all 0 <= i < j < n, rating[i] != rating[j]. -/
  theorem spec_2 (rating : Slice Std.I64) (h : Precond rating) :
      ∃ r, Aegis.NumTeams.num_teams rating = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (rating : Slice Std.I64) (h : Precond rating), ∃ r, Aegis.NumTeams.num_teams rating = ok r) := by
    sorry

  /-- Whenever num_teams(rating) returns a result r, r <= n*(n-1)*(n-2)/6, where n = len(rating). The right-hand side is the total number of index triples 0 <= i < j < k < n.
    Preconditions: Let n = len(rating). The preconditions are: 3 <= n <= 1000; for every i with 0 <= i < n, 1 <= rating[i] <= 100000; and for all 0 <= i < j < n, rating[i] != rating[j]. -/
  theorem spec_3 (rating : Slice Std.I64) (h : Precond rating) (r : Std.I64)
      (hr : Aegis.NumTeams.num_teams rating = ok r) :
      r.val ≤ ((len rating * (len rating - 1) * (len rating - 2) / 6 : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (rating : Slice Std.I64) (h : Precond rating) (r : Std.I64)
        (hr : Aegis.NumTeams.num_teams rating = ok r), r.val ≤ ((len rating * (len rating - 1) * (len rating - 2) / 6 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever num_teams(rating) returns a result r, r is at least the number of indices i with 0 <= i <= n-3 for which the consecutive triple (rating[i], rating[i+1], rating[i+2]) is strictly increasing or strictly decreasing. In symbols, r >= |{ i : 0 <= i <= n-3 and ((rating[i] < rating[i+1] and rating[i+1] < rating[i+2]) or (rating[i] > rating[i+1] and rating[i+1] > rating[i+2])) }|.
    Preconditions: Let n = len(rating). The preconditions are: 3 <= n <= 1000; for every i with 0 <= i < n, 1 <= rating[i] <= 100000; and for all 0 <= i < j < n, rating[i] != rating[j]. -/
  theorem spec_4 (rating : Slice Std.I64) (h : Precond rating) (r : Std.I64)
      (hr : Aegis.NumTeams.num_teams rating = ok r) :
      (consecCount rating : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (rating : Slice Std.I64) (h : Precond rating) (r : Std.I64)
        (hr : Aegis.NumTeams.num_teams rating = ok r), (consecCount rating : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever num_teams(rating) returns a result r, r = 1 if (rating[0] < rating[1] and rating[1] < rating[2]) or (rating[0] > rating[1] and rating[1] > rating[2]), and r = 0 otherwise.
    Preconditions: len(rating) = 3; for every i with 0 <= i < 3, 1 <= rating[i] <= 100000; and rating[0], rating[1], rating[2] are pairwise distinct. -/
  theorem spec_5 (rating : Slice Std.I64) (h3 : len rating = 3)
      (hrange : ∀ i, i < 3 → 1 ≤ valAt rating i ∧ valAt rating i ≤ 100000)
      (hdist : ∀ i j, i < 3 → j < 3 → i ≠ j → valAt rating i ≠ valAt rating j)
      (r : Std.I64) (hr : Aegis.NumTeams.num_teams rating = ok r) :
      r.val = (if isTeam (valAt rating 0) (valAt rating 1) (valAt rating 2) then (1 : ℤ) else 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (rating : Slice Std.I64) (h3 : len rating = 3)
        (hrange : ∀ i, i < 3 → 1 ≤ valAt rating i ∧ valAt rating i ≤ 100000)
        (hdist : ∀ i j, i < 3 → j < 3 → i ≠ j → valAt rating i ≠ valAt rating j)
        (r : Std.I64) (hr : Aegis.NumTeams.num_teams rating = ok r), r.val = (if isTeam (valAt rating 0) (valAt rating 1) (valAt rating 2) then (1 : ℤ) else 0)) := by
    sorry

  /-- Whenever num_teams(rating) returns a result r and rating is strictly increasing, i.e. rating[0] < rating[1] < ... < rating[n-1], then r = n*(n-1)*(n-2)/6.
    Preconditions: Let n = len(rating). The preconditions are: 3 <= n <= 1000; for every i with 0 <= i < n, 1 <= rating[i] <= 100000; and for all 0 <= i < j < n, rating[i] != rating[j]. -/
  theorem spec_6 (rating : Slice Std.I64) (h : Precond rating) (hinc : StrictInc rating)
      (r : Std.I64) (hr : Aegis.NumTeams.num_teams rating = ok r) :
      r.val = ((len rating * (len rating - 1) * (len rating - 2) / 6 : ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (rating : Slice Std.I64) (h : Precond rating) (hinc : StrictInc rating)
        (r : Std.I64) (hr : Aegis.NumTeams.num_teams rating = ok r), r.val = ((len rating * (len rating - 1) * (len rating - 2) / 6 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever num_teams(rating) returns a result r and rating is strictly decreasing, i.e. rating[0] > rating[1] > ... > rating[n-1], then r = n*(n-1)*(n-2)/6.
    Preconditions: Let n = len(rating). The preconditions are: 3 <= n <= 1000; for every i with 0 <= i < n, 1 <= rating[i] <= 100000; and for all 0 <= i < j < n, rating[i] != rating[j]. -/
  theorem spec_7 (rating : Slice Std.I64) (h : Precond rating) (hdec : StrictDec rating)
      (r : Std.I64) (hr : Aegis.NumTeams.num_teams rating = ok r) :
      r.val = ((len rating * (len rating - 1) * (len rating - 2) / 6 : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (rating : Slice Std.I64) (h : Precond rating) (hdec : StrictDec rating)
        (r : Std.I64) (hr : Aegis.NumTeams.num_teams rating = ok r), r.val = ((len rating * (len rating - 1) * (len rating - 2) / 6 : ℕ) : ℤ)) := by
    sorry

  /-- Let rev be the slice of length n defined by rev[i] = rating[n-1-i] for 0 <= i < n. Whenever num_teams(rating) returns a result r and num_teams(rev) returns a result r', we have r = r'.
    Preconditions: Let n = len(rating). The preconditions are: 3 <= n <= 1000; for every i with 0 <= i < n, 1 <= rating[i] <= 100000; and for all 0 <= i < j < n, rating[i] != rating[j]. -/
  theorem spec_8 (rating rev : Slice Std.I64) (h : Precond rating) (hrev : IsRev rev rating)
      (r r' : Std.I64) (hr : Aegis.NumTeams.num_teams rating = ok r)
      (hr' : Aegis.NumTeams.num_teams rev = ok r') :
      r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (rating rev : Slice Std.I64) (h : Precond rating) (hrev : IsRev rev rating)
        (r r' : Std.I64) (hr : Aegis.NumTeams.num_teams rating = ok r)
        (hr' : Aegis.NumTeams.num_teams rev = ok r'), r = r') := by
    sorry

  /-- Whenever num_teams(a) returns a result r and num_teams(b) returns a result r', we have r = r'.
    Preconditions: Let n >= 3 and let a and b be slices of length n. Both satisfy: for every i with 0 <= i < n, 1 <= a[i] <= 100000 and 1 <= b[i] <= 100000; and for all 0 <= i < j < n, a[i] != a[j] and b[i] != b[j]. Additionally, for all 0 <= i, j < n, a[i] < a[j] if and only if b[i] > b[j]. -/
  theorem spec_9 (a b : Slice Std.I64) (h3 : 3 ≤ len a) (hlen : len a = len b)
      (hrangea : InRange a) (hrangeb : InRange b)
      (hdistincta : PairwiseDistinct a) (hdistinctb : PairwiseDistinct b)
      (hord : ∀ i j, i < len a → j < len a → (valAt a i < valAt a j ↔ valAt b i > valAt b j))
      (r r' : Std.I64) (hr : Aegis.NumTeams.num_teams a = ok r)
      (hr' : Aegis.NumTeams.num_teams b = ok r') :
      r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (a b : Slice Std.I64) (h3 : 3 ≤ len a) (hlen : len a = len b)
        (hrangea : InRange a) (hrangeb : InRange b)
        (hdistincta : PairwiseDistinct a) (hdistinctb : PairwiseDistinct b)
        (hord : ∀ i j, i < len a → j < len a → (valAt a i < valAt a j ↔ valAt b i > valAt b j))
        (r r' : Std.I64) (hr : Aegis.NumTeams.num_teams a = ok r)
        (hr' : Aegis.NumTeams.num_teams b = ok r'), r = r') := by
    sorry

  /-- Whenever num_teams(b) returns a result r_b and num_teams(rating) returns a result r, we have r_b <= r.
    Preconditions: Let n = len(rating) with 3 <= n <= 1000, and assume rating satisfies: for every i with 0 <= i < n, 1 <= rating[i] <= 100000; and for all 0 <= i < j < n, rating[i] != rating[j]. Let b be a slice of length m with 3 <= m <= n, and suppose there exist indices 0 <= t_0 < t_1 < ... < t_{m-1} < n such that b[q] = rating[t_q] for all 0 <= q < m. -/
  theorem spec_10 (rating b : Slice Std.I64) (h : Precond rating)
      (hm : 3 ≤ len b ∧ len b ≤ len rating)
      (hemb : ∃ t : ℕ → ℕ,
        (∀ q, q < len b → t q < len rating) ∧
        (∀ q q', q < q' → q' < len b → t q < t q') ∧
        (∀ q, q < len b → valAt b q = valAt rating (t q)))
      (rb r : Std.I64) (hrb : Aegis.NumTeams.num_teams b = ok rb)
      (hr : Aegis.NumTeams.num_teams rating = ok r) :
      rb.val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (rating b : Slice Std.I64) (h : Precond rating)
        (hm : 3 ≤ len b ∧ len b ≤ len rating)
        (hemb : ∃ t : ℕ → ℕ,
          (∀ q, q < len b → t q < len rating) ∧
          (∀ q q', q < q' → q' < len b → t q < t q') ∧
          (∀ q, q < len b → valAt b q = valAt rating (t q)))
        (rb r : Std.I64) (hrb : Aegis.NumTeams.num_teams b = ok rb)
        (hr : Aegis.NumTeams.num_teams rating = ok r), rb.val ≤ r.val) := by
    sorry

  /-- Whenever num_teams(rating) returns a result r, r > 0 if and only if there exist indices 0 <= i < j < k < n such that (rating[i] < rating[j] and rating[j] < rating[k]) or (rating[i] > rating[j] and rating[j] > rating[k]). Equivalently, r = 0 if and only if no valid team exists.
    Preconditions: Let n = len(rating). The preconditions are: 3 <= n <= 1000; for every i with 0 <= i < n, 1 <= rating[i] <= 100000; and for all 0 <= i < j < n, rating[i] != rating[j]. -/
  theorem spec_11 (rating : Slice Std.I64) (h : Precond rating) (r : Std.I64)
      (hr : Aegis.NumTeams.num_teams rating = ok r) :
      0 < r.val ↔ ∃ i j k, i < j ∧ j < k ∧ k < len rating ∧
        isTeam (valAt rating i) (valAt rating j) (valAt rating k) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (rating : Slice Std.I64) (h : Precond rating) (r : Std.I64)
        (hr : Aegis.NumTeams.num_teams rating = ok r), 0 < r.val ↔ ∃ i j k, i < j ∧ j < k ∧ k < len rating ∧
          isTeam (valAt rating i) (valAt rating j) (valAt rating k)) := by
    sorry

  /-- For each middle index j with 0 <= j < n, define L_<(j) = |{ i : 0 <= i < j and rating[i] < rating[j] }|, L_>(j) = |{ i : 0 <= i < j and rating[i] > rating[j] }|, R_<(j) = |{ k : j < k < n and rating[k] < rating[j] }|, and R_>(j) = |{ k : j < k < n and rating[k] > rating[j] }|. Then num_teams(rating) returns a result r, and r = sum over j = 0 to n-1 of (L_<(j) * R_>(j) + L_>(j) * R_<(j)).
    Preconditions: Let n = len(rating). The preconditions are: 3 <= n <= 1000; for every i with 0 <= i < n, 1 <= rating[i] <= 100000; and for all 0 <= i < j < n, rating[i] != rating[j]. -/
  theorem spec_12 (rating : Slice Std.I64) (h : Precond rating) :
      ∃ r, Aegis.NumTeams.num_teams rating = ok r ∧ r.val = (decompCount rating : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (rating : Slice Std.I64) (h : Precond rating), ∃ r, Aegis.NumTeams.num_teams rating = ok r ∧ r.val = (decompCount rating : ℤ)) := by
    sorry

  end AegisSpec.NumTeams
