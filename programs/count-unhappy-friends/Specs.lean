import Aegis.UnhappyFriends.Code.Funs

/-!
# Specifications of `Aegis.UnhappyFriends.unhappy_friends`

LeetCode problem `count-unhappy-friends`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.UnhappyFriends

def NRange (n : I64) : Prop :=
  n.val % 2 = 0 ∧ 2 ≤ n.val ∧ n.val ≤ 500

def PreferencesWF (n : I64) (preferences : Slice (alloc.vec.Vec I64)) : Prop :=
  preferences.val.length = n.val.toNat ∧
    ∀ (i : ℕ) (hi : i < preferences.val.length),
      let row := (preferences.val[i]).val
      row.length = n.val.toNat - 1 ∧
        (∀ e ∈ row, 0 ≤ e.val ∧ e.val < n.val) ∧
        (∀ e ∈ row, e.val ≠ (i : ℤ)) ∧
        row.Nodup

def PairsWF (n : I64) (pairs : Slice (alloc.vec.Vec I64)) : Prop :=
  pairs.val.length = n.val.toNat / 2 ∧
    (∀ (k : ℕ) (hk : k < pairs.val.length),
      let row := (pairs.val[k]).val
      row.length = 2 ∧
        (∀ e ∈ row, 0 ≤ e.val ∧ e.val < n.val) ∧
        row.Nodup) ∧
    ∀ (p : ℕ), p < n.val.toNat →
      ∃! (k : ℕ), ∃ (hk : k < pairs.val.length),
        ∃ e ∈ (pairs.val[k]).val, e.val = (p : ℤ)

def row (preferences : Slice (alloc.vec.Vec I64)) (i : ℤ) : List I64 :=
  match preferences.val[i.toNat]? with
  | none => []
  | some v => v.val

def pos (preferences : Slice (alloc.vec.Vec I64)) (a b : ℤ) : ℕ :=
  (row preferences a).findIdx (fun e => e.val = b)

def prefers (preferences : Slice (alloc.vec.Vec I64)) (a b c : ℤ) : Prop :=
  pos preferences a b < pos preferences a c

def Paired (pairs : Slice (alloc.vec.Vec I64)) (x y : ℤ) : Prop :=
  x ≠ y ∧
    ∃ (k : ℕ) (hk : k < pairs.val.length),
      x ∈ (pairs.val[k]).val.map (fun e => e.val) ∧
        y ∈ (pairs.val[k]).val.map (fun e => e.val)

def Blocks (preferences pairs : Slice (alloc.vec.Vec I64)) (x u : ℤ) : Prop :=
  ∃ y w : ℤ,
    Paired pairs x y ∧ Paired pairs u w ∧
      prefers preferences x u y ∧ prefers preferences u x w

def Unhappy (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (x : ℤ) : Prop :=
  ∃ u : ℤ, 0 ≤ u ∧ u < n.val ∧ u ≠ x ∧ Blocks preferences pairs x u

def headVal (preferences : Slice (alloc.vec.Vec I64)) (i : ℤ) : Option ℤ :=
  (row preferences i).head?.map (fun e => e.val)

def lastVal (preferences : Slice (alloc.vec.Vec I64)) (i : ℤ) : Option ℤ :=
  (row preferences i).getLast?.map (fun e => e.val)

noncomputable def partnerOf (pairs : Slice (alloc.vec.Vec I64)) (x : ℤ) : ℤ := by
  classical
  exact if h : ∃ y, Paired pairs x y then Classical.choose h else x

noncomputable def unhappyCount (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) :
    ℕ := by
  classical
  exact ((Finset.range n.val.toNat).filter
    (fun x : ℕ => Unhappy n preferences pairs (x : ℤ))).card

noncomputable def firstChoiceCount (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) :
    ℕ := by
  classical
  exact ((Finset.range n.val.toNat).filter
    (fun x : ℕ => headVal preferences (x : ℤ) = some (partnerOf pairs (x : ℤ)))).card

noncomputable def blockingPairs (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) :
    Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range n.val.toNat).product (Finset.range n.val.toNat)).filter
    (fun q : ℕ × ℕ => q.1 < q.2 ∧ Blocks preferences pairs (q.1 : ℤ) (q.2 : ℤ))

/-- Whenever the function returns a result r, r equals the number of friends x with 0 <= x < n that are unhappy. Here x is paired with y iff x != y and {x,y} is the set of the two entries of some element of pairs; for distinct a,b with 0 <= a,b < n, pos(a,b) is the unique index j with preferences[a][j] = b; a prefers b over c means pos(a,b) < pos(a,c); and x is unhappy iff, letting y be the unique friend paired with x, there exists a friend u with 0 <= u < n and u != x such that, letting v be the unique friend paired with u, x prefers u over y and u prefers x over v.
  Preconditions: n is even, 2 <= n <= 500, and reading n as a natural number: len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs) = n/2; for every k with 0 <= k < len(pairs), len(pairs[k]) = 2, pairs[k][0] != pairs[k][1], and both entries are in [0,n); and every p with 0 <= p < n occurs as an endpoint in exactly one element of pairs. -/
theorem spec_1 (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r) :
    r.val = (unhappyCount n preferences pairs : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r), r.val = (unhappyCount n preferences pairs : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n.
  Preconditions: n is even, 2 <= n <= 500, and reading n as a natural number: len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs) = n/2; for every k with 0 <= k < len(pairs), len(pairs[k]) = 2, pairs[k][0] != pairs[k][1], and both entries are in [0,n); and every p with 0 <= p < n occurs as an endpoint in exactly one element of pairs. -/
theorem spec_2 (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r) :
    0 ≤ r.val ∧ r.val ≤ n.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r), 0 ≤ r.val ∧ r.val ≤ n.val) := by
  sorry

/-- The function returns a result r (it does not fail, panic, overflow, or access an out-of-bounds index) for every input satisfying the preconditions.
  Preconditions: n is even, 2 <= n <= 500, and reading n as a natural number: len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs) = n/2; for every k with 0 <= k < len(pairs), len(pairs[k]) = 2, pairs[k][0] != pairs[k][1], and both entries are in [0,n); and every p with 0 <= p < n occurs as an endpoint in exactly one element of pairs. -/
theorem spec_3 (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64))
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs) :
    ∃ r, Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64))
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs), ∃ r, Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: n is even, 2 <= n <= 500, and reading n as a natural number: len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs) = n/2; for every k with 0 <= k < len(pairs), len(pairs[k]) = 2, pairs[k][0] != pairs[k][1], and both entries are in [0,n); and every p with 0 <= p < n occurs as an endpoint in exactly one element of pairs. Additionally, for every k with 0 <= k < len(pairs), if a = pairs[k][0] and b = pairs[k][1], then preferences[a][0] = b and preferences[b][0] = a. -/
theorem spec_4 (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (hfirst : ∀ (k : ℕ) (hk : k < pairs.val.length) (a b : I64),
      (pairs.val[k]).val = [a, b] →
        headVal preferences a.val = some b.val ∧ headVal preferences b.val = some a.val)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r) :
    r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (hfirst : ∀ (k : ℕ) (hk : k < pairs.val.length) (a b : I64),
      (pairs.val[k]).val = [a, b] →
        headVal preferences a.val = some b.val ∧ headVal preferences b.val = some a.val)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = n.
  Preconditions: n is even, 2 <= n <= 500, n >= 4, and reading n as a natural number: len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs) = n/2; for every k with 0 <= k < len(pairs), len(pairs[k]) = 2, pairs[k][0] != pairs[k][1], and both entries are in [0,n); and every p with 0 <= p < n occurs as an endpoint in exactly one element of pairs. Additionally, for every k with 0 <= k < len(pairs), if a = pairs[k][0] and b = pairs[k][1], then preferences[a][len(preferences[a]) - 1] = b and preferences[b][len(preferences[b]) - 1] = a. -/
theorem spec_5 (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hn4 : 4 ≤ n.val)
    (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (hlast : ∀ (k : ℕ) (hk : k < pairs.val.length) (a b : I64),
      (pairs.val[k]).val = [a, b] →
        lastVal preferences a.val = some b.val ∧ lastVal preferences b.val = some a.val)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r) :
    r.val = n.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hn4 : 4 ≤ n.val)
    (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (hlast : ∀ (k : ℕ) (hk : k < pairs.val.length) (a b : I64),
      (pairs.val[k]).val = [a, b] →
        lastVal preferences a.val = some b.val ∧ lastVal preferences b.val = some a.val)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r), r.val = n.val) := by
  sorry

/-- Whenever the function returns r, r = 0 if and only if there do not exist distinct friends x,u with 0 <= x,u < n such that, writing y for the unique friend paired with x and w for the unique friend paired with u, pos(x,u) < pos(x,y) and pos(u,x) < pos(u,w), where for distinct a,b with 0 <= a,b < n, pos(a,b) is the unique index j with preferences[a][j] = b, and paired means occurring together as the two entries of one element of pairs.
  Preconditions: n is even, 2 <= n <= 500, and reading n as a natural number: len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs) = n/2; for every k with 0 <= k < len(pairs), len(pairs[k]) = 2, pairs[k][0] != pairs[k][1], and both entries are in [0,n); and every p with 0 <= p < n occurs as an endpoint in exactly one element of pairs. -/
theorem spec_6 (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r) :
    (r.val = 0 ↔
      ¬ ∃ x u : ℤ, 0 ≤ x ∧ x < n.val ∧ 0 ≤ u ∧ u < n.val ∧ x ≠ u ∧
        Blocks preferences pairs x u) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r), (r.val = 0 ↔
      ¬ ∃ x u : ℤ, 0 ≤ x ∧ x < n.val ∧ 0 ≤ u ∧ u < n.val ∧ x ≠ u ∧
        Blocks preferences pairs x u)) := by
  sorry

/-- Whenever the function returns r, r != 1; equivalently, r = 0 or r >= 2.
  Preconditions: n is even, 2 <= n <= 500, and reading n as a natural number: len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs) = n/2; for every k with 0 <= k < len(pairs), len(pairs[k]) = 2, pairs[k][0] != pairs[k][1], and both entries are in [0,n); and every p with 0 <= p < n occurs as an endpoint in exactly one element of pairs. -/
theorem spec_7 (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r) :
    r.val ≠ 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r), r.val ≠ 1) := by
  sorry

/-- If the function returns r1 on (n, preferences, pairs1) and r2 on (n, preferences, pairs2), then r1 = r2.
  Preconditions: Both (n, preferences, pairs1) and (n, preferences, pairs2) satisfy the problem constraints: n is even, 2 <= n <= 500, len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs1) = len(pairs2) = n/2; every element of either pairs list has length 2 with distinct endpoints in [0,n); and every person occurs as an endpoint in exactly one element of pairs1 and exactly one element of pairs2. Moreover, for all x,y in [0,n), {x,y} is the set of entries of some element of pairs1 if and only if it is the set of entries of some element of pairs2. -/
theorem spec_8 (n : I64) (preferences : Slice (alloc.vec.Vec I64))
    (pairs1 pairs2 : Slice (alloc.vec.Vec I64)) (r1 r2 : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences)
    (hpair1 : PairsWF n pairs1) (hpair2 : PairsWF n pairs2)
    (hsame : ∀ x y : ℤ, 0 ≤ x → x < n.val → 0 ≤ y → y < n.val →
      (Paired pairs1 x y ↔ Paired pairs2 x y))
    (h1 : Aegis.UnhappyFriends.unhappy_friends n preferences pairs1 = ok r1)
    (h2 : Aegis.UnhappyFriends.unhappy_friends n preferences pairs2 = ok r2) :
    r1 = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (preferences : Slice (alloc.vec.Vec I64))
    (pairs1 pairs2 : Slice (alloc.vec.Vec I64)) (r1 r2 : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences)
    (hpair1 : PairsWF n pairs1) (hpair2 : PairsWF n pairs2)
    (hsame : ∀ x y : ℤ, 0 ≤ x → x < n.val → 0 ≤ y → y < n.val →
      (Paired pairs1 x y ↔ Paired pairs2 x y))
    (h1 : Aegis.UnhappyFriends.unhappy_friends n preferences pairs1 = ok r1)
    (h2 : Aegis.UnhappyFriends.unhappy_friends n preferences pairs2 = ok r2), r1 = r2) := by
  sorry

/-- If the function returns r on (n, preferences, pairs) and r' on (n, preferences', pairs'), then r = r'.
  Preconditions: The input (n, preferences, pairs) satisfies the problem constraints: n is even, 2 <= n <= 500, len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs) = n/2; every element of pairs has length 2 with distinct endpoints in [0,n); and every person occurs as an endpoint in exactly one element of pairs. Let pi be any bijection from {0,...,n-1} to itself. Let preferences' be defined by: for each i, preferences'[pi(i)] is the list obtained from preferences[i] by replacing each entry z with pi(z). Let pairs' be obtained from pairs by replacing each endpoint z with pi(z). -/
theorem spec_9 (n : I64)
    (preferences preferences' pairs pairs' : Slice (alloc.vec.Vec I64))
    (r r' : I64) (pi : ℤ → ℤ)
    (hn : NRange n)
    (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (hpref' : PreferencesWF n preferences') (hpair' : PairsWF n pairs')
    (hpi_maps : ∀ i : ℤ, 0 ≤ i → i < n.val → 0 ≤ pi i ∧ pi i < n.val)
    (hpi_inj : ∀ i j : ℤ, 0 ≤ i → i < n.val → 0 ≤ j → j < n.val → pi i = pi j → i = j)
    (hpi_surj : ∀ j : ℤ, 0 ≤ j → j < n.val → ∃ i : ℤ, 0 ≤ i ∧ i < n.val ∧ pi i = j)
    (hrelabel : ∀ i j : ℤ, 0 ≤ i → i < n.val → 0 ≤ j → j < n.val →
      pos preferences' (pi i) (pi j) = pos preferences i j)
    (hrelabel_pairs : ∀ x y : ℤ, 0 ≤ x → x < n.val → 0 ≤ y → y < n.val →
      (Paired pairs' (pi x) (pi y) ↔ Paired pairs x y))
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r)
    (h' : Aegis.UnhappyFriends.unhappy_friends n preferences' pairs' = ok r') :
    r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64)
    (preferences preferences' pairs pairs' : Slice (alloc.vec.Vec I64))
    (r r' : I64) (pi : ℤ → ℤ)
    (hn : NRange n)
    (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (hpref' : PreferencesWF n preferences') (hpair' : PairsWF n pairs')
    (hpi_maps : ∀ i : ℤ, 0 ≤ i → i < n.val → 0 ≤ pi i ∧ pi i < n.val)
    (hpi_inj : ∀ i j : ℤ, 0 ≤ i → i < n.val → 0 ≤ j → j < n.val → pi i = pi j → i = j)
    (hpi_surj : ∀ j : ℤ, 0 ≤ j → j < n.val → ∃ i : ℤ, 0 ≤ i ∧ i < n.val ∧ pi i = j)
    (hrelabel : ∀ i j : ℤ, 0 ≤ i → i < n.val → 0 ≤ j → j < n.val →
      pos preferences' (pi i) (pi j) = pos preferences i j)
    (hrelabel_pairs : ∀ x y : ℤ, 0 ≤ x → x < n.val → 0 ≤ y → y < n.val →
      (Paired pairs' (pi x) (pi y) ↔ Paired pairs x y))
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r)
    (h' : Aegis.UnhappyFriends.unhappy_friends n preferences' pairs' = ok r'), r = r') := by
  sorry

/-- Whenever the function returns r, let c be the number of friends x with 0 <= x < n such that preferences[x][0] equals the unique friend paired with x by pairs. Then r <= n - c.
  Preconditions: n is even, 2 <= n <= 500, and reading n as a natural number: len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs) = n/2; for every k with 0 <= k < len(pairs), len(pairs[k]) = 2, pairs[k][0] != pairs[k][1], and both entries are in [0,n); and every p with 0 <= p < n occurs as an endpoint in exactly one element of pairs. -/
theorem spec_10 (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r) :
    r.val ≤ n.val - (firstChoiceCount n preferences pairs : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r), r.val ≤ n.val - (firstChoiceCount n preferences pairs : ℤ)) := by
  sorry

/-- Whenever the function returns r, let E be the number of unordered pairs {x,u} of distinct friends with 0 <= x,u < n such that, writing y for x's partner and w for u's partner, pos(x,u) < pos(x,y) and pos(u,x) < pos(u,w), where pos(a,b) is the unique index j with preferences[a][j] = b and partner means the unique friend occurring with one in an element of pairs. Then r <= 2*E.
  Preconditions: n is even, 2 <= n <= 500, and reading n as a natural number: len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs) = n/2; for every k with 0 <= k < len(pairs), len(pairs[k]) = 2, pairs[k][0] != pairs[k][1], and both entries are in [0,n); and every p with 0 <= p < n occurs as an endpoint in exactly one element of pairs. -/
theorem spec_11 (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r) :
    r.val ≤ 2 * ((blockingPairs n preferences pairs).card : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r), r.val ≤ 2 * ((blockingPairs n preferences pairs).card : ℤ)) := by
  sorry

/-- Whenever the function returns r with r > 0, there exist distinct friends x,u with 0 <= x,u < n such that, writing y for x's partner and w for u's partner, pos(x,u) < pos(x,y) and pos(u,x) < pos(u,w), where pos(a,b) is the unique index j with preferences[a][j] = b and partner means the unique friend occurring with one in an element of pairs.
  Preconditions: n is even, 2 <= n <= 500, and reading n as a natural number: len(preferences) = n; for every i with 0 <= i < n, len(preferences[i]) = n - 1, every entry of preferences[i] is in [0,n), preferences[i] contains no i, and all entries of preferences[i] are distinct; len(pairs) = n/2; for every k with 0 <= k < len(pairs), len(pairs[k]) = 2, pairs[k][0] != pairs[k][1], and both entries are in [0,n); and every p with 0 <= p < n occurs as an endpoint in exactly one element of pairs. -/
theorem spec_12 (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r)
    (hr : 0 < r.val) :
    ∃ x u : ℤ, 0 ≤ x ∧ x < n.val ∧ 0 ≤ u ∧ u < n.val ∧ x ≠ u ∧
      Blocks preferences pairs x u := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : I64) (preferences pairs : Slice (alloc.vec.Vec I64)) (r : I64)
    (hn : NRange n) (hpref : PreferencesWF n preferences) (hpair : PairsWF n pairs)
    (h : Aegis.UnhappyFriends.unhappy_friends n preferences pairs = ok r)
    (hr : 0 < r.val), ∃ x u : ℤ, 0 ≤ x ∧ x < n.val ∧ 0 ≤ u ∧ u < n.val ∧ x ≠ u ∧
      Blocks preferences pairs x u) := by
  sorry

end AegisSpec.UnhappyFriends
