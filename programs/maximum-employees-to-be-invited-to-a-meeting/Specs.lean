import Aegis.MaximumInvitations.Code.Funs

/-!
# Specifications of `Aegis.MaximumInvitations.maximum_invitations`

LeetCode problem `maximum-employees-to-be-invited-to-a-meeting`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumInvitations

  def slen (favorite : Slice I64) : Nat := favorite.val.length

  def fav (favorite : Slice I64) (i : Nat) : Int :=
    match favorite.val[i]? with
    | some v => v.val
    | none => 0

  lemma slen_eq_len (favorite : Slice I64) : (Slice.len favorite).val = slen favorite := by
    simp [slen, Slice.len, Usize.ofNatCore]

  lemma fav_eq (favorite : Slice I64) (i : Nat) (h : i < slen favorite) :
      fav favorite i = (favorite.val.get ⟨i, h⟩).val := by
    simp only [fav, List.getElem?_eq_getElem h]
    rfl

  def mapsTo (favorite : Slice I64) (x y : Nat) : Prop := fav favorite x = (y : Int)

  structure Precondition (favorite : Slice I64) : Prop where

    len_ge : 2 ≤ slen favorite

    len_le : slen favorite ≤ 100000

    nonneg : ∀ i, i < slen favorite → 0 ≤ fav favorite i

    lt_len : ∀ i, i < slen favorite → fav favorite i < (slen favorite : Int)

    ne_self : ∀ i, i < slen favorite → fav favorite i ≠ (i : Int)

  def IsCycle (favorite : Slice I64) (c : Nat) (v : Nat → Nat) : Prop :=
    (∀ i, i < c → v i < slen favorite) ∧
    (∀ i, i < c → ∀ j, j < c → v i = v j → i = j) ∧
    (∀ i, i < c → mapsTo favorite (v i) (v ((i + 1) % c)))

  def MutualPair (favorite : Slice I64) (a b : Nat) : Prop :=
    mapsTo favorite a b ∧ mapsTo favorite b a

  def OnlyCycleIsPair (favorite : Slice I64) (a b : Nat) : Prop :=
    mapsTo favorite a b ∧ mapsTo favorite b a ∧
      (∀ (c : Nat) (v : Nat → Nat), IsCycle favorite c v → c = 2 ∧ ∀ i, i < c → (v i = a ∨ v i = b))

  def IsMaxCycleLenGe3 (favorite : Slice I64) (m : Nat) : Prop :=
    3 ≤ m ∧ (∃ v : Nat → Nat, IsCycle favorite m v) ∧
      (∀ (c : Nat) (v : Nat → Nat), 3 ≤ c → IsCycle favorite c v → c ≤ m)

  def IsMaxCycleLenOrZero (favorite : Slice I64) (m : Nat) : Prop :=
    (m = 0 ∧ ¬ ∃ (c : Nat) (v : Nat → Nat), 3 ≤ c ∧ IsCycle favorite c v) ∨
      (3 ≤ m ∧ (∃ v : Nat → Nat, IsCycle favorite m v) ∧
        ∀ (c : Nat) (v : Nat → Nat), 3 ≤ c → IsCycle favorite c v → c ≤ m)

  def IsChainInto (favorite : Slice I64) (a b : Nat) (l : List Nat) : Prop :=
    l.Nodup ∧
      (∀ x ∈ l, x < slen favorite) ∧
      (∀ x ∈ l, x ≠ a ∧ x ≠ b) ∧
      (∀ (i : Nat) (h : i + 1 < l.length),
        mapsTo favorite (l.get ⟨i, by omega⟩) (l.get ⟨i + 1, by omega⟩)) ∧
      (∀ last, l.getLast? = some last → mapsTo favorite last a)

  def IsLongestChainInto (favorite : Slice I64) (a b : Nat) (m : Nat) : Prop :=
    (∃ l : List Nat, IsChainInto favorite a b l ∧ l.length = m) ∧
      ∀ l : List Nat, IsChainInto favorite a b l → l.length ≤ m

  noncomputable def chainLen (favorite : Slice I64) (a b : Nat) : Nat := by
    classical
    exact Nat.findGreatest
      (fun m => ∃ l : List Nat, IsChainInto favorite a b l ∧ l.length = m)
      (slen favorite)

  def IsCircularSeating (S : Finset Nat) (seat : Nat → Nat) : Prop :=
    (∀ x ∈ S, seat x < S.card) ∧
      (∀ x ∈ S, ∀ y ∈ S, seat x = seat y → x = y) ∧
      (∀ k, k < S.card → ∃ x ∈ S, seat x = k)

  def Adjacent (S : Finset Nat) (seat : Nat → Nat) (x y : Nat) : Prop :=
    x ∈ S ∧ y ∈ S ∧ x ≠ y ∧
      (S.card ≤ 2 ∨ seat y = (seat x + 1) % S.card ∨
        seat y = (seat x + S.card - 1) % S.card)

  def HasValidSeating (favorite : Slice I64) (S : Finset Nat) : Prop :=
    ∃ seat : Nat → Nat, IsCircularSeating S seat ∧
      ∀ x ∈ S, ∃ y ∈ S, mapsTo favorite x y ∧ Adjacent S seat x y

  noncomputable def pairWeight (favorite : Slice I64) (a b : Nat) : Nat :=
    2 + chainLen favorite a b + chainLen favorite b a

  noncomputable def pairSum (favorite : Slice I64) : Nat := by
    classical
    exact ∑ a ∈ Finset.range (slen favorite), ∑ b ∈ Finset.range (slen favorite),
      (if a < b ∧ MutualPair favorite a b then pairWeight favorite a b else 0)

  noncomputable def mutualPairCount (favorite : Slice I64) : Nat := by
    classical
    exact ∑ a ∈ Finset.range (slen favorite), ∑ b ∈ Finset.range (slen favorite),
      (if a < b ∧ MutualPair favorite a b then 1 else 0)

  /-- The function returns a result r, and r is the largest integer k for which there exists a set S of employees with S subset of {0,...,n-1}, |S| = k, and a circular seating of S such that every x in S has favorite[x] in S and adjacent to x. A circular seating of a finite set S is a bijection seat : S -> {0,...,|S|-1}; for |S| >= 3, two employees x and y are adjacent iff seat(y) = (seat(x)+1) mod |S| or seat(y) = (seat(x)-1) mod |S|; for |S| = 2 the two employees are adjacent to each other; for |S| = 1 no two distinct employees are adjacent. The maximum is over all such S, including the empty set, but the empty set never affects the value because at least two employees can always be seated.
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. -/
  theorem spec_1 (favorite : Slice I64) (h : Precondition favorite) :
      ∃ r : I64,
        Aegis.MaximumInvitations.maximum_invitations favorite = ok r ∧
          (∃ S : Finset Nat,
            S ⊆ Finset.range (slen favorite) ∧ (S.card : Int) = r.val ∧
              HasValidSeating favorite S) ∧
          (∀ S : Finset Nat,
            S ⊆ Finset.range (slen favorite) → HasValidSeating favorite S →
              (S.card : Int) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite), ∃ r : I64,
          Aegis.MaximumInvitations.maximum_invitations favorite = ok r ∧
            (∃ S : Finset Nat,
              S ⊆ Finset.range (slen favorite) ∧ (S.card : Int) = r.val ∧
                HasValidSeating favorite S) ∧
            (∀ S : Finset Nat,
              S ⊆ Finset.range (slen favorite) → HasValidSeating favorite S →
                (S.card : Int) ≤ r.val)) := by
    sorry

  /-- The function returns a result r; no call on an input satisfying the preconditions fails (there is no arithmetic overflow, out-of-bounds access, or panic).
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. -/
  theorem spec_2 (favorite : Slice I64) (h : Precondition favorite) :
      ∃ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite), ∃ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 2 <= r <= n.
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. -/
  theorem spec_3 (favorite : Slice I64) (h : Precondition favorite) :
      ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
        2 ≤ r.val ∧ r.val ≤ (slen favorite : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite), ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
          2 ≤ r.val ∧ r.val ≤ (slen favorite : Int)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a set S of employees with |S| = r and a circular seating of S, using the circular-table adjacency convention of spec_1, such that for every x in S, favorite[x] is in S and is adjacent to x in that seating.
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. -/
  theorem spec_4 (favorite : Slice I64) (h : Precondition favorite) :
      ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
        ∃ S : Finset Nat,
          S ⊆ Finset.range (slen favorite) ∧ (S.card : Int) = r.val ∧
            HasValidSeating favorite S := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite), ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
          ∃ S : Finset Nat,
            S ⊆ Finset.range (slen favorite) ∧ (S.card : Int) = r.val ∧
              HasValidSeating favorite S) := by
    sorry

  /-- Whenever the function returns a result r, for every set S of employees that admits a circular seating, using the circular-table adjacency convention of spec_1, in which every x in S is adjacent to favorite[x], we have |S| <= r.
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. -/
  theorem spec_5 (favorite : Slice I64) (h : Precondition favorite) :
      ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
        ∀ S : Finset Nat,
          S ⊆ Finset.range (slen favorite) → HasValidSeating favorite S →
            (S.card : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite), ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
          ∀ S : Finset Nat,
            S ⊆ Finset.range (slen favorite) → HasValidSeating favorite S →
              (S.card : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every directed cycle v_0,...,v_{c-1} of favorite with c >= 2 (distinct employees and favorite[v_i] = v_{(i+1) mod c} for all i), we have r >= c.
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. -/
  theorem spec_6 (favorite : Slice I64) (h : Precondition favorite) :
      ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
        ∀ (c : Nat) (v : Nat → Nat), 2 ≤ c → IsCycle favorite c v → (c : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite), ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
          ∀ (c : Nat) (v : Nat → Nat), 2 ≤ c → IsCycle favorite c v → (c : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r equals the maximum length c of a directed cycle of favorite (a sequence v_0,...,v_{c-1} of distinct employees, with c >= 3, such that favorite[v_i] = v_{(i+1) mod c} for all i).
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. In addition, there is no employee i with favorite[favorite[i]] = i (equivalently, there is no directed cycle of length 2). -/
  theorem spec_7 (favorite : Slice I64) (h : Precondition favorite)
      (h2 : ∀ i, i < slen favorite → ∀ j, mapsTo favorite i j → ¬ mapsTo favorite j i) :
      ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
        ∃ m : Nat, IsMaxCycleLenGe3 favorite m ∧ r.val = (m : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite)
        (h2 : ∀ i, i < slen favorite → ∀ j, mapsTo favorite i j → ¬ mapsTo favorite j i), ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
          ∃ m : Nat, IsMaxCycleLenGe3 favorite m ∧ r.val = (m : Int)) := by
    sorry

  /-- Whenever the function returns a result r, let L_a be the largest m >= 0 for which there exist distinct employees x_1,...,x_m, none equal to a or b, such that favorite[x_i] = x_{i+1} for 1 <= i < m and, if m > 0, favorite[x_m] = a. Define L_b similarly with b in place of a. Then r = 2 + L_a + L_b.
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. In addition, there exist employees a and b such that favorite[a] = b, favorite[b] = a, and the only directed cycle of favorite is this 2-cycle. -/
  theorem spec_8 (favorite : Slice I64) (h : Precondition favorite)
      (hpair : ∃ a b : Nat, a < slen favorite ∧ b < slen favorite ∧ OnlyCycleIsPair favorite a b) :
      ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
        ∀ (a b : Nat), a < slen favorite → b < slen favorite → OnlyCycleIsPair favorite a b →
          ∀ La Lb : Nat,
            IsLongestChainInto favorite a b La → IsLongestChainInto favorite b a Lb →
              r.val = 2 + (La : Int) + (Lb : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite)
        (hpair : ∃ a b : Nat, a < slen favorite ∧ b < slen favorite ∧ OnlyCycleIsPair favorite a b), ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
          ∀ (a b : Nat), a < slen favorite → b < slen favorite → OnlyCycleIsPair favorite a b →
            ∀ La Lb : Nat,
              IsLongestChainInto favorite a b La → IsLongestChainInto favorite b a Lb →
                r.val = 2 + (La : Int) + (Lb : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every mutual pair a,b (favorite[a] = b and favorite[b] = a) and every sequence x_1,...,x_p of pairwise distinct employees, none equal to a or b, with favorite[x_i] = x_{i+1} for 1 <= i < p and, if p > 0, favorite[x_p] = a, and every sequence y_1,...,y_q of pairwise distinct employees, none equal to a or b or any x_i, with favorite[y_j] = y_{j+1} for 1 <= j < q and, if q > 0, favorite[y_q] = b, we have r >= 2 + p + q.
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. -/
  theorem spec_9 (favorite : Slice I64) (h : Precondition favorite) :
      ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
        ∀ (a b : Nat), MutualPair favorite a b →
          ∀ (xs ys : List Nat),
            IsChainInto favorite a b xs → IsChainInto favorite b a ys → xs.Disjoint ys →
              2 + (xs.length : Int) + (ys.length : Int) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite), ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
          ∀ (a b : Nat), MutualPair favorite a b →
            ∀ (xs ys : List Nat),
              IsChainInto favorite a b xs → IsChainInto favorite b a ys → xs.Disjoint ys →
                2 + (xs.length : Int) + (ys.length : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, if q is the number of unordered pairs {a,b} of distinct employees with favorite[a] = b and favorite[b] = a, then r >= 2*q.
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. In addition, every directed cycle of favorite has length 2. -/
  theorem spec_10 (favorite : Slice I64) (h : Precondition favorite)
      (hcyc : ∀ (c : Nat) (v : Nat → Nat), IsCycle favorite c v → c = 2) :
      ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
        2 * (mutualPairCount favorite : Int) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite)
        (hcyc : ∀ (c : Nat) (v : Nat → Nat), IsCycle favorite c v → c = 2), ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
          2 * (mutualPairCount favorite : Int) ≤ r.val) := by
    sorry

  /-- Let n = len(favorite). For each unordered mutual pair {a,b} with favorite[a]=b and favorite[b]=a, let L_{a,b} be the largest m >= 0 for which there exist distinct employees x_1,...,x_m, none equal to a or b, such that favorite[x_i]=x_{i+1} for 1 <= i < m and, if m > 0, favorite[x_m]=a; define L_{b,a} similarly with b in place of a. Let T be the sum over all unordered mutual pairs {a,b} of (2 + L_{a,b} + L_{b,a}). Let M be the maximum length c of a directed cycle v_0,...,v_{c-1} of favorite with c >= 3 (distinct employees and favorite[v_i]=v_{(i+1) mod c}), or M=0 if no such cycle exists. Whenever the function returns a result r, r = max(M,T).
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. -/
  theorem spec_11 (favorite : Slice I64) (h : Precondition favorite) :
      ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
        ∃ M : Nat, IsMaxCycleLenOrZero favorite M ∧
          r.val = max (M : Int) (pairSum favorite : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite), ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
          ∃ M : Nat, IsMaxCycleLenOrZero favorite M ∧
            r.val = max (M : Int) (pairSum favorite : Int)) := by
    sorry

  /-- Whenever the function returns a result r, with L_{a,b} and L_{b,a} defined as above for every mutual pair {a,b}, r >= sum over all unordered mutual pairs {a,b} of (2 + L_{a,b} + L_{b,a}). Thus all 2-cycle components, each with its two longest feeding chains, can be seated simultaneously.
    Preconditions: Let n = len(favorite). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= favorite[i] <= n-1 and favorite[i] != i. -/
  theorem spec_12 (favorite : Slice I64) (h : Precondition favorite) :
      ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
        (pairSum favorite : Int) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (favorite : Slice I64) (h : Precondition favorite), ∀ r : I64, Aegis.MaximumInvitations.maximum_invitations favorite = ok r →
          (pairSum favorite : Int) ≤ r.val) := by
    sorry

  end AegisSpec.MaximumInvitations
