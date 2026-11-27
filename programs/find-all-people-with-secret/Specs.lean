import Aegis.FindAllPeople.Code.Funs

/-!
# Specifications of `Aegis.FindAllPeople.find_all_people`

LeetCode problem `find-all-people-with-secret`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindAllPeople

def triples (meetings : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int × Int) :=
  meetings.val.filterMap fun m =>
    match m.val with
    | [x, y, t] => some (x.val, y.val, t.val)
    | _ => none

def ValidInput (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) : Prop :=
  2 ≤ n.val ∧ n.val ≤ 100000 ∧
  1 ≤ (meetings.val.length : Int) ∧ (meetings.val.length : Int) ≤ 100000 ∧
  (∀ (i : Nat) (hi : i < meetings.val.length),
    (meetings.val.get ⟨i, hi⟩).val.length = 3 ∧
    (∀ (x y t : Std.I64), (meetings.val.get ⟨i, hi⟩).val = [x, y, t] →
      0 ≤ x.val ∧ x.val ≤ n.val - 1 ∧
      0 ≤ y.val ∧ y.val ≤ n.val - 1 ∧
      x.val ≠ y.val ∧
      1 ≤ t.val ∧ t.val ≤ 100000)) ∧
  1 ≤ firstPerson.val ∧ firstPerson.val ≤ n.val - 1

def Occurs (r : alloc.vec.Vec Std.I64) (p : Int) : Prop :=
  ∃ e, e ∈ r.val ∧ e.val = p

def Adj (T : List (Int × Int × Int)) (t u v : Int) : Prop :=
  (u, v, t) ∈ T ∨ (v, u, t) ∈ T

def SameComponent (T : List (Int × Int × Int)) (t u v : Int) : Prop :=
  Relation.ReflTransGen (Adj T t) u v

def step (T : List (Int × Int × Int)) (K : Int → Prop) (t : Int) : Int → Prop :=
  fun p => K p ∨ ∃ u, K u ∧ SameComponent T t u p

def secretUpTo (T : List (Int × Int × Int)) (K₀ : Int → Prop) : Nat → Int → Prop
  | 0 => K₀
  | k + 1 => step T (secretUpTo T K₀ k) (k : Int)

def secretInit (firstPerson : Int) : Int → Prop :=
  fun p => p = 0 ∨ p = firstPerson

def maxTime (T : List (Int × Int × Int)) : Int :=
  T.foldr (fun m acc => max m.2.2 acc) 0

def FinalSecret (meetings : Slice (alloc.vec.Vec Std.I64)) (firstPerson : Int) : Int → Prop :=
  secretUpTo (triples meetings) (secretInit firstPerson) ((maxTime (triples meetings)).toNat + 1)

def SecretBefore (meetings : Slice (alloc.vec.Vec Std.I64)) (firstPerson : Int)
    (t : Int) : Int → Prop :=
  secretUpTo (triples meetings) (secretInit firstPerson) t.toNat

def Nondecreasing : List Int → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≤ b ∧ Nondecreasing (b :: rest)

def ChainWitness (meetings : Slice (alloc.vec.Vec Std.I64)) (firstPerson : Int)
    (ps ts : List Int) : Prop :=
  ps.length = ts.length + 1 ∧
  (ps[0]? = some 0 ∨ ps[0]? = some firstPerson) ∧
  (∀ (j : Nat), j < ts.length →
    ∃ (x y t : Int), ps[j]? = some x ∧ ps[j + 1]? = some y ∧ ts[j]? = some t ∧
      ((x, y, t) ∈ triples meetings ∨ (y, x, t) ∈ triples meetings))

def ChainTo (meetings : Slice (alloc.vec.Vec Std.I64)) (firstPerson : Int) (p : Int) : Prop :=
  ∃ (ps ts : List Int), ChainWitness meetings firstPerson ps ts ∧
    ps[ts.length]? = some p ∧ Nondecreasing ts

/-- Whenever the function returns a result r, r has no repeated entries and, for every person p with 0 <= p < n, p occurs in r if and only if p belongs to the final secret set K defined as follows. Let K_0 = {0, firstPerson}. Process the distinct meeting times in increasing order. For a time t, let G_t be the undirected graph on people {0,...,n-1} with an edge between x and y exactly when meetings contains a triple [x,y,t] or [y,x,t]. Let K_<t be the set obtained after processing all times less than t. Let C_t be the union of all connected components of G_t (including isolated vertices) that contain at least one vertex of K_<t. Set K_t = K_<t union C_t. Then K is the set after processing the largest meeting time (and K = K_0 if meetings is empty). The entries of r may be in any order.
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_1 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      r.val.Nodup ∧
      (∀ p : Int, 0 ≤ p → p < n.val →
        (Occurs r p ↔ FinalSecret meetings firstPerson.val p)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      r.val.Nodup ∧
      (∀ p : Int, 0 ≤ p → p < n.val →
        (Occurs r p ↔ FinalSecret meetings firstPerson.val p))) := by
  sorry

/-- The function returns a result r (it does not fail, panic, overflow, or access out of bounds) for every input satisfying the preconditions.
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_2 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∃ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∃ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), the integer r[i] satisfies 0 <= r[i] < n.
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_3 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        0 ≤ (r.val.get ⟨i, hi⟩).val ∧ (r.val.get ⟨i, hi⟩).val < n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        0 ≤ (r.val.get ⟨i, hi⟩).val ∧ (r.val.get ⟨i, hi⟩).val < n.val) := by
  sorry

/-- Whenever the function returns a result r, for all indices i and j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_4 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length), i < j →
        r.val.get ⟨i, hi⟩ ≠ r.val.get ⟨j, hj⟩ := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length), i < j →
        r.val.get ⟨i, hi⟩ ≠ r.val.get ⟨j, hj⟩) := by
  sorry

/-- Whenever the function returns a result r, 2 <= len(r) <= n.
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_5 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      2 ≤ (r.val.length : Int) ∧ (r.val.length : Int) ≤ n.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      2 ≤ (r.val.length : Int) ∧ (r.val.length : Int) ≤ n.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(r) and r[i] = 0.
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_6 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∃ (i : Nat) (hi : i < r.val.length), (r.val.get ⟨i, hi⟩).val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∃ (i : Nat) (hi : i < r.val.length), (r.val.get ⟨i, hi⟩).val = 0) := by
  sorry

/-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(r) and r[i] = firstPerson.
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_7 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∃ (i : Nat) (hi : i < r.val.length), (r.val.get ⟨i, hi⟩).val = firstPerson.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∃ (i : Nat) (hi : i < r.val.length), (r.val.get ⟨i, hi⟩).val = firstPerson.val) := by
  sorry

/-- Whenever the function returns a result r, for every person p with 0 <= p < n, if p != 0, p != firstPerson, and no index i with 0 <= i < len(meetings) has meetings[i][0] = p or meetings[i][1] = p, then p does not occur in r.
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_8 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ p : Int, 0 ≤ p → p < n.val → p ≠ 0 → p ≠ firstPerson.val →
        (∀ (i : Nat) (hi : i < meetings.val.length) (x y t : Std.I64),
          (meetings.val.get ⟨i, hi⟩).val = [x, y, t] → x.val ≠ p ∧ y.val ≠ p) →
        ¬ Occurs r p := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ p : Int, 0 ≤ p → p < n.val → p ≠ 0 → p ≠ firstPerson.val →
        (∀ (i : Nat) (hi : i < meetings.val.length) (x y t : Std.I64),
          (meetings.val.get ⟨i, hi⟩).val = [x, y, t] → x.val ≠ p ∧ y.val ≠ p) →
        ¬ Occurs r p) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(meetings), writing meetings[i] = [x,y,t], if x = 0 or x = firstPerson then y occurs in r, and if y = 0 or y = firstPerson then x occurs in r.
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_9 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ (i : Nat) (hi : i < meetings.val.length) (x y t : Std.I64),
        (meetings.val.get ⟨i, hi⟩).val = [x, y, t] →
        (x.val = 0 ∨ x.val = firstPerson.val → Occurs r y.val) ∧
        (y.val = 0 ∨ y.val = firstPerson.val → Occurs r x.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ (i : Nat) (hi : i < meetings.val.length) (x y t : Std.I64),
        (meetings.val.get ⟨i, hi⟩).val = [x, y, t] →
        (x.val = 0 ∨ x.val = firstPerson.val → Occurs r y.val) ∧
        (y.val = 0 ∨ y.val = firstPerson.val → Occurs r x.val)) := by
  sorry

/-- Whenever the function returns a result r, for every person p that occurs in r there exist an integer k >= 0, people p_0,...,p_k, and meeting times t_1,...,t_k such that p_k = p, p_0 = 0 or p_0 = firstPerson, and for every j with 1 <= j <= k, meetings contains a meeting whose two endpoints are p_{j-1} and p_j and whose time is t_j, and 1 <= t_1 <= t_2 <= ... <= t_k. When k = 0 this says p is 0 or firstPerson.
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_10 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ p : Int, Occurs r p → ChainTo meetings firstPerson.val p := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ p : Int, Occurs r p → ChainTo meetings firstPerson.val p) := by
  sorry

/-- Whenever the function returns a result r, for every person p with 0 <= p < n, if there exist an integer k >= 0, people p_0,...,p_k, and meeting times t_1,...,t_k such that p_k = p, p_0 = 0 or p_0 = firstPerson, for every j with 1 <= j <= k meetings contains a meeting whose two endpoints are p_{j-1} and p_j and whose time is t_j, and 1 <= t_1 <= t_2 <= ... <= t_k, then p occurs in r.
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_11 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ p : Int, 0 ≤ p → p < n.val → ChainTo meetings firstPerson.val p → Occurs r p := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ p : Int, 0 ≤ p → p < n.val → ChainTo meetings firstPerson.val p → Occurs r p) := by
  sorry

/-- Whenever the function returns r on input (n, meetings, firstPerson) and returns r' on input (n, meetings', firstPerson), for every person p with 0 <= p < n, p occurs in r if and only if p occurs in r'.
  Preconditions: 2 <= n <= 10^5; 1 <= firstPerson <= n-1; meetings and meetings' are two valid meeting arrays, meaning each has length between 1 and 10^5, each entry has length 3, and for each meeting [x,y,t] in either array, 0 <= x,y <= n-1, x != y, and 1 <= t <= 10^5; and for every time t and every unordered pair of distinct people {x,y}, some meeting [x,y,t] or [y,x,t] occurs in meetings if and only if some meeting [x,y,t] or [y,x,t] occurs in meetings'. -/
theorem spec_12 (n : Std.I64) (meetings meetings' : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson)
    (hpre' : ValidInput n meetings' firstPerson)
    (hedges : ∀ (t x y : Int), x ≠ y →
      ((x, y, t) ∈ triples meetings ∨ (y, x, t) ∈ triples meetings) ↔
      ((x, y, t) ∈ triples meetings' ∨ (y, x, t) ∈ triples meetings')) :
    ∀ (r r' : alloc.vec.Vec Std.I64),
      Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      Aegis.FindAllPeople.find_all_people n meetings' firstPerson = ok r' →
      ∀ p : Int, 0 ≤ p → p < n.val → (Occurs r p ↔ Occurs r' p) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (meetings meetings' : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson)
    (hpre' : ValidInput n meetings' firstPerson)
    (hedges : ∀ (t x y : Int), x ≠ y →
      ((x, y, t) ∈ triples meetings ∨ (y, x, t) ∈ triples meetings) ↔
      ((x, y, t) ∈ triples meetings' ∨ (y, x, t) ∈ triples meetings')), ∀ (r r' : alloc.vec.Vec Std.I64),
      Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      Aegis.FindAllPeople.find_all_people n meetings' firstPerson = ok r' →
      ∀ p : Int, 0 ≤ p → p < n.val → (Occurs r p ↔ Occurs r' p)) := by
  sorry

/-- Whenever the function returns a result r, for every time t and every pair of people x,y with 0 <= x,y < n, if x belongs to K_<t and x and y lie in the same connected component of the undirected graph H_t, then y occurs in r. Here K_<t is the set of people who know the secret after all meetings with time strictly less than t, computed from K_0 = {0, firstPerson} by, for each meeting time t' < t in increasing order, adding every vertex in a connected component of H_{t'} that contains a vertex already in the set; and H_t is the undirected graph on {0,...,n-1} whose edges are {a,b} for every meeting [a,b,t] or [b,a,t] in meetings.
  Preconditions: 2 <= n <= 10^5; 1 <= len(meetings) <= 10^5; for every i with 0 <= i < len(meetings), len(meetings[i]) = 3, and if meetings[i] = [x_i, y_i, t_i] then 0 <= x_i, y_i <= n-1, x_i != y_i, and 1 <= t_i <= 10^5; 1 <= firstPerson <= n-1. -/
theorem spec_13 (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson) :
    ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ (t x y : Int), 0 ≤ x → x < n.val → 0 ≤ y → y < n.val →
        SecretBefore meetings firstPerson.val t x →
        SameComponent (triples meetings) t x y →
        Occurs r y := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (meetings : Slice (alloc.vec.Vec Std.I64))
    (firstPerson : Std.I64) (hpre : ValidInput n meetings firstPerson), ∀ r, Aegis.FindAllPeople.find_all_people n meetings firstPerson = ok r →
      ∀ (t x y : Int), 0 ≤ x → x < n.val → 0 ≤ y → y < n.val →
        SecretBefore meetings firstPerson.val t x →
        SameComponent (triples meetings) t x y →
        Occurs r y) := by
  sorry

end AegisSpec.FindAllPeople
