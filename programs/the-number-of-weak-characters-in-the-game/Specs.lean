import Aegis.NumberOfWeakCharacters.Code.Funs

/-!
# Specifications of `Aegis.NumberOfWeakCharacters.number_of_weak_characters`

LeetCode problem `the-number-of-weak-characters-in-the-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NumberOfWeakCharacters (number_of_weak_characters)

  namespace AegisSpec.NumberOfWeakCharacters

  def rowVal (r : alloc.vec.Vec Std.I64) : List Int := r.val.map fun x => x.val

  def rowsVal (properties : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    properties.val.map rowVal

  def attack (r : List Int) : Int := r.getD 0 0

  def defense (r : List Int) : Int := r.getD 1 0

  def rowAt (rows : List (List Int)) (i : Nat) : List Int := rows.getD i []

  def RowOK (r : List Int) : Prop :=
    ∃ a d : Int, r = [a, d] ∧ 1 ≤ a ∧ a ≤ 100000 ∧ 1 ≤ d ∧ d ≤ 100000

  def BaseConstraints (rows : List (List Int)) : Prop :=
    2 ≤ rows.length ∧ rows.length ≤ 100000 ∧ ∀ r ∈ rows, RowOK r

  def Dominates (rows : List (List Int)) (k j : Nat) : Prop :=
    attack (rowAt rows k) > attack (rowAt rows j) ∧
      defense (rowAt rows k) > defense (rowAt rows j)

  def IsWeak (rows : List (List Int)) (i : Nat) : Prop :=
    i < rows.length ∧ ∃ j : Nat, j < rows.length ∧ j ≠ i ∧ Dominates rows j i

  noncomputable def weakCount (rows : List (List Int)) : Nat := by
    classical
    exact ((Finset.range rows.length).filter (fun i => IsWeak rows i)).card

  def HasDominatingIndex (rows : List (List Int)) : Prop :=
    ∃ k : Nat, k < rows.length ∧ ∀ j : Nat, j < rows.length → j ≠ k → Dominates rows k j

  def IsRelabeling (rows rows' : List (List Int)) : Prop :=
    ∃ π : Nat → Nat,
      (∀ i, i < rows.length → π i < rows.length) ∧
        (∀ j, j < rows.length → ∃ i, i < rows.length ∧ π i = j) ∧
          (∀ i, i < rows'.length → rowAt rows' i = rowAt rows (π i))

  /-- Whenever the function returns a result r, r is the number of indices i with 0 <= i < len(properties) for which there exists an index j with 0 <= j < len(properties), j != i, properties[j][0] > properties[i][0], and properties[j][1] > properties[i][1]. Each index position contributes at most one to this count; equality in either coordinate does not make a character weak.
    Preconditions: 2 <= len(properties) <= 100000; for every i with 0 <= i < len(properties), len(properties[i]) = 2, 1 <= properties[i][0] <= 100000, and 1 <= properties[i][1] <= 100000. -/
  theorem spec_1 (properties : Slice (alloc.vec.Vec Std.I64))
      (h : BaseConstraints (rowsVal properties)) :
      ∀ r : Std.I64, number_of_weak_characters properties = ok r →
        r.val = (weakCount (rowsVal properties) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (properties : Slice (alloc.vec.Vec Std.I64))
        (h : BaseConstraints (rowsVal properties)), ∀ r : Std.I64, number_of_weak_characters properties = ok r →
          r.val = (weakCount (rowsVal properties) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: 2 <= len(properties) <= 100000; for every i with 0 <= i < len(properties), len(properties[i]) = 2, 1 <= properties[i][0] <= 100000, and 1 <= properties[i][1] <= 100000. -/
  theorem spec_2 (properties : Slice (alloc.vec.Vec Std.I64))
      (h : BaseConstraints (rowsVal properties)) :
      ∃ r : Std.I64, number_of_weak_characters properties = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (properties : Slice (alloc.vec.Vec Std.I64))
        (h : BaseConstraints (rowsVal properties)), ∃ r : Std.I64, number_of_weak_characters properties = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(properties) - 1.
    Preconditions: 2 <= len(properties) <= 100000; for every i with 0 <= i < len(properties), len(properties[i]) = 2, 1 <= properties[i][0] <= 100000, and 1 <= properties[i][1] <= 100000. -/
  theorem spec_3 (properties : Slice (alloc.vec.Vec Std.I64))
      (h : BaseConstraints (rowsVal properties)) :
      ∀ r : Std.I64, number_of_weak_characters properties = ok r →
        0 ≤ r.val ∧ r.val ≤ (properties.val.length : Int) - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (properties : Slice (alloc.vec.Vec Std.I64))
        (h : BaseConstraints (rowsVal properties)), ∀ r : Std.I64, number_of_weak_characters properties = ok r →
          0 ≤ r.val ∧ r.val ≤ (properties.val.length : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: 2 <= len(properties) <= 100000; for every i with 0 <= i < len(properties), len(properties[i]) = 2, 1 <= properties[i][0] <= 100000, and 1 <= properties[i][1] <= 100000; there exists an integer d such that for every i with 0 <= i < len(properties), properties[i][1] = d. -/
  theorem spec_4 (properties : Slice (alloc.vec.Vec Std.I64))
      (h : BaseConstraints (rowsVal properties))
      (hd : ∃ d : Int, ∀ r ∈ rowsVal properties, defense r = d) :
      ∀ r : Std.I64, number_of_weak_characters properties = ok r → r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (properties : Slice (alloc.vec.Vec Std.I64))
        (h : BaseConstraints (rowsVal properties))
        (hd : ∃ d : Int, ∀ r ∈ rowsVal properties, defense r = d), ∀ r : Std.I64, number_of_weak_characters properties = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r on properties and a result r' on properties', r = r'.
    Preconditions: Both properties and properties' satisfy the base constraints: 2 <= len(properties) <= 100000, 2 <= len(properties') <= 100000, and for every i in the respective list, len of the row is 2 with both coordinates between 1 and 100000. Also len(properties') = len(properties) and there exists a bijection pi from {0,...,len(properties)-1} to itself such that properties'[i] = properties[pi(i)] for every i. -/
  theorem spec_5 (properties properties' : Slice (alloc.vec.Vec Std.I64))
      (h : BaseConstraints (rowsVal properties))
      (h' : BaseConstraints (rowsVal properties'))
      (hlen : (rowsVal properties').length = (rowsVal properties).length)
      (hπ : IsRelabeling (rowsVal properties) (rowsVal properties')) :
      ∀ r r' : Std.I64, number_of_weak_characters properties = ok r →
        number_of_weak_characters properties' = ok r' → r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (properties properties' : Slice (alloc.vec.Vec Std.I64))
        (h : BaseConstraints (rowsVal properties))
        (h' : BaseConstraints (rowsVal properties'))
        (hlen : (rowsVal properties').length = (rowsVal properties).length)
        (hπ : IsRelabeling (rowsVal properties) (rowsVal properties')), ∀ r r' : Std.I64, number_of_weak_characters properties = ok r →
          number_of_weak_characters properties' = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r' on properties', r' = len(properties).
    Preconditions: properties satisfies the base constraints: 2 <= len(properties) <= 100000, every row has length 2, and both coordinates are between 1 and 100000. Let n = len(properties), assume n < 100000. Let q be a pair with 1 <= q[0] <= 100000 and 1 <= q[1] <= 100000 such that for every i with 0 <= i < n, q[0] > properties[i][0] and q[1] > properties[i][1]. Let properties' be the list of length n+1 with properties'[i] = properties[i] for 0 <= i < n and properties'[n] = q. Then properties' also satisfies the base constraints. -/
  theorem spec_6 (properties properties' : Slice (alloc.vec.Vec Std.I64))
      (q0 q1 : Int)
      (h : BaseConstraints (rowsVal properties))
      (hn : (rowsVal properties).length < 100000)
      (hq0 : 1 ≤ q0) (hq0' : q0 ≤ 100000) (hq1 : 1 ≤ q1) (hq1' : q1 ≤ 100000)
      (hdom : ∀ r ∈ rowsVal properties, attack r < q0 ∧ defense r < q1)
      (h' : rowsVal properties' = rowsVal properties ++ [[q0, q1]])
      (hbase' : BaseConstraints (rowsVal properties')) :
      ∀ r' : Std.I64, number_of_weak_characters properties' = ok r' →
        r'.val = ((rowsVal properties).length : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (properties properties' : Slice (alloc.vec.Vec Std.I64))
        (q0 q1 : Int)
        (h : BaseConstraints (rowsVal properties))
        (hn : (rowsVal properties).length < 100000)
        (hq0 : 1 ≤ q0) (hq0' : q0 ≤ 100000) (hq1 : 1 ≤ q1) (hq1' : q1 ≤ 100000)
        (hdom : ∀ r ∈ rowsVal properties, attack r < q0 ∧ defense r < q1)
        (h' : rowsVal properties' = rowsVal properties ++ [[q0, q1]])
        (hbase' : BaseConstraints (rowsVal properties')), ∀ r' : Std.I64, number_of_weak_characters properties' = ok r' →
          r'.val = ((rowsVal properties).length : Int)) := by
    sorry

  /-- Whenever the function returns a result r on properties and a result r' on properties', r' = r + 1.
    Preconditions: properties satisfies the base constraints: 2 <= len(properties) <= 100000, every row has length 2, and both coordinates are between 1 and 100000. Let n = len(properties), assume n < 100000. Let q be a pair with 1 <= q[0] <= 100000 and 1 <= q[1] <= 100000 such that for every i with 0 <= i < n, q[0] < properties[i][0] and q[1] < properties[i][1]. Let properties' be the list of length n+1 with properties'[i] = properties[i] for 0 <= i < n and properties'[n] = q. Then properties' also satisfies the base constraints. -/
  theorem spec_7 (properties properties' : Slice (alloc.vec.Vec Std.I64))
      (q0 q1 : Int)
      (h : BaseConstraints (rowsVal properties))
      (hn : (rowsVal properties).length < 100000)
      (hq0 : 1 ≤ q0) (hq0' : q0 ≤ 100000) (hq1 : 1 ≤ q1) (hq1' : q1 ≤ 100000)
      (hdom : ∀ r ∈ rowsVal properties, q0 < attack r ∧ q1 < defense r)
      (h' : rowsVal properties' = rowsVal properties ++ [[q0, q1]])
      (hbase' : BaseConstraints (rowsVal properties')) :
      ∀ r r' : Std.I64, number_of_weak_characters properties = ok r →
        number_of_weak_characters properties' = ok r' → r'.val = r.val + 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (properties properties' : Slice (alloc.vec.Vec Std.I64))
        (q0 q1 : Int)
        (h : BaseConstraints (rowsVal properties))
        (hn : (rowsVal properties).length < 100000)
        (hq0 : 1 ≤ q0) (hq0' : q0 ≤ 100000) (hq1 : 1 ≤ q1) (hq1' : q1 ≤ 100000)
        (hdom : ∀ r ∈ rowsVal properties, q0 < attack r ∧ q1 < defense r)
        (h' : rowsVal properties' = rowsVal properties ++ [[q0, q1]])
        (hbase' : BaseConstraints (rowsVal properties')), ∀ r r' : Std.I64, number_of_weak_characters properties = ok r →
          number_of_weak_characters properties' = ok r' → r'.val = r.val + 1) := by
    sorry

  /-- Whenever the function returns a result r, r = len(properties) - 1 if and only if there exists an index k with 0 <= k < len(properties) such that for every j with 0 <= j < len(properties) and j != k, properties[k][0] > properties[j][0] and properties[k][1] > properties[j][1].
    Preconditions: 2 <= len(properties) <= 100000; for every i with 0 <= i < len(properties), len(properties[i]) = 2, 1 <= properties[i][0] <= 100000, and 1 <= properties[i][1] <= 100000. -/
  theorem spec_8 (properties : Slice (alloc.vec.Vec Std.I64))
      (h : BaseConstraints (rowsVal properties)) :
      ∀ r : Std.I64, number_of_weak_characters properties = ok r →
        (r.val = ((rowsVal properties).length : Int) - 1 ↔
          HasDominatingIndex (rowsVal properties)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (properties : Slice (alloc.vec.Vec Std.I64))
        (h : BaseConstraints (rowsVal properties)), ∀ r : Std.I64, number_of_weak_characters properties = ok r →
          (r.val = ((rowsVal properties).length : Int) - 1 ↔
            HasDominatingIndex (rowsVal properties))) := by
    sorry

  end AegisSpec.NumberOfWeakCharacters
