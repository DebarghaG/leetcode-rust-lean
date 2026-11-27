import Aegis.Permute.Code.Funs

/-!
# Specifications of `Aegis.Permute.permute`

LeetCode problem `permutations-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Permute

  def vals (v : alloc.vec.Vec Std.I64) : List Int := v.val.map fun x => x.val

  def rows (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List Int) := r.val.map vals

  def OppParity : List Int → Prop
    | [] => True
    | [_] => True
    | x :: y :: rest => x % 2 ≠ y % 2 ∧ OppParity (y :: rest)

  def LexLt (p q : List Int) : Prop :=
    ∃ (j : Nat) (hp : j < p.length) (hq : j < q.length),
      p.take j = q.take j ∧ p[j]'hp < q[j]'hq

  def StrictLexSorted : List (List Int) → Prop
    | [] => True
    | [_] => True
    | p :: q :: rest => LexLt p q ∧ StrictLexSorted (q :: rest)

  def IsAltPerm (n : Nat) (l : List Int) : Prop :=
    l.length = n ∧ l.Nodup ∧ (∀ x ∈ l, 1 ≤ x ∧ x ≤ (n : Int)) ∧ OppParity l

  def EnumeratesAltPerms (n : Nat) (rs : List (List Int)) : Prop :=
    (∀ p ∈ rs, IsAltPerm n p) ∧ (∀ p, IsAltPerm n p → p ∈ rs) ∧
      rs.Nodup ∧ StrictLexSorted rs

  def OddAtEvenPositions (l : List Int) : Prop :=
    ∀ (i : Nat) (x : Int), l[i]? = some x → (x % 2 = 1 ↔ i % 2 = 0)

  def OddAtOddPositions (l : List Int) : Prop :=
    ∀ (i : Nat) (x : Int), l[i]? = some x → (x % 2 = 1 ↔ i % 2 = 1)

  /-- The function returns a result r (it does not fail) such that r is exactly the list of all alternating permutations of {1,2,...,n}, each appearing once, in strictly increasing lexicographic order. An alternating permutation of {1,...,n} is a vector p with len(p)=n, whose entries are pairwise distinct and all lie in {1,...,n}, and such that for every i with 0 <= i < n-1, p[i] and p[i+1] have opposite parity (one is odd and the other is even). Strictly increasing lexicographic order means that for every k with 0 <= k < r.length-1, there is an index j with 0 <= j < n such that r[k][t]=r[k+1][t] for all t with 0 <= t < j and r[k][j] < r[k+1][j].
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∃ r, Aegis.Permute.permute n = ok r ∧ EnumeratesAltPerms n.val.toNat (rows r) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∃ r, Aegis.Permute.permute n = ok r ∧ EnumeratesAltPerms n.val.toNat (rows r)) := by
    sorry

  /-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, panic, or allocation failure).
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∃ r, Aegis.Permute.permute n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∃ r, Aegis.Permute.permute n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, every inner vector has length n: for every k with 0 <= k < r.length, len(r[k]) = n.
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∀ r, Aegis.Permute.permute n = ok r →
        ∀ (k : Nat) (hk : k < r.val.length), (vals (r.val[k])).length = n.val.toNat := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∀ r, Aegis.Permute.permute n = ok r →
          ∀ (k : Nat) (hk : k < r.val.length), (vals (r.val[k])).length = n.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, every entry of every inner vector is in the range from 1 to n inclusive: for every k with 0 <= k < r.length and every i with 0 <= i < n, 1 <= r[k][i] <= n.
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∀ r, Aegis.Permute.permute n = ok r →
        ∀ (k : Nat) (hk : k < r.val.length) (i : Nat) (hi : i < n.val.toNat),
          ∃ x : Int, (vals (r.val[k]))[i]? = some x ∧ 1 ≤ x ∧ x ≤ n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∀ r, Aegis.Permute.permute n = ok r →
          ∀ (k : Nat) (hk : k < r.val.length) (i : Nat) (hi : i < n.val.toNat),
            ∃ x : Int, (vals (r.val[k]))[i]? = some x ∧ 1 ≤ x ∧ x ≤ n.val) := by
    sorry

  /-- Whenever the function returns a result r, the entries of each inner vector are pairwise distinct: for every k with 0 <= k < r.length and all i,j with 0 <= i < j < n, r[k][i] != r[k][j].
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∀ r, Aegis.Permute.permute n = ok r →
        ∀ (k : Nat) (hk : k < r.val.length) (i j : Nat), i < j → j < n.val.toNat →
          ∃ x y : Int, (vals (r.val[k]))[i]? = some x ∧
            (vals (r.val[k]))[j]? = some y ∧ x ≠ y := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∀ r, Aegis.Permute.permute n = ok r →
          ∀ (k : Nat) (hk : k < r.val.length) (i j : Nat), i < j → j < n.val.toNat →
            ∃ x y : Int, (vals (r.val[k]))[i]? = some x ∧
              (vals (r.val[k]))[j]? = some y ∧ x ≠ y) := by
    sorry

  /-- Whenever the function returns a result r, adjacent entries of each inner vector have opposite parity: for every k with 0 <= k < r.length and every i with 0 <= i < n-1, (r[k][i] mod 2) != (r[k][i+1] mod 2).
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_6 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∀ r, Aegis.Permute.permute n = ok r →
        ∀ (k : Nat) (hk : k < r.val.length), OppParity (vals (r.val[k])) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∀ r, Aegis.Permute.permute n = ok r →
          ∀ (k : Nat) (hk : k < r.val.length), OppParity (vals (r.val[k]))) := by
    sorry

  /-- Whenever the function returns a result r, every alternating permutation of {1,...,n} occurs in r: for every vector p with len(p)=n, with pairwise distinct entries all in {1,...,n}, and with (p[i] mod 2) != (p[i+1] mod 2) for every 0 <= i < n-1, there exists k with 0 <= k < r.length such that r[k][i]=p[i] for all i with 0 <= i < n.
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_7 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∀ r, Aegis.Permute.permute n = ok r →
        ∀ p : List Int, IsAltPerm n.val.toNat p → p ∈ rows r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∀ r, Aegis.Permute.permute n = ok r →
          ∀ p : List Int, IsAltPerm n.val.toNat p → p ∈ rows r) := by
    sorry

  /-- Whenever the function returns a result r, no two inner vectors are equal: for all k,l with 0 <= k < l < r.length, there exists i with 0 <= i < n such that r[k][i] != r[l][i].
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_8 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∀ r, Aegis.Permute.permute n = ok r → (rows r).Nodup := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∀ r, Aegis.Permute.permute n = ok r → (rows r).Nodup) := by
    sorry

  /-- Whenever the function returns a result r, the inner vectors are in strictly increasing lexicographic order: for every k with 0 <= k < r.length-1, there exists j with 0 <= j < n such that r[k][t]=r[k+1][t] for all t with 0 <= t < j and r[k][j] < r[k+1][j].
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_9 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∀ r, Aegis.Permute.permute n = ok r → StrictLexSorted (rows r) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∀ r, Aegis.Permute.permute n = ok r → StrictLexSorted (rows r)) := by
    sorry

  /-- Whenever the function returns a result r, r is nonempty and its first inner vector is the identity permutation [1,2,...,n]: r.length > 0 and for every i with 0 <= i < n, r[0][i] = i+1.
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_10 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∀ r, Aegis.Permute.permute n = ok r →
        0 < r.val.length ∧
          ∀ row : List Int, (rows r).head? = some row →
            ∀ (i : Nat) (hi : i < n.val.toNat), row[i]? = some ((i : Int) + 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∀ r, Aegis.Permute.permute n = ok r →
          0 < r.val.length ∧
            ∀ row : List Int, (rows r).head? = some row →
              ∀ (i : Nat) (hi : i < n.val.toNat), row[i]? = some ((i : Int) + 1)) := by
    sorry

  /-- Whenever the function returns a result r, r is nonempty and its last inner vector is the descending permutation [n,n-1,...,1]: r.length > 0 and for every i with 0 <= i < n, r[r.length-1][i] = n-i.
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_11 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∀ r, Aegis.Permute.permute n = ok r →
        0 < r.val.length ∧
          ∀ row : List Int, (rows r).getLast? = some row →
            ∀ (i : Nat) (hi : i < n.val.toNat), row[i]? = some (n.val - (i : Int)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∀ r, Aegis.Permute.permute n = ok r →
          0 < r.val.length ∧
            ∀ row : List Int, (rows r).getLast? = some row →
              ∀ (i : Nat) (hi : i < n.val.toNat), row[i]? = some (n.val - (i : Int))) := by
    sorry

  /-- Whenever the function returns a result r, every inner vector has odd entries in even positions and even entries in odd positions: for every k with 0 <= k < r.length and every i with 0 <= i < n, (r[k][i] mod 2 = 1) if and only if i is even.
    Preconditions: n is an integer satisfying 1 <= n <= 10 and n is odd. -/
  theorem spec_12 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) (hodd : n.val % 2 = 1) :
      ∀ r, Aegis.Permute.permute n = ok r →
        ∀ (k : Nat) (hk : k < r.val.length), OddAtEvenPositions (vals (r.val[k])) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) (hodd : n.val % 2 = 1), ∀ r, Aegis.Permute.permute n = ok r →
          ∀ (k : Nat) (hk : k < r.val.length), OddAtEvenPositions (vals (r.val[k]))) := by
    sorry

  /-- Whenever the function returns a result r, each inner vector uses one of the two possible alternating parity patterns: for every k with 0 <= k < r.length, either (for all i with 0 <= i < n, r[k][i] mod 2 = 1 if and only if i is even) or (for all i with 0 <= i < n, r[k][i] mod 2 = 1 if and only if i is odd).
    Preconditions: n is an integer satisfying 1 <= n <= 10 and n is even. -/
  theorem spec_13 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) (heven : n.val % 2 = 0) :
      ∀ r, Aegis.Permute.permute n = ok r →
        ∀ (k : Nat) (hk : k < r.val.length),
          OddAtEvenPositions (vals (r.val[k])) ∨ OddAtOddPositions (vals (r.val[k])) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) (heven : n.val % 2 = 0), ∀ r, Aegis.Permute.permute n = ok r →
          ∀ (k : Nat) (hk : k < r.val.length),
            OddAtEvenPositions (vals (r.val[k])) ∨ OddAtOddPositions (vals (r.val[k]))) := by
    sorry

  /-- Whenever the function returns a result r, the length of r equals the number of alternating permutations of {1,...,n}. Concretely, if n is odd then r.length = ((n+1)/2)! * ((n-1)/2)!, and if n is even then r.length = 2 * ((n/2)!)^2, where m! denotes the factorial 1*2*...*m with 0!=1.
    Preconditions: n is an integer satisfying 1 <= n <= 10. -/
  theorem spec_14 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
      ∀ r, Aegis.Permute.permute n = ok r →
        (n.val % 2 = 1 →
            r.val.length =
              ((n.val.toNat + 1) / 2).factorial * ((n.val.toNat - 1) / 2).factorial) ∧
          (n.val % 2 = 0 →
            r.val.length = 2 * ((n.val.toNat / 2).factorial) ^ 2) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∀ r, Aegis.Permute.permute n = ok r →
          (n.val % 2 = 1 →
              r.val.length =
                ((n.val.toNat + 1) / 2).factorial * ((n.val.toNat - 1) / 2).factorial) ∧
            (n.val % 2 = 0 →
              r.val.length = 2 * ((n.val.toNat / 2).factorial) ^ 2)) := by
    sorry

  end AegisSpec.Permute
