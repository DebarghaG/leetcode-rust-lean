import Aegis.GetPermutationIndex.Code.Funs

/-!
# Specifications of `Aegis.GetPermutationIndex.get_permutation_index`

LeetCode problem `find-the-index-of-permutation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetPermutationIndex

def M : Int := 1000000007

def vals (perm : Slice I64) : List Int := perm.val.map (fun x => x.val)

def rangeList (n : Nat) : List Int := (List.range n).map (fun k => (k : Int) + 1)

def IsPermOfRange (n : Nat) (l : List Int) : Prop := l.Perm (rangeList n)

def compList (n : Nat) (l : List Int) : List Int := l.map (fun x => (n : Int) + 1 - x)

def lexLtB : List Int → List Int → Bool
  | [], _ => false
  | _ :: _, [] => false
  | a :: u, b :: v => if a < b then true else if b < a then false else lexLtB u v

def lexLt (p q : List Int) : Prop := lexLtB p q = true

def IsImmediateLexSucc (n : Nat) (p q : List Int) : Prop :=
  lexLt p q ∧ ∀ s : List Int, IsPermOfRange n s → lexLt p s → lexLt s q → False

def allPermsOf (n : Nat) : List (List Int) := (rangeList n).permutations

def numSmallerPerms (n : Nat) (l : List Int) : Nat :=
  (allPermsOf n).countP (fun q => lexLtB q l)

def countSmallerAfter (l : List Int) (i : Nat) : Nat :=
  ((l.drop (i + 1)).filter (fun x => x < l.getD i 0)).length

def lehmerSum (l : List Int) : Int :=
  ((List.range l.length).map
      (fun i => (countSmallerAfter l i : Int) * (Nat.factorial (l.length - 1 - i) : Int))).sum

abbrev gpi (perm : Slice I64) : Result I64 := Aegis.GetPermutationIndex.get_permutation_index perm

/-- Whenever the function returns a result r, r is the unique integer with 0 <= r < M such that r is congruent modulo M to N(perm), where N(perm) is the number of permutations q of {1,2,...,n} that are lexicographically strictly less than perm. Equivalently, r is the 0-based index of perm in the lexicographically sorted list of all permutations of {1,2,...,n}, reduced modulo M. Lexicographic comparison means comparing entries from left to right and, at the first position where two permutations differ, the one with the smaller entry comes first.
  Preconditions: Let n = len(perm) and M = 10^9 + 7. The slice has 0-based indices. Assume 1 <= n <= 10^5 and perm is a permutation of {1,2,...,n}: for every i with 0 <= i < n, 1 <= perm[i] <= n, and for every i,j with 0 <= i < j < n, perm[i] != perm[j]. -/
theorem spec_1 (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j]) :
    ∀ r : I64, gpi perm = ok r →
      0 ≤ r.val ∧ r.val < M ∧
        r.val = ((numSmallerPerms (vals perm).length (vals perm) : Int) % M) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j]), ∀ r : I64, gpi perm = ok r →
      0 ≤ r.val ∧ r.val < M ∧
        r.val = ((numSmallerPerms (vals perm).length (vals perm) : Int) % M)) := by
  sorry

/-- For every perm satisfying the preconditions, the function returns a result r; it does not fail, panic, or report arithmetic overflow.
  Preconditions: Let n = len(perm) and M = 10^9 + 7. Assume 1 <= n <= 10^5 and perm is a permutation of {1,2,...,n}: for every i with 0 <= i < n, 1 <= perm[i] <= n, and for every i,j with 0 <= i < j < n, perm[i] != perm[j]. -/
theorem spec_2 (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j]) :
    ∃ r : I64, gpi perm = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j]), ∃ r : I64, gpi perm = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(perm) and M = 10^9 + 7. Assume 1 <= n <= 10^5, perm is a permutation of {1,2,...,n}, and for every i with 0 <= i < n, perm[i] = i + 1. -/
theorem spec_3 (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_id : ∀ (i : Nat) (hi : i < (vals perm).length), (vals perm)[i] = (i : Int) + 1) :
    ∀ r : I64, gpi perm = ok r → r.val = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_id : ∀ (i : Nat) (hi : i < (vals perm).length), (vals perm)[i] = (i : Int) + 1), ∀ r : I64, gpi perm = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = (n! - 1) mod M, where n! = 1 * 2 * ... * n is the number of permutations of {1,2,...,n}.
  Preconditions: Let n = len(perm) and M = 10^9 + 7. Assume 1 <= n <= 10^5, perm is a permutation of {1,2,...,n}, and for every i with 0 <= i < n, perm[i] = n - i. -/
theorem spec_4 (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_rev : ∀ (i : Nat) (hi : i < (vals perm).length),
      (vals perm)[i] = ((vals perm).length : Int) - (i : Int)) :
    ∀ r : I64, gpi perm = ok r →
      r.val = ((Nat.factorial (vals perm).length : Int) - 1) % M := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_rev : ∀ (i : Nat) (hi : i < (vals perm).length),
      (vals perm)[i] = ((vals perm).length : Int) - (i : Int)), ∀ r : I64, gpi perm = ok r →
      r.val = ((Nat.factorial (vals perm).length : Int) - 1) % M) := by
  sorry

/-- Whenever the function returns a result r, r = N exactly, so the modular reduction does not change the value; in particular 0 <= r < n!.
  Preconditions: Let n = len(perm) and M = 10^9 + 7. Assume 1 <= n <= 10^5, perm is a permutation of {1,2,...,n}, and n! <= M. Let N be the number of permutations q of {1,2,...,n} that are lexicographically strictly less than perm. -/
theorem spec_5 (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_fact : (Nat.factorial (vals perm).length : Int) ≤ M) :
    ∀ r : I64, gpi perm = ok r →
      r.val = (numSmallerPerms (vals perm).length (vals perm) : Int) ∧
        0 ≤ r.val ∧ r.val < (Nat.factorial (vals perm).length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_fact : (Nat.factorial (vals perm).length : Int) ≤ M), ∀ r : I64, gpi perm = ok r →
      r.val = (numSmallerPerms (vals perm).length (vals perm) : Int) ∧
        0 ≤ r.val ∧ r.val < (Nat.factorial (vals perm).length : Int)) := by
  sorry

/-- Whenever get_permutation_index(p) returns a result r_p and get_permutation_index(q) returns a result r_q, we have r_p < r_q.
  Preconditions: Let n and M = 10^9 + 7 be such that 2 <= n and n! <= M. Let p and q be two permutations of {1,2,...,n}, represented as slices. Suppose p is lexicographically strictly less than q. -/
theorem spec_6 (n : Nat) (p q : Slice I64)
    (h_two : 2 ≤ n)
    (h_fact : (Nat.factorial n : Int) ≤ M)
    (h_len_p : (vals p).length = n)
    (h_len_q : (vals q).length = n)
    (h_bounds_p : ∀ (i : Nat) (hi : i < (vals p).length),
      1 ≤ (vals p)[i] ∧ (vals p)[i] ≤ ((vals p).length : Int))
    (h_distinct_p : ∀ (i j : Nat) (hi : i < (vals p).length) (hj : j < (vals p).length),
      i < j → (vals p)[i] ≠ (vals p)[j])
    (h_bounds_q : ∀ (i : Nat) (hi : i < (vals q).length),
      1 ≤ (vals q)[i] ∧ (vals q)[i] ≤ ((vals q).length : Int))
    (h_distinct_q : ∀ (i j : Nat) (hi : i < (vals q).length) (hj : j < (vals q).length),
      i < j → (vals q)[i] ≠ (vals q)[j])
    (h_lt : lexLt (vals p) (vals q)) :
    ∀ (r_p r_q : I64), gpi p = ok r_p → gpi q = ok r_q → r_p.val < r_q.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Nat) (p q : Slice I64)
    (h_two : 2 ≤ n)
    (h_fact : (Nat.factorial n : Int) ≤ M)
    (h_len_p : (vals p).length = n)
    (h_len_q : (vals q).length = n)
    (h_bounds_p : ∀ (i : Nat) (hi : i < (vals p).length),
      1 ≤ (vals p)[i] ∧ (vals p)[i] ≤ ((vals p).length : Int))
    (h_distinct_p : ∀ (i j : Nat) (hi : i < (vals p).length) (hj : j < (vals p).length),
      i < j → (vals p)[i] ≠ (vals p)[j])
    (h_bounds_q : ∀ (i : Nat) (hi : i < (vals q).length),
      1 ≤ (vals q)[i] ∧ (vals q)[i] ≤ ((vals q).length : Int))
    (h_distinct_q : ∀ (i j : Nat) (hi : i < (vals q).length) (hj : j < (vals q).length),
      i < j → (vals q)[i] ≠ (vals q)[j])
    (h_lt : lexLt (vals p) (vals q)), ∀ (r_p r_q : I64), gpi p = ok r_p → gpi q = ok r_q → r_p.val < r_q.val) := by
  sorry

/-- Whenever get_permutation_index(p) returns a result r_p and get_permutation_index(q) returns a result r_q, r_q = (r_p + 1) mod M.
  Preconditions: Let n and M = 10^9 + 7 be such that 2 <= n <= 10^5. Let p and q be two permutations of {1,2,...,n}, represented as slices, such that q is the immediate lexicographic successor of p among all permutations of {1,2,...,n}: p is lexicographically less than q, and there is no permutation s of {1,2,...,n} with p lexicographically less than s and s lexicographically less than q. -/
theorem spec_7 (n : Nat) (p q : Slice I64)
    (h_two : 2 ≤ n)
    (h_n_le : n ≤ 10 ^ 5)
    (h_len_p : (vals p).length = n)
    (h_len_q : (vals q).length = n)
    (h_bounds_p : ∀ (i : Nat) (hi : i < (vals p).length),
      1 ≤ (vals p)[i] ∧ (vals p)[i] ≤ ((vals p).length : Int))
    (h_distinct_p : ∀ (i j : Nat) (hi : i < (vals p).length) (hj : j < (vals p).length),
      i < j → (vals p)[i] ≠ (vals p)[j])
    (h_bounds_q : ∀ (i : Nat) (hi : i < (vals q).length),
      1 ≤ (vals q)[i] ∧ (vals q)[i] ≤ ((vals q).length : Int))
    (h_distinct_q : ∀ (i j : Nat) (hi : i < (vals q).length) (hj : j < (vals q).length),
      i < j → (vals q)[i] ≠ (vals q)[j])
    (h_succ : IsImmediateLexSucc n (vals p) (vals q)) :
    ∀ (r_p r_q : I64), gpi p = ok r_p → gpi q = ok r_q → r_q.val = (r_p.val + 1) % M := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Nat) (p q : Slice I64)
    (h_two : 2 ≤ n)
    (h_n_le : n ≤ 10 ^ 5)
    (h_len_p : (vals p).length = n)
    (h_len_q : (vals q).length = n)
    (h_bounds_p : ∀ (i : Nat) (hi : i < (vals p).length),
      1 ≤ (vals p)[i] ∧ (vals p)[i] ≤ ((vals p).length : Int))
    (h_distinct_p : ∀ (i j : Nat) (hi : i < (vals p).length) (hj : j < (vals p).length),
      i < j → (vals p)[i] ≠ (vals p)[j])
    (h_bounds_q : ∀ (i : Nat) (hi : i < (vals q).length),
      1 ≤ (vals q)[i] ∧ (vals q)[i] ≤ ((vals q).length : Int))
    (h_distinct_q : ∀ (i j : Nat) (hi : i < (vals q).length) (hj : j < (vals q).length),
      i < j → (vals q)[i] ≠ (vals q)[j])
    (h_succ : IsImmediateLexSucc n (vals p) (vals q)), ∀ (r_p r_q : I64), gpi p = ok r_p → gpi q = ok r_q → r_q.val = (r_p.val + 1) % M) := by
  sorry

/-- Whenever get_permutation_index(perm) returns a result r and get_permutation_index(comp) returns a result r_c, we have (r + r_c) mod M = (n! - 1) mod M; equivalently r_c = (n! - 1 - r) mod M.
  Preconditions: Let n = len(perm) and M = 10^9 + 7. Assume 1 <= n <= 10^5 and perm is a permutation of {1,2,...,n}. Define comp to be the slice of length n with comp[i] = n + 1 - perm[i] for every i with 0 <= i < n; comp is also a permutation of {1,2,...,n}. -/
theorem spec_8 (n : Nat) (perm comp : Slice I64)
    (h_len_pos : 1 ≤ n)
    (h_n_le : n ≤ 10 ^ 5)
    (h_len : (vals perm).length = n)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_comp : vals comp = compList n (vals perm)) :
    ∀ (r r_c : I64), gpi perm = ok r → gpi comp = ok r_c →
      (r.val + r_c.val) % M = ((Nat.factorial n : Int) - 1) % M ∧
        r_c.val = ((Nat.factorial n : Int) - 1 - r.val) % M := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Nat) (perm comp : Slice I64)
    (h_len_pos : 1 ≤ n)
    (h_n_le : n ≤ 10 ^ 5)
    (h_len : (vals perm).length = n)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_comp : vals comp = compList n (vals perm)), ∀ (r r_c : I64), gpi perm = ok r → gpi comp = ok r_c →
      (r.val + r_c.val) % M = ((Nat.factorial n : Int) - 1) % M ∧
        r_c.val = ((Nat.factorial n : Int) - 1 - r.val) % M) := by
  sorry

/-- Whenever the function returns a result r, r = (sum for i = 0 to n-1 of c_i * (n - 1 - i)!) mod M.
  Preconditions: Let n = len(perm) and M = 10^9 + 7. Assume 1 <= n <= 10^5 and perm is a permutation of {1,2,...,n}. For each i with 0 <= i < n, let c_i be the number of indices j with i < j < n and perm[j] < perm[i]. Use 0! = 1. -/
theorem spec_9 (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j]) :
    ∀ r : I64, gpi perm = ok r → r.val = lehmerSum (vals perm) % M := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j]), ∀ r : I64, gpi perm = ok r → r.val = lehmerSum (vals perm) % M) := by
  sorry

/-- Whenever the function returns a result r, (k - 1) * (n - 1)! <= r <= k * (n - 1)! - 1.
  Preconditions: Let n = len(perm) and M = 10^9 + 7. Assume 1 <= n <= 10^5, perm is a permutation of {1,2,...,n}, and n! <= M. Let k = perm[0]. Use 0! = 1. -/
theorem spec_10 (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_fact : (Nat.factorial (vals perm).length : Int) ≤ M) :
    ∀ r : I64, gpi perm = ok r →
      (((vals perm).getD 0 0) - 1) * (Nat.factorial ((vals perm).length - 1) : Int) ≤ r.val ∧
        r.val ≤ ((vals perm).getD 0 0) * (Nat.factorial ((vals perm).length - 1) : Int) - 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_fact : (Nat.factorial (vals perm).length : Int) ≤ M), ∀ r : I64, gpi perm = ok r →
      (((vals perm).getD 0 0) - 1) * (Nat.factorial ((vals perm).length - 1) : Int) ≤ r.val ∧
        r.val ≤ ((vals perm).getD 0 0) * (Nat.factorial ((vals perm).length - 1) : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if perm[i] = i + 1 for every i with 0 <= i < n.
  Preconditions: Let n = len(perm) and M = 10^9 + 7. Assume 1 <= n <= 10^5, perm is a permutation of {1,2,...,n}, and n! <= M. -/
theorem spec_11 (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_fact : (Nat.factorial (vals perm).length : Int) ≤ M) :
    ∀ r : I64, gpi perm = ok r →
      (r.val = 0 ↔ ∀ (i : Nat) (hi : i < (vals perm).length), (vals perm)[i] = (i : Int) + 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (perm : Slice I64)
    (h_len_pos : 1 ≤ (vals perm).length)
    (h_len_le : (vals perm).length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : Nat) (hi : i < (vals perm).length),
      1 ≤ (vals perm)[i] ∧ (vals perm)[i] ≤ ((vals perm).length : Int))
    (h_distinct : ∀ (i j : Nat) (hi : i < (vals perm).length) (hj : j < (vals perm).length),
      i < j → (vals perm)[i] ≠ (vals perm)[j])
    (h_fact : (Nat.factorial (vals perm).length : Int) ≤ M), ∀ r : I64, gpi perm = ok r →
      (r.val = 0 ↔ ∀ (i : Nat) (hi : i < (vals perm).length), (vals perm)[i] = (i : Int) + 1)) := by
  sorry

end AegisSpec.GetPermutationIndex
