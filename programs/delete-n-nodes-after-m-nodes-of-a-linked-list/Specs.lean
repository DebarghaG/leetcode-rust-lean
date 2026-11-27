import Aegis.DeleteNodes.Code.Funs

/-!
# Specifications of `Aegis.DeleteNodes.delete_nodes`

LeetCode problem `delete-n-nodes-after-m-nodes-of-a-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DeleteNodes

abbrev LList : Type := Aegis.DeleteNodes.List

abbrev delete_nodes : LList → I64 → I64 → Result LList :=
  Aegis.DeleteNodes.delete_nodes

def contents : LList → List Int
  | .Nil => []
  | .Cons v next => v.val :: contents next

def keepNat (m : I64) : Nat := m.val.toNat

def delNat (n : I64) : Nat := n.val.toNat

def periodNat (m n : I64) : Nat := (m.val + n.val).toNat

def keptIndices (period keep len : Nat) : List Nat :=
  (List.range len).filter fun i => decide (i % period < keep)

def keptElems (period keep : Nat) (l : List Int) : List Int :=
  (keptIndices period keep l.length).filterMap fun i => l[i]?

def occCount (v : Int) (l : List Int) : Nat :=
  l.countP fun x => decide (x = v)

def keptOccCount (period keep : Nat) (v : Int) (l : List Int) : Nat :=
  ((keptIndices period keep l.length).filter fun i => decide (l[i]? = some v)).length

def IsKeptSubseqWitness (period keep : Nat) (l r : List Int) (f : Nat → Nat) : Prop :=
  (∀ k, k < r.length → f k < l.length ∧ f k % period < keep ∧ r[k]? = l[f k]?) ∧
    ∀ k, k + 1 < r.length → f k < f (k + 1)

def IsKeptEnumeration (period keep : Nat) (l r : List Int) (f : Nat → Nat) : Prop :=
  IsKeptSubseqWitness period keep l r f ∧
    ∀ j, j < l.length → j % period < keep → ∃ k, k < r.length ∧ f k = j

def countInInterval (f : Nat → Nat) (n lo hi : Nat) : Nat :=
  ((List.range n).filter fun t => decide (lo ≤ f t ∧ f t < hi)).length

/-- Whenever delete_nodes(head, m, n) returns a result r, r is exactly the list of the elements head[i] for all integers i with 0 <= i < len(head) and (i mod (m + n)) < m, taken in increasing order of i. Formally, let K be the number of such indices and let i_0 < i_1 < ... < i_{K-1} be those indices; then len(r) = K and for every k with 0 <= k < K, r[k] = head[i_k].
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, and for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000. -/
theorem spec_1 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r →
      contents r = keptElems (periodNat m n) (keepNat m) (contents head) ∧
        (contents r).length
          = (keptIndices (periodNat m n) (keepNat m) (contents head).length).length := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r →
      contents r = keptElems (periodNat m n) (keepNat m) (contents head) ∧
        (contents r).length
          = (keptIndices (periodNat m n) (keepNat m) (contents head).length).length) := by
  sorry

/-- Under the preconditions, delete_nodes(head, m, n) returns a result r (that is, it does not fail due to arithmetic overflow, out-of-bounds access, or panic).
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, and for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000. -/
theorem spec_2 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∃ r : LList, delete_nodes head m n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∃ r : LList, delete_nodes head m n = ok r) := by
  sorry

/-- Whenever delete_nodes(head, m, n) returns a result r, the length of r is len(r) = (len(head) / (m + n)) * m + min(len(head) mod (m + n), m), where / denotes integer division and mod denotes integer remainder.
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, and for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000. -/
theorem spec_3 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r →
      (contents r).length
        = (contents head).length / (periodNat m n) * (keepNat m)
            + min ((contents head).length % (periodNat m n)) (keepNat m) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r →
      (contents r).length
        = (contents head).length / (periodNat m n) * (keepNat m)
            + min ((contents head).length % (periodNat m n)) (keepNat m)) := by
  sorry

/-- Whenever delete_nodes(head, m, n) returns a result r, if len(head) > 0 then len(r) > 0 and r[0] = head[0].
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, and for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000. -/
theorem spec_4 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r → 0 < (contents head).length →
      0 < (contents r).length ∧ (contents r)[0]? = (contents head)[0]? := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r → 0 < (contents head).length →
      0 < (contents r).length ∧ (contents r)[0]? = (contents head)[0]?) := by
  sorry

/-- Whenever delete_nodes(head, m, n) returns a result r, under the additional precondition len(head) <= m + n, r is the prefix of head of length min(m, len(head)). That is, len(r) = min(m, len(head)) and for every i with 0 <= i < len(r), r[i] = head[i].
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000, and len(head) <= m + n. -/
theorem spec_5 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r → (contents head).length ≤ periodNat m n →
      (contents r).length = min (keepNat m) (contents head).length ∧
        ∀ i : Nat, i < (contents r).length → (contents r)[i]? = (contents head)[i]? := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r → (contents head).length ≤ periodNat m n →
      (contents r).length = min (keepNat m) (contents head).length ∧
        ∀ i : Nat, i < (contents r).length → (contents r)[i]? = (contents head)[i]?) := by
  sorry

/-- Whenever delete_nodes(head, m, n) returns a result r, under the additional precondition len(head) >= m, the first m elements of r are exactly the first m elements of head: for every j with 0 <= j < m, r[j] = head[j].
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000, and len(head) >= m. -/
theorem spec_6 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r → keepNat m ≤ (contents head).length →
      ∀ j : Nat, j < keepNat m → (contents r)[j]? = (contents head)[j]? := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r → keepNat m ≤ (contents head).length →
      ∀ j : Nat, j < keepNat m → (contents r)[j]? = (contents head)[j]?) := by
  sorry

/-- Whenever delete_nodes(head, m, n) returns a result r, there exists a strictly increasing sequence of indices 0 <= i_0 < i_1 < ... < i_{len(r)-1} < len(head) such that r[k] = head[i_k] for every k with 0 <= k < len(r), and for every k, (i_k mod (m + n)) < m.
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, and for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000. -/
theorem spec_7 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r →
      ∃ f : Nat → Nat,
        IsKeptSubseqWitness (periodNat m n) (keepNat m) (contents head) (contents r) f := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r →
      ∃ f : Nat → Nat,
        IsKeptSubseqWitness (periodNat m n) (keepNat m) (contents head) (contents r) f) := by
  sorry

/-- Whenever delete_nodes(head, m, n) returns a result r, for every integer value v, the number of occurrences of v in r equals the number of indices i with 0 <= i < len(head) such that head[i] = v and (i mod (m + n)) < m.
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, and for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000. -/
theorem spec_8 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r → ∀ v : Int,
      occCount v (contents r) = keptOccCount (periodNat m n) (keepNat m) v (contents head) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r → ∀ v : Int,
      occCount v (contents r) = keptOccCount (periodNat m n) (keepNat m) v (contents head)) := by
  sorry

/-- Whenever delete_nodes(head, m, n) returns a result r, if len(r) > 0, then r[len(r)-1] = head[L] where L is the largest integer i with 0 <= i < len(head) and (i mod (m + n)) < m.
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, and for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000. -/
theorem spec_9 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r → 0 < (contents r).length →
      ∃ L : Nat,
        L < (contents head).length ∧ L % (periodNat m n) < keepNat m ∧
          (∀ i : Nat, i < (contents head).length → i % (periodNat m n) < keepNat m → i ≤ L) ∧
            (contents r)[(contents r).length - 1]? = (contents head)[L]? := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r → 0 < (contents r).length →
      ∃ L : Nat,
        L < (contents head).length ∧ L % (periodNat m n) < keepNat m ∧
          (∀ i : Nat, i < (contents head).length → i % (periodNat m n) < keepNat m → i ≤ L) ∧
            (contents r)[(contents r).length - 1]? = (contents head)[L]?) := by
  sorry

/-- Whenever delete_nodes(head, m, n) returns a result r, for every integer k >= 0 such that (k + 1) * (m + n) <= len(head), the output r contains no element from the original positions k*(m+n) + m, k*(m+n) + m + 1, ..., k*(m+n) + m + n - 1. More precisely, if i_0 < i_1 < ... < i_{len(r)-1} are the indices witnessing that r is a subsequence of head (as in spec_7), then none of these indices lies in the interval [k*(m+n) + m, k*(m+n) + m + n - 1].
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, and for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000. -/
theorem spec_10 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r →
      ∀ f : Nat → Nat,
        IsKeptSubseqWitness (periodNat m n) (keepNat m) (contents head) (contents r) f →
          ∀ k : Nat, (k + 1) * (periodNat m n) ≤ (contents head).length →
            ∀ t : Nat, t < (contents r).length →
              ¬ (k * (periodNat m n) + keepNat m ≤ f t ∧
                  f t < k * (periodNat m n) + keepNat m + delNat n) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r →
      ∀ f : Nat → Nat,
        IsKeptSubseqWitness (periodNat m n) (keepNat m) (contents head) (contents r) f →
          ∀ k : Nat, (k + 1) * (periodNat m n) ≤ (contents head).length →
            ∀ t : Nat, t < (contents r).length →
              ¬ (k * (periodNat m n) + keepNat m ≤ f t ∧
                  f t < k * (periodNat m n) + keepNat m + delNat n)) := by
  sorry

/-- Whenever delete_nodes(head, m, n) returns a result r, 1 <= len(r) <= len(head).
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, and for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000. -/
theorem spec_11 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r →
      1 ≤ (contents r).length ∧ (contents r).length ≤ (contents head).length := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r →
      1 ≤ (contents r).length ∧ (contents r).length ≤ (contents head).length) := by
  sorry

/-- Whenever delete_nodes(head, m, n) returns a result r, let i_0 < i_1 < ... < i_{len(r)-1} be the increasing indices such that r[k] = head[i_k] for all k (as in spec_7). Then for every k with 0 <= k < len(r) - 1, the difference i_{k+1} - i_k is either 1 or n + 1.
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, and for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000. -/
theorem spec_12 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r →
      ∀ f : Nat → Nat,
        IsKeptEnumeration (periodNat m n) (keepNat m) (contents head) (contents r) f →
          ∀ k : Nat, k + 1 < (contents r).length →
            f (k + 1) - f k = 1 ∨ f (k + 1) - f k = delNat n + 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r →
      ∀ f : Nat → Nat,
        IsKeptEnumeration (periodNat m n) (keepNat m) (contents head) (contents r) f →
          ∀ k : Nat, k + 1 < (contents r).length →
            f (k + 1) - f k = 1 ∨ f (k + 1) - f k = delNat n + 1) := by
  sorry

/-- Whenever delete_nodes(head, m, n) returns a result r, for every integer k >= 0 such that (k + 1) * (m + n) <= len(head), the number of indices i in the interval [k*(m+n), (k+1)*(m+n)) that appear in the witness sequence from S7 is exactly m.
  Preconditions: 1 <= m <= 1000, 1 <= n <= 1000, 1 <= len(head) <= 10000, and for every i with 0 <= i < len(head), 1 <= head[i] <= 1000000. -/
theorem spec_13 (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000) :
    ∀ r : LList, delete_nodes head m n = ok r →
      ∀ f : Nat → Nat,
        IsKeptEnumeration (periodNat m n) (keepNat m) (contents head) (contents r) f →
          ∀ k : Nat, (k + 1) * (periodNat m n) ≤ (contents head).length →
            countInInterval f (contents r).length (k * (periodNat m n))
                ((k + 1) * (periodNat m n))
              = keepNat m := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (head : LList) (m n : I64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hlen_lo : 1 ≤ (contents head).length) (hlen_hi : (contents head).length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < (contents head).length),
      1 ≤ (contents head)[i] ∧ (contents head)[i] ≤ 1000000), ∀ r : LList, delete_nodes head m n = ok r →
      ∀ f : Nat → Nat,
        IsKeptEnumeration (periodNat m n) (keepNat m) (contents head) (contents r) f →
          ∀ k : Nat, (k + 1) * (periodNat m n) ≤ (contents head).length →
            countInInterval f (contents r).length (k * (periodNat m n))
                ((k + 1) * (periodNat m n))
              = keepNat m) := by
  sorry

end AegisSpec.DeleteNodes
