import Aegis.ReverseKGroup.Code.Funs

/-!
# Specifications of `Aegis.ReverseKGroup.reverse_k_group`

LeetCode problem `reverse-nodes-in-k-group`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace Aegis.ReverseKGroup

def List.val : List → _root_.List Int
  | List.Nil => []
  | List.Cons v next => v.val :: next.val

end Aegis.ReverseKGroup

namespace AegisSpec.ReverseKGroup
open Aegis.ReverseKGroup

def occ (v : Int) : _root_.List Int → Nat
  | [] => 0
  | y :: ys => (if y = v then 1 else 0) + occ v ys

/-- Whenever the function returns a result r (i.e., Ok r), let ys be the sequence of values in r. Then len(ys) = n, and for every j with 0 <= j < n / k (integer division) and every p with 0 <= p < k, we have ys[j*k + p] = xs[j*k + (k-1-p)], and for every i with k*(n/k) <= i < n, we have ys[i] = xs[i].
  Preconditions: Let n be the number of nodes in head, and let xs be the sequence of values in head (so xs[0] is the value of the first node, xs[1] the second, etc., and len(xs) = n). The preconditions are: 1 <= k, k <= n, n <= 5000, and for every i with 0 <= i < n, 0 <= xs[i] <= 1000. -/
theorem spec_1 (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000) :
    ∀ r : Aegis.ReverseKGroup.List, reverse_k_group head k = .ok r →
      r.val.length = head.val.length ∧
      (∀ j p : Nat, j < head.val.length / k.val.toNat → p < k.val.toNat →
        r.val.getD (j * k.val.toNat + p) 0
          = head.val.getD (j * k.val.toNat + (k.val.toNat - 1 - p)) 0) ∧
      (∀ i : Nat, k.val.toNat * (head.val.length / k.val.toNat) ≤ i →
        i < head.val.length → r.val.getD i 0 = head.val.getD i 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000), ∀ r : Aegis.ReverseKGroup.List, reverse_k_group head k = Result.ok r →
      r.val.length = head.val.length ∧
      (∀ j p : Nat, j < head.val.length / k.val.toNat → p < k.val.toNat →
        r.val.getD (j * k.val.toNat + p) 0
          = head.val.getD (j * k.val.toNat + (k.val.toNat - 1 - p)) 0) ∧
      (∀ i : Nat, k.val.toNat * (head.val.length / k.val.toNat) ≤ i →
        i < head.val.length → r.val.getD i 0 = head.val.getD i 0)) := by
  sorry

/-- The function returns a result r (i.e., Ok r).
  Preconditions: Let n be the number of nodes in head, and let xs be the sequence of values in head. The preconditions are: 1 <= k, k <= n, n <= 5000, and for every i with 0 <= i < n, 0 <= xs[i] <= 1000. -/
theorem spec_2 (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000) :
    ∃ r : Aegis.ReverseKGroup.List, reverse_k_group head k = .ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000), ∃ r : Aegis.ReverseKGroup.List, reverse_k_group head k = Result.ok r) := by
  sorry

/-- Whenever the function returns Ok r, the multiset of values in r equals the multiset of values in head. That is, for every integer v, the number of occurrences of v in r equals the number of occurrences of v in head.
  Preconditions: Let n be the number of nodes in head, and let xs be the sequence of values in head. The preconditions are: 1 <= k, k <= n, n <= 5000, and for every i with 0 <= i < n, 0 <= xs[i] <= 1000. -/
theorem spec_3 (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000) :
    ∀ r : Aegis.ReverseKGroup.List, reverse_k_group head k = .ok r →
      ∀ v : Int, occ v r.val = occ v head.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000), ∀ r : Aegis.ReverseKGroup.List, reverse_k_group head k = Result.ok r →
      ∀ v : Int, occ v r.val = occ v head.val) := by
  sorry

/-- Whenever the function returns Ok r, for every value v in r, 0 <= v <= 1000.
  Preconditions: Let n be the number of nodes in head, and let xs be the sequence of values in head. The preconditions are: 1 <= k, k <= n, n <= 5000, and for every i with 0 <= i < n, 0 <= xs[i] <= 1000. -/
theorem spec_4 (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000) :
    ∀ r : Aegis.ReverseKGroup.List, reverse_k_group head k = .ok r →
      ∀ v : Int, v ∈ r.val → 0 ≤ v ∧ v ≤ 1000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000), ∀ r : Aegis.ReverseKGroup.List, reverse_k_group head k = Result.ok r →
      ∀ v : Int, v ∈ r.val → 0 ≤ v ∧ v ≤ 1000) := by
  sorry

/-- For every input (head, k) satisfying the preconditions, if the function returns Ok r on (head, k) and returns Ok r2 on (r, k), then r2 = head.
  Preconditions: Let n be the number of nodes in head, and let xs be the sequence of values in head. The preconditions are: 1 <= k, k <= n, n <= 5000, and for every i with 0 <= i < n, 0 <= xs[i] <= 1000. -/
theorem spec_5 (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000) :
    ∀ r r2 : Aegis.ReverseKGroup.List,
      reverse_k_group head k = .ok r → reverse_k_group r k = .ok r2 → r2 = head := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000), ∀ r r2 : Aegis.ReverseKGroup.List,
      reverse_k_group head k = Result.ok r → reverse_k_group r k = Result.ok r2 → r2 = head) := by
  sorry

/-- Whenever the function returns Ok r, there exists a sequence of lists B_0, ..., B_{m-1} and a list T such that: head = B_0 ++ ... ++ B_{m-1} ++ T, for every j with 0 <= j < m, len(B_j) = k, len(T) < k, and r = reverse(B_0) ++ ... ++ reverse(B_{m-1}) ++ T, where m = n / k (integer division).
  Preconditions: Let n be the number of nodes in head, and let xs be the sequence of values in head. The preconditions are: 1 <= k, k <= n, n <= 5000, and for every i with 0 <= i < n, 0 <= xs[i] <= 1000. -/
theorem spec_6 (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000) :
    ∀ r : Aegis.ReverseKGroup.List, reverse_k_group head k = .ok r →
      ∃ (B : _root_.List (_root_.List Int)) (T : _root_.List Int),
        head.val = B.flatten ++ T ∧
        B.length = head.val.length / k.val.toNat ∧
        (∀ b ∈ B, b.length = k.val.toNat) ∧
        T.length < k.val.toNat ∧
        r.val = (B.map _root_.List.reverse).flatten ++ T := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.ReverseKGroup.List) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (head.val.length : Int))
    (hn_le : head.val.length ≤ 5000)
    (hxs : ∀ i : Nat, i < head.val.length →
      0 ≤ head.val.getD i 0 ∧ head.val.getD i 0 ≤ 1000), ∀ r : Aegis.ReverseKGroup.List, reverse_k_group head k = Result.ok r →
      ∃ (B : _root_.List (_root_.List Int)) (T : _root_.List Int),
        head.val = B.flatten ++ T ∧
        B.length = head.val.length / k.val.toNat ∧
        (∀ b ∈ B, b.length = k.val.toNat) ∧
        T.length < k.val.toNat ∧
        r.val = (B.map _root_.List.reverse).flatten ++ T) := by
  sorry

end AegisSpec.ReverseKGroup
