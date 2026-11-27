import Aegis.ReverseEvenLengthGroups.Code.Funs

/-!
# Specifications of `Aegis.ReverseEvenLengthGroups.reverse_even_length_groups`

LeetCode problem `reverse-nodes-in-even-length-groups`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace Aegis.ReverseEvenLengthGroups

def List.val : List → _root_.List Std.I64
  | List.Nil => []
  | List.Cons v next => v :: next.val

end Aegis.ReverseEvenLengthGroups

namespace AegisSpec.ReverseEvenLengthGroups

open Aeneas Aeneas.Std Result

def blockEnd (k : Nat) : Nat := k * (k + 1) / 2

def blockStart (k : Nat) : Nat := (k - 1) * k / 2

def blockLen (k n : Nat) : Nat := min k (n - blockStart k)

def nthVal (vs : _root_.List Std.I64) (i : Nat) : Int := (vs.getD i 0#i64).val

def countBetween (vs : _root_.List Std.I64) (x : Int) (s t : Nat) : Nat :=
  ((vs.drop s).take (t + 1 - s)).countP (fun v => decide (v.val = x))

/-- The function returns a result r. Let a_i be the value of the i-th node of head and b_i the value of the i-th node of r, for 0 <= i < n. Then len(r) = n, and for every i with 0 <= i < n, let k be the unique positive integer such that (k-1)*k/2 <= i < k*(k+1)/2, set s = (k-1)*k/2 and t = min(k*(k+1)/2, n) - 1. If t - s + 1 is even, then b_i = a_{s+t-i}; otherwise b_i = a_i.
  Preconditions: head is a finite linked list with n = len(head), where 1 <= n <= 100000, and every node value v in head satisfies 0 <= v <= 100000. -/
theorem spec_1 (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∃ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r ∧
      r.val.length = n ∧
      ∀ (i k : Nat), i < n → 1 ≤ k → blockStart k ≤ i → i < blockEnd k →
        (let s := blockStart k
         let t := min (blockEnd k) n - 1
         if (t - s + 1) % 2 = 0 then nthVal r.val i = nthVal head.val (s + t - i)
         else nthVal r.val i = nthVal head.val i) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000), ∃ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r ∧
      r.val.length = n ∧
      ∀ (i k : Nat), i < n → 1 ≤ k → blockStart k ≤ i → i < blockEnd k →
        (let s := blockStart k
         let t := min (blockEnd k) n - 1
         if (t - s + 1) % 2 = 0 then nthVal r.val i = nthVal head.val (s + t - i)
         else nthVal r.val i = nthVal head.val i)) := by
  sorry

/-- The function does not fail: for every such head, reverse_even_length_groups(head) returns a result r, with no out-of-bounds access, panic, or 64-bit arithmetic overflow.
  Preconditions: head is a finite linked list with n = len(head), where 1 <= n <= 100000, and every node value v in head satisfies 0 <= v <= 100000. -/
theorem spec_2 (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∃ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000), ∃ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = n.
  Preconditions: head is a finite linked list with n = len(head), where 1 <= n <= 100000, and every node value v in head satisfies 0 <= v <= 100000. -/
theorem spec_3 (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∀ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r →
      r.val.length = n := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000), ∀ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r →
      r.val.length = n) := by
  sorry

/-- Let a_i be the value of the i-th node of head for 0 <= i < n. Whenever the function returns a result r with len(r) = n, let b_i be the value of the i-th node of r. For every positive integer k with s = (k-1)*k/2 < n, let len_k = min(k, n-s) and t = s+len_k-1. For every integer x, the number of indices i with s <= i <= t and b_i = x equals the number of indices i with s <= i <= t and a_i = x.
  Preconditions: head is a finite linked list with n = len(head), where 1 <= n <= 100000, and every node value v in head satisfies 0 <= v <= 100000. -/
theorem spec_4 (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∀ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r →
      r.val.length = n →
      ∀ k, 1 ≤ k → blockStart k < n →
        ∀ x : Int,
          countBetween r.val x (blockStart k) (blockStart k + blockLen k n - 1) =
            countBetween head.val x (blockStart k) (blockStart k + blockLen k n - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000), ∀ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r →
      r.val.length = n →
      ∀ k, 1 ≤ k → blockStart k < n →
        ∀ x : Int,
          countBetween r.val x (blockStart k) (blockStart k + blockLen k n - 1) =
            countBetween head.val x (blockStart k) (blockStart k + blockLen k n - 1)) := by
  sorry

/-- Let a_i be the value of the i-th node of head for 0 <= i < n. Whenever the function returns a result r with len(r) = n, let b_i be the value of the i-th node of r. For every positive integer k with s = (k-1)*k/2 < n, let len_k = min(k, n-s). If len_k is odd, then for every j with 0 <= j < len_k, b_{s+j} = a_{s+j}.
  Preconditions: head is a finite linked list with n = len(head), where 1 <= n <= 100000, and every node value v in head satisfies 0 <= v <= 100000. -/
theorem spec_5 (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∀ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r →
      r.val.length = n →
      ∀ k, 1 ≤ k → blockStart k < n → blockLen k n % 2 = 1 →
        ∀ j, j < blockLen k n →
          nthVal r.val (blockStart k + j) = nthVal head.val (blockStart k + j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000), ∀ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r →
      r.val.length = n →
      ∀ k, 1 ≤ k → blockStart k < n → blockLen k n % 2 = 1 →
        ∀ j, j < blockLen k n →
          nthVal r.val (blockStart k + j) = nthVal head.val (blockStart k + j)) := by
  sorry

/-- Let a_i be the value of the i-th node of head for 0 <= i < n. Whenever the function returns a result r with len(r) = n, let b_i be the value of the i-th node of r. For every positive integer k with s = (k-1)*k/2 < n, let len_k = min(k, n-s). If len_k is even, then for every j with 0 <= j < len_k, b_{s+j} = a_{s+len_k-1-j}.
  Preconditions: head is a finite linked list with n = len(head), where 1 <= n <= 100000, and every node value v in head satisfies 0 <= v <= 100000. -/
theorem spec_6 (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∀ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r →
      r.val.length = n →
      ∀ k, 1 ≤ k → blockStart k < n → blockLen k n % 2 = 0 →
        ∀ j, j < blockLen k n →
          nthVal r.val (blockStart k + j) =
            nthVal head.val (blockStart k + blockLen k n - 1 - j) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000), ∀ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r →
      r.val.length = n →
      ∀ k, 1 ≤ k → blockStart k < n → blockLen k n % 2 = 0 →
        ∀ j, j < blockLen k n →
          nthVal r.val (blockStart k + j) =
            nthVal head.val (blockStart k + blockLen k n - 1 - j)) := by
  sorry

/-- For every such head, let r be the result of reverse_even_length_groups(head), and let r2 be the result of reverse_even_length_groups(r). Then r2 has the same node values in the same order as head.
  Preconditions: head is a finite linked list with n = len(head), where 1 <= n <= 100000, and every node value v in head satisfies 0 <= v <= 100000. -/
theorem spec_7 (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∃ r r2, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r ∧
      Aegis.ReverseEvenLengthGroups.reverse_even_length_groups r = ok r2 ∧
      r2.val = head.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000), ∃ r r2, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r ∧
      Aegis.ReverseEvenLengthGroups.reverse_even_length_groups r = ok r2 ∧
      r2.val = head.val) := by
  sorry

/-- Whenever the function returns a result r, every node value v in r satisfies 0 <= v <= 100000.
  Preconditions: head is a finite linked list with n = len(head), where 1 <= n <= 100000, and every node value v in head satisfies 0 <= v <= 100000. -/
theorem spec_8 (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∀ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r →
      ∀ v ∈ r.val, 0 ≤ v.val ∧ v.val ≤ 100000 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.ReverseEvenLengthGroups.List) (n : Nat)
    (hn : head.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hv : ∀ v ∈ head.val, 0 ≤ v.val ∧ v.val ≤ 100000), ∀ r, Aegis.ReverseEvenLengthGroups.reverse_even_length_groups head = ok r →
      ∀ v ∈ r.val, 0 ≤ v.val ∧ v.val ≤ 100000) := by
  sorry

end AegisSpec.ReverseEvenLengthGroups
