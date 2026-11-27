import Aegis.SwapNodes.Code.Funs

/-!
# Specifications of `Aegis.SwapNodes.swap_nodes`

LeetCode problem `swapping-nodes-in-a-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SwapNodes

def vals : Aegis.SwapNodes.List → List Std.I64
  | Aegis.SwapNodes.List.Nil => []
  | Aegis.SwapNodes.List.Cons v next => v :: vals next

def nth (vs : List Std.I64) (i : Nat) : Std.I64 := vs.getD i 0#i64

def swapIndex (n : Nat) (k : Std.I64) (i : Nat) : Nat :=
  if i = n - k.toNat then k.toNat - 1
  else if i = k.toNat - 1 then n - k.toNat
  else i

def countVal (x : Std.I64) : List Std.I64 → Nat
  | [] => 0
  | y :: ys => (if y = x then 1 else 0) + countVal x ys

/-- Whenever the function returns a result r, let u_0, u_1, ..., u_{m-1} be the values of r in order from its head. Then m = n, and for every i with 0 <= i < n, u_i = v_{j(i)}, where j(i) is defined by j(i) = if i = n-k then k-1 else if i = k-1 then n-k else i. In words, r is exactly the list obtained from head by swapping the value at 0-based position k-1 with the value at 0-based position n-k, leaving every other value and the list length unchanged.
  Preconditions: head is a finite singly linked list with n >= 1 nodes and values v_0, v_1, ..., v_{n-1} in order from the head (0-indexed). k is an integer with 1 <= k <= n. Every v_i satisfies 0 <= v_i <= 100. -/
theorem spec_1
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hbounds : ∀ i, i < v.length → 0 ≤ (nth v i).val ∧ (nth v i).val ≤ 100) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      (vals r).length = v.length ∧
        ∀ i, i < v.length → nth (vals r) i = nth v (swapIndex v.length k i) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hbounds : ∀ i, i < v.length → 0 ≤ (nth v i).val ∧ (nth v i).val ≤ 100), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      (vals r).length = v.length ∧
        ∀ i, i < v.length → nth (vals r) i = nth v (swapIndex v.length k i)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no failed Result, overflow, out-of-bounds access, or panic).
  Preconditions: head is a finite singly linked list with n nodes and values v_0, v_1, ..., v_{n-1} in order from the head (0-indexed), where 1 <= n <= 100000. k is an integer with 1 <= k <= n. Every v_i satisfies 0 <= v_i <= 100. -/
theorem spec_2
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn_lower : 1 ≤ v.length)
    (hn_upper : v.length ≤ 100000)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hbounds : ∀ i, i < v.length → 0 ≤ (nth v i).val ∧ (nth v i).val ≤ 100) :
    ∃ r, Aegis.SwapNodes.swap_nodes head k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn_lower : 1 ≤ v.length)
    (hn_upper : v.length ≤ 100000)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hbounds : ∀ i, i < v.length → 0 ≤ (nth v i).val ∧ (nth v i).val ≤ 100), ∃ r, Aegis.SwapNodes.swap_nodes head k = ok r) := by
  sorry

/-- Whenever the function returns a result r, the number of nodes of r is exactly n, the number of nodes of head.
  Preconditions: head is a finite singly linked list with n >= 1 nodes. k is an integer with 1 <= k <= n. -/
theorem spec_3
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r → (vals r).length = v.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r → (vals r).length = v.length) := by
  sorry

/-- Whenever the function returns a result r, r has n nodes and its values u_0, ..., u_{n-1} satisfy u_i = v_i for every i with 0 <= i < n. That is, r equals head.
  Preconditions: head is a finite singly linked list with n >= 1 nodes and values v_0, ..., v_{n-1}. k is an integer with 1 <= k <= n, and k-1 = n-k (equivalently 2*k = n+1). -/
theorem spec_4
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hsym : k.val - 1 = (v.length : ℤ) - k.val) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      (vals r).length = v.length ∧
        ∀ i, i < v.length → nth (vals r) i = nth v i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hsym : k.val - 1 = (v.length : ℤ) - k.val), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      (vals r).length = v.length ∧
        ∀ i, i < v.length → nth (vals r) i = nth v i) := by
  sorry

/-- Whenever the function returns a result r with values u_0, ..., u_{n-1}, for every i with 0 <= i < n such that i != k-1 and i != n-k, we have u_i = v_i.
  Preconditions: head is a finite singly linked list with n >= 1 nodes and values v_0, ..., v_{n-1}. k is an integer with 1 <= k <= n. -/
theorem spec_5
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      ∀ i, i < v.length → i ≠ k.toNat - 1 → i ≠ v.length - k.toNat →
        nth (vals r) i = nth v i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      ∀ i, i < v.length → i ≠ k.toNat - 1 → i ≠ v.length - k.toNat →
        nth (vals r) i = nth v i) := by
  sorry

/-- Whenever the function returns a result r with values u_0, ..., u_{n-1}, the value at position k-1 is the original kth-from-end value: u_{k-1} = v_{n-k}.
  Preconditions: head is a finite singly linked list with n >= 1 nodes and values v_0, ..., v_{n-1}. k is an integer with 1 <= k <= n. -/
theorem spec_6
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      nth (vals r) (k.toNat - 1) = nth v (v.length - k.toNat) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      nth (vals r) (k.toNat - 1) = nth v (v.length - k.toNat)) := by
  sorry

/-- Whenever the function returns a result r with values u_0, ..., u_{n-1}, the value at position n-k is the original kth-from-beginning value: u_{n-k} = v_{k-1}.
  Preconditions: head is a finite singly linked list with n >= 1 nodes and values v_0, ..., v_{n-1}. k is an integer with 1 <= k <= n. -/
theorem spec_7
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      nth (vals r) (v.length - k.toNat) = nth v (k.toNat - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      nth (vals r) (v.length - k.toNat) = nth v (k.toNat - 1)) := by
  sorry

/-- Whenever the function returns a result r, for every integer x, the number of nodes of r whose value is x equals the number of nodes of head whose value is x. Thus r is a permutation of the values of head.
  Preconditions: head is a finite singly linked list with n >= 1 nodes and values v_0, ..., v_{n-1}. k is an integer with 1 <= k <= n. -/
theorem spec_8
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      ∀ x : Std.I64, countVal x (vals r) = countVal x v := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      ∀ x : Std.I64, countVal x (vals r) = countVal x v) := by
  sorry

/-- Whenever the function returns a result r with values u_0, ..., u_{n-1}, we have u_0 = v_{n-1}, u_{n-1} = v_0, and u_i = v_i for every i with 0 < i < n-1.
  Preconditions: head is a finite singly linked list with n >= 1 nodes and values v_0, ..., v_{n-1}. k is an integer with 1 <= k <= n, and either k = 1 or k = n. -/
theorem spec_9
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hedge : k.toNat = 1 ∨ k.toNat = v.length) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      nth (vals r) 0 = nth v (v.length - 1) ∧
        nth (vals r) (v.length - 1) = nth v 0 ∧
          ∀ i, 0 < i → i < v.length - 1 → nth (vals r) i = nth v i := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hedge : k.toNat = 1 ∨ k.toNat = v.length), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      nth (vals r) 0 = nth v (v.length - 1) ∧
        nth (vals r) (v.length - 1) = nth v 0 ∧
          ∀ i, 0 < i → i < v.length - 1 → nth (vals r) i = nth v i) := by
  sorry

/-- Whenever the function returns a result r with values u_0, ..., u_{n-1}, we have u_i = v_i for every i with 0 <= i < n. That is, r equals head.
  Preconditions: head is a finite singly linked list with n >= 1 nodes and values v_0, ..., v_{n-1}. k is an integer with 1 <= k <= n. The two selected values are equal: v_{k-1} = v_{n-k}. -/
theorem spec_10
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hsame : nth v (k.toNat - 1) = nth v (v.length - k.toNat)) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      ∀ i, i < v.length → nth (vals r) i = nth v i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hsame : nth v (k.toNat - 1) = nth v (v.length - k.toNat)), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      ∀ i, i < v.length → nth (vals r) i = nth v i) := by
  sorry

/-- Whenever the function returns a result r with values u_0, ..., u_{n-1}, for every i with 0 <= i < n, u_i != v_i if and only if i = k-1 or i = n-k.
  Preconditions: head is a finite singly linked list with n >= 1 nodes and values v_0, ..., v_{n-1}. k is an integer with 1 <= k <= n. The two selected positions are distinct: k-1 != n-k. The two selected original values are distinct: v_{k-1} != v_{n-k}. -/
theorem spec_11
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hpos : k.toNat - 1 ≠ v.length - k.toNat)
    (hdistinct : nth v (k.toNat - 1) ≠ nth v (v.length - k.toNat)) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      ∀ i, i < v.length →
        (nth (vals r) i ≠ nth v i ↔ i = k.toNat - 1 ∨ i = v.length - k.toNat) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hpos : k.toNat - 1 ≠ v.length - k.toNat)
    (hdistinct : nth v (k.toNat - 1) ≠ nth v (v.length - k.toNat)), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      ∀ i, i < v.length →
        (nth (vals r) i ≠ nth v i ↔ i = k.toNat - 1 ∨ i = v.length - k.toNat)) := by
  sorry

/-- Whenever the function returns a result r, every node value of r is an integer in the interval [0, 100].
  Preconditions: head is a finite singly linked list with n >= 1 nodes. k is an integer with 1 <= k <= n. Every node value of head is between 0 and 100 inclusive. -/
theorem spec_12
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hbounds : ∀ i, i < v.length → 0 ≤ (nth v i).val ∧ (nth v i).val ≤ 100) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      ∀ i, i < (vals r).length → 0 ≤ (nth (vals r) i).val ∧ (nth (vals r) i).val ≤ 100 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ))
    (hbounds : ∀ i, i < v.length → 0 ≤ (nth v i).val ∧ (nth v i).val ≤ 100), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      ∀ i, i < (vals r).length → 0 ≤ (nth (vals r) i).val ∧ (nth (vals r) i).val ≤ 100) := by
  sorry

/-- Whenever the function returns a result r with values u_0, ..., u_{n-1}, the head value u_0 satisfies: u_0 = v_{n-1} if k = 1 or k = n, and u_0 = v_0 otherwise (that is, if 1 < k < n).
  Preconditions: head is a finite singly linked list with n >= 1 nodes and values v_0, ..., v_{n-1}. k is an integer with 1 <= k <= n. -/
theorem spec_13
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      nth (vals r) 0 =
        (if k.toNat = 1 ∨ k.toNat = v.length then nth v (v.length - 1) else nth v 0) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      nth (vals r) 0 =
        (if k.toNat = 1 ∨ k.toNat = v.length then nth v (v.length - 1) else nth v 0)) := by
  sorry

/-- Whenever the function returns a result r with values u_0, ..., u_{n-1}, the last value u_{n-1} satisfies: u_{n-1} = v_0 if k = 1 or k = n, and u_{n-1} = v_{n-1} otherwise (that is, if 1 < k < n).
  Preconditions: head is a finite singly linked list with n >= 1 nodes and values v_0, ..., v_{n-1}. k is an integer with 1 <= k <= n. -/
theorem spec_14
    (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)) :
    ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      nth (vals r) (v.length - 1) =
        (if k.toNat = 1 ∨ k.toNat = v.length then nth v 0 else nth v (v.length - 1)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (head : Aegis.SwapNodes.List) (k : Std.I64) (v : List Std.I64)
    (hvals : vals head = v)
    (hn : 1 ≤ v.length)
    (hk_lower : 1 ≤ k.val)
    (hk_upper : k.val ≤ (v.length : ℤ)), ∀ r, Aegis.SwapNodes.swap_nodes head k = ok r →
      nth (vals r) (v.length - 1) =
        (if k.toNat = 1 ∨ k.toNat = v.length then nth v 0 else nth v (v.length - 1))) := by
  sorry

end AegisSpec.SwapNodes
