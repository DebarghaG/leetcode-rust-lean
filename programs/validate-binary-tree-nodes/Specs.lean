import Aegis.ValidateBinaryTreeNodes.Code.Funs

/-!
# Specifications of `Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes`

LeetCode problem `validate-binary-tree-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ValidateBinaryTreeNodes

def size (n : Std.I64) : ℕ := n.val.toNat

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def slot (s : Slice Std.I64) (i : ℕ) : ℤ := (s.val.getD i default).val

def P (n : ℕ) (leftChild rightChild : Slice Std.I64) (c : ℤ) : ℕ :=
  ((List.range n).filter (fun i => slot leftChild i = c)).length +
    ((List.range n).filter (fun i => slot rightChild i = c)).length

def nonnegSlots (n : ℕ) (s : Slice Std.I64) : ℕ :=
  ((List.range n).filter (fun i => slot s i ≠ -1)).length

def Edge (leftChild rightChild : Slice Std.I64) (u w : ℕ) : Prop :=
  (vals leftChild)[u]? = some (w : ℤ) ∨ (vals rightChild)[u]? = some (w : ℤ)

inductive Reach (leftChild rightChild : Slice Std.I64) : ℕ → ℕ → Prop where
  | refl (u : ℕ) : Reach leftChild rightChild u u
  | step {u v w : ℕ} :
      Reach leftChild rightChild u v →
        Edge leftChild rightChild v w → Reach leftChild rightChild u w

def HasCycle (leftChild rightChild : Slice Std.I64) (n : ℕ) : Prop :=
  ∃ (k : ℕ) (hk : 1 ≤ k), ∃ v : Fin k → ℕ,
    (∀ j : Fin k, v j < n) ∧
      (∀ j : Fin k,
        Edge leftChild rightChild (v j) (v ⟨(j.val + 1) % k, Nat.mod_lt _ (by omega)⟩))

/-- Define P(c) for 0 <= c < n by P(c) = (number of i in [0,n) with leftChild[i] = c) + (number of i in [0,n) with rightChild[i] = c); each of the two child slots is counted separately. Say v is reachable from r if there exist k >= 0 and nodes v_0,...,v_k in [0,n) with v_0 = r, v_k = v, and for every j < k, leftChild[v_j] = v_{j+1} or rightChild[v_j] = v_{j+1}. The function returns Result.ok b for some Bool b, and b = true if and only if there exists a node root with 0 <= root < n such that: (1) P(root) = 0; (2) P(v) = 1 for every v with 0 <= v < n and v != root; (3) every v with 0 <= v < n is reachable from root. Equivalently, b = false exactly when no such root exists.
  Preconditions: n = len(leftChild), n = len(rightChild), 1 <= n <= 10000, and for every i with 0 <= i < n, -1 <= leftChild[i] < n and -1 <= rightChild[i] < n. -/
theorem spec_1 (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val) :
    ∃ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b ∧
        (b = true ↔
          ∃ root : ℕ, root < size n ∧
            P (size n) leftChild rightChild (root : ℤ) = 0 ∧
            (∀ v : ℕ, v < size n → v ≠ root →
              P (size n) leftChild rightChild (v : ℤ) = 1) ∧
            (∀ v : ℕ, v < size n → Reach leftChild rightChild root v)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val), ∃ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b ∧
        (b = true ↔
          ∃ root : ℕ, root < size n ∧
            P (size n) leftChild rightChild (root : ℤ) = 0 ∧
            (∀ v : ℕ, v < size n → v ≠ root →
              P (size n) leftChild rightChild (v : ℤ) = 1) ∧
            (∀ v : ℕ, v < size n → Reach leftChild rightChild root v))) := by
  sorry

/-- The function returns Result.ok b for some Bool b; in particular it does not fail (no panic, arithmetic overflow, or out-of-bounds access) on any input satisfying the preconditions.
  Preconditions: n = len(leftChild), n = len(rightChild), 1 <= n <= 10000, and for every i with 0 <= i < n, -1 <= leftChild[i] < n and -1 <= rightChild[i] < n. -/
theorem spec_2 (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val) :
    ∃ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val), ∃ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b) := by
  sorry

/-- Whenever the function returns Result.ok b with b = true, the total number of non-negative child slots is exactly n-1: (sum over 0 <= i < n of 1 if leftChild[i] != -1 else 0) + (sum over 0 <= i < n of 1 if rightChild[i] != -1 else 0) = n-1.
  Preconditions: n = len(leftChild), n = len(rightChild), 1 <= n <= 10000, and for every i with 0 <= i < n, -1 <= leftChild[i] < n and -1 <= rightChild[i] < n. -/
theorem spec_3 (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val) :
    ∀ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b →
        b = true →
          (nonnegSlots (size n) leftChild : ℤ) + (nonnegSlots (size n) rightChild : ℤ) =
            n.val - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val), ∀ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b →
        b = true →
          (nonnegSlots (size n) leftChild : ℤ) + (nonnegSlots (size n) rightChild : ℤ) =
            n.val - 1) := by
  sorry

/-- Define P(c) as P(c) = (number of i in [0,n) with leftChild[i] = c) + (number of i in [0,n) with rightChild[i] = c). Whenever the function returns Result.ok b with b = true, there is exactly one node c with 0 <= c < n such that P(c) = 0; for every other node d with 0 <= d < n and d != c, P(d) >= 1.
  Preconditions: n = len(leftChild), n = len(rightChild), 1 <= n <= 10000, and for every i with 0 <= i < n, -1 <= leftChild[i] < n and -1 <= rightChild[i] < n. -/
theorem spec_4 (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val) :
    ∀ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b →
        b = true →
          ∃ c : ℕ, c < size n ∧ P (size n) leftChild rightChild (c : ℤ) = 0 ∧
            (∀ d : ℕ, d < size n → d ≠ c →
              1 ≤ P (size n) leftChild rightChild (d : ℤ)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val), ∀ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b →
        b = true →
          ∃ c : ℕ, c < size n ∧ P (size n) leftChild rightChild (c : ℤ) = 0 ∧
            (∀ d : ℕ, d < size n → d ≠ c →
              1 ≤ P (size n) leftChild rightChild (d : ℤ))) := by
  sorry

/-- Define P(c) as P(c) = (number of i in [0,n) with leftChild[i] = c) + (number of i in [0,n) with rightChild[i] = c). Whenever the function returns Result.ok b with b = true, P(c) <= 1 for every c with 0 <= c < n.
  Preconditions: n = len(leftChild), n = len(rightChild), 1 <= n <= 10000, and for every i with 0 <= i < n, -1 <= leftChild[i] < n and -1 <= rightChild[i] < n. -/
theorem spec_5 (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val) :
    ∀ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b →
        b = true →
          ∀ c : ℕ, c < size n → P (size n) leftChild rightChild (c : ℤ) ≤ 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val), ∀ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b →
        b = true →
          ∀ c : ℕ, c < size n → P (size n) leftChild rightChild (c : ℤ) ≤ 1) := by
  sorry

/-- Whenever the function returns Result.ok b with b = true, the directed graph whose edges are i -> c for every i in [0,n) and every non-negative slot c in {leftChild[i], rightChild[i]} has no directed cycle of positive length: there do not exist k >= 1 and nodes v_0,...,v_{k-1} in [0,n) such that, with indices taken modulo k, for each j, leftChild[v_j] = v_{j+1} or rightChild[v_j] = v_{j+1}.
  Preconditions: n = len(leftChild), n = len(rightChild), 1 <= n <= 10000, and for every i with 0 <= i < n, -1 <= leftChild[i] < n and -1 <= rightChild[i] < n. -/
theorem spec_6 (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val) :
    ∀ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b →
        b = true → ¬ HasCycle leftChild rightChild (size n) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val), ∀ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b →
        b = true → ¬ HasCycle leftChild rightChild (size n)) := by
  sorry

/-- Whenever the function returns Result.ok b with b = true, there exists a node root with 0 <= root < n such that every node v with 0 <= v < n is reachable from root by following zero or more child edges, where an edge u -> w exists exactly when leftChild[u] = w or rightChild[u] = w with w != -1.
  Preconditions: n = len(leftChild), n = len(rightChild), 1 <= n <= 10000, and for every i with 0 <= i < n, -1 <= leftChild[i] < n and -1 <= rightChild[i] < n. -/
theorem spec_7 (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val) :
    ∀ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b →
        b = true →
          ∃ root : ℕ, root < size n ∧
            ∀ v : ℕ, v < size n → Reach leftChild rightChild root v := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val), ∀ b : Bool,
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild = ok b →
        b = true →
          ∃ root : ℕ, root < size n ∧
            ∀ v : ℕ, v < size n → Reach leftChild rightChild root v) := by
  sorry

/-- Define P(c) as P(c) = (number of i in [0,n) with leftChild[i] = c) + (number of i in [0,n) with rightChild[i] = c). If there exists a node root with 0 <= root < n such that P(root) = 0 and P(v) = 1 for every v with 0 <= v < n and v != root, but some node w with 0 <= w < n is not reachable from root by following child edges, then the function returns Result.ok false.
  Preconditions: n = len(leftChild), n = len(rightChild), 1 <= n <= 10000, and for every i with 0 <= i < n, -1 <= leftChild[i] < n and -1 <= rightChild[i] < n. -/
theorem spec_8 (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val) :
    (∃ root : ℕ, root < size n ∧
        P (size n) leftChild rightChild (root : ℤ) = 0 ∧
        (∀ v : ℕ, v < size n → v ≠ root →
          P (size n) leftChild rightChild (v : ℤ) = 1) ∧
        (∃ w : ℕ, w < size n ∧ ¬ Reach leftChild rightChild root w)) →
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild =
        ok false := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (leftChild rightChild : Slice Std.I64)
    (h_len_left : size n = leftChild.length)
    (h_len_right : size n = rightChild.length)
    (h_n_range : 1 ≤ n.val ∧ n.val ≤ 10000)
    (h_slots : ∀ i : ℕ, i < size n →
      -1 ≤ slot leftChild i ∧ slot leftChild i < n.val ∧
        -1 ≤ slot rightChild i ∧ slot rightChild i < n.val), (∃ root : ℕ, root < size n ∧
        P (size n) leftChild rightChild (root : ℤ) = 0 ∧
        (∀ v : ℕ, v < size n → v ≠ root →
          P (size n) leftChild rightChild (v : ℤ) = 1) ∧
        (∃ w : ℕ, w < size n ∧ ¬ Reach leftChild rightChild root w)) →
      Aegis.ValidateBinaryTreeNodes.validate_binary_tree_nodes n leftChild rightChild =
        ok false) := by
  sorry

end AegisSpec.ValidateBinaryTreeNodes
