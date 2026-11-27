import Aegis.DeleteTreeNodes.Code.Funs

/-!
# Specifications of `Aegis.DeleteTreeNodes.delete_tree_nodes`

LeetCode problem `delete-tree-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Classical

  noncomputable section

  open Aegis.DeleteTreeNodes

  namespace AegisSpec.DeleteTreeNodes

  def valAt (value : Slice Std.I64) (i : ℕ) : ℤ := (value.val.getD i 0#i64).val

  def parIdx (parent : Slice Std.I64) (i : ℕ) : ℕ := (valAt parent i).toNat

  def IsAncestor (parent : Slice Std.I64) (a u : ℕ) : Prop :=
    ∃ k : ℕ, (parIdx parent)^[k] u = a

  def subtreeNodes (nodes : ℕ) (parent : Slice Std.I64) (v : ℕ) : Finset ℕ :=
    (Finset.range nodes).filter (fun u => IsAncestor parent v u)

  def SubtreeSum (nodes : ℕ) (parent value : Slice Std.I64) (v : ℕ) : ℤ :=
    ∑ u ∈ subtreeNodes nodes parent v, valAt value u

  def SubtreeSize (nodes : ℕ) (parent : Slice Std.I64) (v : ℕ) : ℕ :=
    (subtreeNodes nodes parent v).card

  def zeroSumNodes (nodes : ℕ) (parent value : Slice Std.I64) : Finset ℕ :=
    (Finset.range nodes).filter (fun v => SubtreeSum nodes parent value v = 0)

  def IsRemoved (nodes : ℕ) (parent value : Slice Std.I64) (u : ℕ) : Prop :=
    ∃ a : ℕ, IsAncestor parent a u ∧ SubtreeSum nodes parent value a = 0

  def IsKept (nodes : ℕ) (parent value : Slice Std.I64) (u : ℕ) : Prop :=
    ∀ a : ℕ, IsAncestor parent a u → SubtreeSum nodes parent value a ≠ 0

  def keptNodes (nodes : ℕ) (parent value : Slice Std.I64) : Finset ℕ :=
    (Finset.range nodes).filter (fun u => IsKept nodes parent value u)

  def TotalSum (nodes : ℕ) (value : Slice Std.I64) : ℤ :=
    ∑ u ∈ Finset.range nodes, valAt value u

  def nonzeroValueCount (nodes : ℕ) (value : Slice Std.I64) : ℕ :=
    ((Finset.Ico 1 nodes).filter (fun i => valAt value i ≠ 0)).card

  def nonzeroRootChildCount (nodes : ℕ) (parent value : Slice Std.I64) : ℕ :=
    ((Finset.Ico 1 nodes).filter
      (fun c => (valAt parent c = 0) ∧ SubtreeSum nodes parent value c ≠ 0)).card

  /-- For a node v, let SubtreeSum(v) be the sum of value[u] over all nodes u in the subtree rooted at v, including v itself. A node u is removed exactly when some ancestor a of u, possibly a = u, satisfies SubtreeSum(a) = 0. The function returns a result r and r equals the number of nodes u with 0 <= u < nodes such that every ancestor a of u, including u, satisfies SubtreeSum(a) != 0.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_1
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000) :
      ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
        r.val = ((keptNodes nodes.val.toNat parent value).card : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000), ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
          r.val = ((keptNodes nodes.val.toNat parent value).card : ℤ)) := by
    sorry

  /-- The function returns a result r without failing, panicking, or overflowing.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_2
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000) :
      ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000), ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= nodes.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_3
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000) :
      ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
        0 ≤ r.val ∧ r.val ≤ nodes.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000), ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
          0 ≤ r.val ∧ r.val ≤ nodes.val) := by
    sorry

  /-- For a node v, let SubtreeSum(v) be the sum of value[u] over all nodes u in the subtree rooted at v, including v itself. If SubtreeSum(0) = 0, then the function returns r = 0.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_4
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
      (hzero : SubtreeSum nodes.val.toNat parent value 0 = 0) :
      ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
        (hzero : SubtreeSum nodes.val.toNat parent value 0 = 0), ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 0) := by
    sorry

  /-- For a node v, let SubtreeSum(v) be the sum of value[u] over all nodes u in the subtree rooted at v, including v itself. If SubtreeSum(0) != 0, then the function returns a result r with r >= 1.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_5
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
      (hnz : SubtreeSum nodes.val.toNat parent value 0 ≠ 0) :
      ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
        (hnz : SubtreeSum nodes.val.toNat parent value 0 ≠ 0), ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- For a node v, let SubtreeSum(v) be the sum of value[u] over all nodes u in the subtree rooted at v, including v itself. If for every v with 0 <= v < nodes, SubtreeSum(v) != 0, then the function returns r = nodes.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_6
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
      (hnone : ∀ v : ℕ, v < nodes.val.toNat →
        SubtreeSum nodes.val.toNat parent value v ≠ 0) :
      ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = nodes.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
        (hnone : ∀ v : ℕ, v < nodes.val.toNat →
          SubtreeSum nodes.val.toNat parent value v ≠ 0), ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = nodes.val) := by
    sorry

  /-- For a node v, let SubtreeSum(v) be the sum of value[u] over all nodes u in the subtree rooted at v, including v itself, and let SubtreeSize(v) be the number of nodes in that subtree. For every v with 0 <= v < nodes, if SubtreeSum(v) = 0, then the function returns a result r with r <= nodes - SubtreeSize(v).
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_7
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000) :
      ∀ v : ℕ, v < nodes.val.toNat → SubtreeSum nodes.val.toNat parent value v = 0 →
        ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
          r.val ≤ nodes.val - ((SubtreeSize nodes.val.toNat parent v : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000), ∀ v : ℕ, v < nodes.val.toNat → SubtreeSum nodes.val.toNat parent value v = 0 →
          ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
            r.val ≤ nodes.val - ((SubtreeSize nodes.val.toNat parent v : ℕ) : ℤ)) := by
    sorry

  /-- For a node v, let SubtreeSum(v) be the sum of value[u] over all nodes u in the subtree rooted at v, including v itself, and let SubtreeSize(v) be the number of nodes in that subtree. If there is exactly one node v with 0 <= v < nodes such that SubtreeSum(v) = 0, then for that v the function returns r = nodes - SubtreeSize(v).
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_8
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
      (hunique : ∃ v : ℕ, v < nodes.val.toNat ∧
        SubtreeSum nodes.val.toNat parent value v = 0 ∧
        ∀ w : ℕ, w < nodes.val.toNat → SubtreeSum nodes.val.toNat parent value w = 0 → w = v) :
      ∀ v : ℕ, v < nodes.val.toNat → SubtreeSum nodes.val.toNat parent value v = 0 →
        ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
          r.val = nodes.val - ((SubtreeSize nodes.val.toNat parent v : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
        (hunique : ∃ v : ℕ, v < nodes.val.toNat ∧
          SubtreeSum nodes.val.toNat parent value v = 0 ∧
          ∀ w : ℕ, w < nodes.val.toNat → SubtreeSum nodes.val.toNat parent value w = 0 → w = v), ∀ v : ℕ, v < nodes.val.toNat → SubtreeSum nodes.val.toNat parent value v = 0 →
          ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
            r.val = nodes.val - ((SubtreeSize nodes.val.toNat parent v : ℕ) : ℤ)) := by
    sorry

  /-- If nodes = 1, then the function returns r = 0 when value[0] = 0, and returns r = 1 when value[0] != 0.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_9
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
      (hsize : nodes.val = 1) :
      (valAt value 0 = 0 →
          ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 0) ∧
        (valAt value 0 ≠ 0 →
          ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
        (hsize : nodes.val = 1), (valAt value 0 = 0 →
            ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 0) ∧
          (valAt value 0 ≠ 0 →
            ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 1)) := by
    sorry

  /-- If nodes = 2, write a = value[0] and b = value[1]. Then the function returns r = 0 if a + b = 0; it returns r = 1 if a + b != 0 and b = 0; and it returns r = 2 if a + b != 0 and b != 0.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_10
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
      (hsize : nodes.val = 2) :
      (valAt value 0 + valAt value 1 = 0 →
          ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 0) ∧
        (valAt value 0 + valAt value 1 ≠ 0 → valAt value 1 = 0 →
          ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 1) ∧
        (valAt value 0 + valAt value 1 ≠ 0 → valAt value 1 ≠ 0 →
          ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 2) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
        (hsize : nodes.val = 2), (valAt value 0 + valAt value 1 = 0 →
            ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 0) ∧
          (valAt value 0 + valAt value 1 ≠ 0 → valAt value 1 = 0 →
            ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 1) ∧
          (valAt value 0 + valAt value 1 ≠ 0 → valAt value 1 ≠ 0 →
            ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 2)) := by
    sorry

  /-- Assume the tree is a star rooted at 0, so every node i > 0 is a child of the root. Let S = value[0] + value[1] + ... + value[nodes-1]. The function returns r = 0 if S = 0; if S != 0, it returns r = 1 + the number of indices i with 1 <= i < nodes and value[i] != 0.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5; additionally, for every i with 1 <= i < nodes, parent[i] = 0. -/
  theorem spec_11
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
      (hstar : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat → (parent.val.getD i 0#i64).val = 0) :
      (TotalSum nodes.val.toNat value = 0 →
          ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 0) ∧
        (TotalSum nodes.val.toNat value ≠ 0 →
          ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
            r.val = 1 + ((nonzeroValueCount nodes.val.toNat value : ℕ) : ℤ)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
        (hstar : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat → (parent.val.getD i 0#i64).val = 0), (TotalSum nodes.val.toNat value = 0 →
            ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧ r.val = 0) ∧
          (TotalSum nodes.val.toNat value ≠ 0 →
            ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
              r.val = 1 + ((nonzeroValueCount nodes.val.toNat value : ℕ) : ℤ))) := by
    sorry

  /-- Let value' be the array defined by value'[i] = c * value[i] for every i with 0 <= i < nodes. The function returns a result r on input (nodes, parent, value) and a result r' on input (nodes, parent, value'), and r = r'.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5; additionally, c is a nonzero integer such that -10^5 <= c * value[i] <= 10^5 for every i with 0 <= i < nodes. -/
  theorem spec_12
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
      (c : ℤ) (hc : c ≠ 0)
      (hc_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ c * (value.val.getD i 0#i64).val ∧
          c * (value.val.getD i 0#i64).val ≤ 100000)
      (value' : Slice Std.I64)
      (hvalue'_len : value'.val.length = value.val.length)
      (hvalue' : ∀ i : ℕ, i < value.val.length →
        (value'.val.getD i 0#i64).val = c * (value.val.getD i 0#i64).val) :
      ∃ r r' : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
        delete_tree_nodes nodes parent value' = ok r' ∧ r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
        (c : ℤ) (hc : c ≠ 0)
        (hc_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ c * (value.val.getD i 0#i64).val ∧
            c * (value.val.getD i 0#i64).val ≤ 100000)
        (value' : Slice Std.I64)
        (hvalue'_len : value'.val.length = value.val.length)
        (hvalue' : ∀ i : ℕ, i < value.val.length →
          (value'.val.getD i 0#i64).val = c * (value.val.getD i 0#i64).val), ∃ r r' : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
          delete_tree_nodes nodes parent value' = ok r' ∧ r = r') := by
    sorry

  /-- For a node v, let SubtreeSum(v) be the sum of value[u] over all nodes u in the subtree rooted at v, including v itself. Let Z be the number of indices v with 0 <= v < nodes and SubtreeSum(v) = 0. The function returns a result r with r <= nodes - Z.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_13
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000) :
      ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
        r.val ≤ nodes.val - ((zeroSumNodes nodes.val.toNat parent value).card : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000), ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
          r.val ≤ nodes.val - ((zeroSumNodes nodes.val.toNat parent value).card : ℤ)) := by
    sorry

  /-- For a node v, let SubtreeSum(v) be the sum of value[u] over all nodes u in the subtree rooted at v, including v itself. If SubtreeSum(0) != 0, let C be the number of indices c with 1 <= c < nodes, parent[c] = 0, and SubtreeSum(c) != 0. Then the function returns a result r with r >= 1 + C.
    Preconditions: nodes is an integer with 1 <= nodes <= 10^4; len(parent) = nodes and len(value) = nodes; parent[0] = -1; for every i with 1 <= i < nodes, 0 <= parent[i] < nodes; the parent relation is a valid rooted tree, meaning repeated application of parent from any node eventually reaches 0 and no cycle occurs; for every i with 0 <= i < nodes, -10^5 <= value[i] <= 10^5. -/
  theorem spec_14
      (nodes : Std.I64) (parent value : Slice Std.I64)
      (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
      (hparent_len : parent.val.length = nodes.val.toNat)
      (hvalue_len : value.val.length = nodes.val.toNat)
      (hroot : (parent.val.getD 0 0#i64).val = -1)
      (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
        0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
      (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
      (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
        -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
      (hnz : SubtreeSum nodes.val.toNat parent value 0 ≠ 0) :
      ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
        1 + ((nonzeroRootChildCount nodes.val.toNat parent value : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nodes : Std.I64) (parent value : Slice Std.I64)
        (hnodes_lo : 1 ≤ nodes.val) (hnodes_hi : nodes.val ≤ 10000)
        (hparent_len : parent.val.length = nodes.val.toNat)
        (hvalue_len : value.val.length = nodes.val.toNat)
        (hroot : (parent.val.getD 0 0#i64).val = -1)
        (hparent_range : ∀ i : ℕ, 1 ≤ i → i < nodes.val.toNat →
          0 ≤ (parent.val.getD i 0#i64).val ∧ (parent.val.getD i 0#i64).val < nodes.val)
        (htree : ∀ u : ℕ, u < nodes.val.toNat → ∃ k : ℕ, (parIdx parent)^[k] u = 0)
        (hvalue_range : ∀ i : ℕ, i < nodes.val.toNat →
          -100000 ≤ (value.val.getD i 0#i64).val ∧ (value.val.getD i 0#i64).val ≤ 100000)
        (hnz : SubtreeSum nodes.val.toNat parent value 0 ≠ 0), ∃ r : Std.I64, delete_tree_nodes nodes parent value = ok r ∧
          1 + ((nonzeroRootChildCount nodes.val.toNat parent value : ℕ) : ℤ) ≤ r.val) := by
    sorry

  end AegisSpec.DeleteTreeNodes
