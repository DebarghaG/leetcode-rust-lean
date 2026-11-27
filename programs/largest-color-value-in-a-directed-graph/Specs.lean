import Aegis.LargestPathValue.Code.Funs

/-!
# Specifications of `Aegis.LargestPathValue.largest_path_value`

LeetCode problem `largest-color-value-in-a-directed-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LargestPathValue

  def colorAt (colors : Slice Std.U8) (x : Nat) : Nat :=
    (colors.val.getD x (0#u8)).val

  def IsLetterCode (c : Nat) : Prop := 97 ≤ c ∧ c ≤ 122

  def ColorsAreLetters (colors : Slice Std.U8) : Prop :=
    ∀ i : Nat, i < colors.val.length → IsLetterCode (colorAt colors i)

  def EdgesWellFormed (n : Nat) (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ v : alloc.vec.Vec Std.I64, v ∈ edges.val →
      ∃ a b : Int,
        v.val.map (fun x => x.val) = [a, b] ∧
          0 ≤ a ∧ a < (n : Int) ∧ 0 ≤ b ∧ b < (n : Int)

  def HasEdge (edges : Slice (alloc.vec.Vec Std.I64)) (a b : Nat) : Prop :=
    ∃ v : alloc.vec.Vec Std.I64,
      v ∈ edges.val ∧ v.val.map (fun x => x.val) = [(a : Int), (b : Int)]

  def HasDirectedCycle (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∃ vs : List Nat,
      1 ≤ vs.length ∧
        ∀ i : Nat,
          i < vs.length →
            HasEdge edges (vs.getD i 0) (vs.getD ((i + 1) % vs.length) 0)

  def Acyclic (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ¬ HasDirectedCycle edges

  def IsValidPath (n : Nat) (edges : Slice (alloc.vec.Vec Std.I64))
      (P : List Nat) : Prop :=
    1 ≤ P.length ∧
      (∀ x : Nat, x ∈ P → x < n) ∧
        ∀ i : Nat, i + 1 < P.length → HasEdge edges (P.getD i 0) (P.getD (i + 1) 0)

  def countColor (colors : Slice Std.U8) (P : List Nat) (c : Nat) : Nat :=
    P.countP (fun x => decide (colorAt colors x = c))

  def pathValue (colors : Slice Std.U8) (P : List Nat) : Nat :=
    (List.range 26).foldr (fun k acc => max (countColor colors P (97 + k)) acc) 0

  def IsMaxPathValue (colors : Slice Std.U8) (n : Nat)
      (edges : Slice (alloc.vec.Vec Std.I64)) (r : Int) : Prop :=
    (∀ P : List Nat, IsValidPath n edges P → (pathValue colors P : Int) ≤ r) ∧
      ∃ P : List Nat, IsValidPath n edges P ∧ (pathValue colors P : Int) = r

  def IsMaxPathLength (n : Nat) (edges : Slice (alloc.vec.Vec Std.I64))
      (L : Nat) : Prop :=
    (∃ P : List Nat, IsValidPath n edges P ∧ P.length = L) ∧
      ∀ P : List Nat, IsValidPath n edges P → P.length ≤ L

  def EdgesSameColor (colors : Slice Std.U8)
      (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ a b : Nat, HasEdge edges a b → colorAt colors a = colorAt colors b

  /-- Whenever largest_path_value returns a result r, r is characterized as follows. The directed graph has nodes 0,...,n-1 and an edge a -> b whenever some edges[j] = [a,b]. A directed cycle means a sequence v_0,...,v_{k-1} with k >= 1 such that for every i there is an edge from v_i to v_{(i+1) mod k}; a self-loop is the case k = 1. If the graph contains a directed cycle, then r = -1. Otherwise the graph is acyclic, and r = max { val(P) : P is a nonempty valid path }, where a nonempty valid path is a sequence P = (x_0,...,x_{L-1}) with L >= 1 such that for every i with 0 <= i < L-1 there is an edge from x_i to x_{i+1}, and val(P) is the maximum, over lowercase English letters c, of the number of indices i with 0 <= i < L and colors[x_i] = c.
    Preconditions: Let n = len(colors) and m = len(edges). Preconditions: 1 <= n <= 100000; every byte colors[i] for 0 <= i < n is the ASCII code of a lowercase English letter; 0 <= m <= 100000; for every j with 0 <= j < m, edges[j] is a vector of length 2, and if edges[j][0] = a and edges[j][1] = b then 0 <= a < n and 0 <= b < n. -/
  theorem spec_1
      (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
      (hm_max : edges.val.length ≤ 100000)
      (hcolors : ColorsAreLetters colors)
      (hedges : EdgesWellFormed colors.val.length edges) :
      ∀ r : Std.I64,
        Aegis.LargestPathValue.largest_path_value colors edges = ok r →
          (HasDirectedCycle edges → r.val = -1) ∧
            (Acyclic edges →
              IsMaxPathValue colors colors.val.length edges r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
        (hm_max : edges.val.length ≤ 100000)
        (hcolors : ColorsAreLetters colors)
        (hedges : EdgesWellFormed colors.val.length edges), ∀ r : Std.I64,
          Aegis.LargestPathValue.largest_path_value colors edges = ok r →
            (HasDirectedCycle edges → r.val = -1) ∧
              (Acyclic edges →
                IsMaxPathValue colors colors.val.length edges r.val)) := by
    sorry

  /-- For every input satisfying the preconditions, largest_path_value returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(colors) and m = len(edges). Preconditions: 1 <= n <= 100000; every byte colors[i] for 0 <= i < n is the ASCII code of a lowercase English letter; 0 <= m <= 100000; for every j with 0 <= j < m, edges[j] is a vector of length 2, and if edges[j][0] = a and edges[j][1] = b then 0 <= a < n and 0 <= b < n. -/
  theorem spec_2
      (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
      (hm_max : edges.val.length ≤ 100000)
      (hcolors : ColorsAreLetters colors)
      (hedges : EdgesWellFormed colors.val.length edges) :
      ∃ r : Std.I64, Aegis.LargestPathValue.largest_path_value colors edges = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
        (hm_max : edges.val.length ≤ 100000)
        (hcolors : ColorsAreLetters colors)
        (hedges : EdgesWellFormed colors.val.length edges), ∃ r : Std.I64, Aegis.LargestPathValue.largest_path_value colors edges = ok r) := by
    sorry

  /-- Whenever largest_path_value returns a result r, r = -1 if and only if the directed graph determined by edges contains a directed cycle, where a self-loop is counted as a cycle of length 1.
    Preconditions: Let n = len(colors) and m = len(edges). Preconditions: 1 <= n <= 100000; every byte colors[i] for 0 <= i < n is the ASCII code of a lowercase English letter; 0 <= m <= 100000; for every j with 0 <= j < m, edges[j] is a vector of length 2, and if edges[j][0] = a and edges[j][1] = b then 0 <= a < n and 0 <= b < n. -/
  theorem spec_3
      (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
      (hm_max : edges.val.length ≤ 100000)
      (hcolors : ColorsAreLetters colors)
      (hedges : EdgesWellFormed colors.val.length edges) :
      ∀ r : Std.I64,
        Aegis.LargestPathValue.largest_path_value colors edges = ok r →
          (r.val = -1 ↔ HasDirectedCycle edges) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
        (hm_max : edges.val.length ≤ 100000)
        (hcolors : ColorsAreLetters colors)
        (hedges : EdgesWellFormed colors.val.length edges), ∀ r : Std.I64,
          Aegis.LargestPathValue.largest_path_value colors edges = ok r →
            (r.val = -1 ↔ HasDirectedCycle edges)) := by
    sorry

  /-- Whenever largest_path_value returns a result r, -1 <= r <= n.
    Preconditions: Let n = len(colors) and m = len(edges). Preconditions: 1 <= n <= 100000; every byte colors[i] for 0 <= i < n is the ASCII code of a lowercase English letter; 0 <= m <= 100000; for every j with 0 <= j < m, edges[j] is a vector of length 2, and if edges[j][0] = a and edges[j][1] = b then 0 <= a < n and 0 <= b < n. -/
  theorem spec_4
      (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
      (hm_max : edges.val.length ≤ 100000)
      (hcolors : ColorsAreLetters colors)
      (hedges : EdgesWellFormed colors.val.length edges) :
      ∀ r : Std.I64,
        Aegis.LargestPathValue.largest_path_value colors edges = ok r →
          -1 ≤ r.val ∧ r.val ≤ (colors.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
        (hm_max : edges.val.length ≤ 100000)
        (hcolors : ColorsAreLetters colors)
        (hedges : EdgesWellFormed colors.val.length edges), ∀ r : Std.I64,
          Aegis.LargestPathValue.largest_path_value colors edges = ok r →
            -1 ≤ r.val ∧ r.val ≤ (colors.val.length : Int)) := by
    sorry

  /-- Whenever largest_path_value returns a result r, if the directed graph determined by edges contains no directed cycle, then r >= 1.
    Preconditions: Let n = len(colors) and m = len(edges). Preconditions: 1 <= n <= 100000; every byte colors[i] for 0 <= i < n is the ASCII code of a lowercase English letter; 0 <= m <= 100000; for every j with 0 <= j < m, edges[j] is a vector of length 2, and if edges[j][0] = a and edges[j][1] = b then 0 <= a < n and 0 <= b < n. -/
  theorem spec_5
      (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
      (hm_max : edges.val.length ≤ 100000)
      (hcolors : ColorsAreLetters colors)
      (hedges : EdgesWellFormed colors.val.length edges) :
      ∀ r : Std.I64,
        Aegis.LargestPathValue.largest_path_value colors edges = ok r →
          Acyclic edges → (1 : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
        (hm_max : edges.val.length ≤ 100000)
        (hcolors : ColorsAreLetters colors)
        (hedges : EdgesWellFormed colors.val.length edges), ∀ r : Std.I64,
          Aegis.LargestPathValue.largest_path_value colors edges = ok r →
            Acyclic edges → (1 : Int) ≤ r.val) := by
    sorry

  /-- Whenever largest_path_value returns a result r, if the directed graph determined by edges contains no directed cycle, then for every nonempty valid path P = (x_0,...,x_{L-1}) and every lowercase English letter c, the number of indices i with 0 <= i < L and colors[x_i] = c is at most r. Here a nonempty valid path means L >= 1 and for every i with 0 <= i < L-1 there is an edge from x_i to x_{i+1}.
    Preconditions: Let n = len(colors) and m = len(edges). Preconditions: 1 <= n <= 100000; every byte colors[i] for 0 <= i < n is the ASCII code of a lowercase English letter; 0 <= m <= 100000; for every j with 0 <= j < m, edges[j] is a vector of length 2, and if edges[j][0] = a and edges[j][1] = b then 0 <= a < n and 0 <= b < n. -/
  theorem spec_6
      (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
      (hm_max : edges.val.length ≤ 100000)
      (hcolors : ColorsAreLetters colors)
      (hedges : EdgesWellFormed colors.val.length edges) :
      ∀ r : Std.I64,
        Aegis.LargestPathValue.largest_path_value colors edges = ok r →
          Acyclic edges →
            ∀ (P : List Nat), IsValidPath colors.val.length edges P →
              ∀ c : Nat, IsLetterCode c → (countColor colors P c : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
        (hm_max : edges.val.length ≤ 100000)
        (hcolors : ColorsAreLetters colors)
        (hedges : EdgesWellFormed colors.val.length edges), ∀ r : Std.I64,
          Aegis.LargestPathValue.largest_path_value colors edges = ok r →
            Acyclic edges →
              ∀ (P : List Nat), IsValidPath colors.val.length edges P →
                ∀ c : Nat, IsLetterCode c → (countColor colors P c : Int) ≤ r.val) := by
    sorry

  /-- Whenever largest_path_value returns a result r, if the directed graph determined by edges contains no directed cycle, then there exists a nonempty valid path P such that val(P) = r, where val(P) is the maximum, over lowercase English letters c, of the number of nodes of P whose color is c.
    Preconditions: Let n = len(colors) and m = len(edges). Preconditions: 1 <= n <= 100000; every byte colors[i] for 0 <= i < n is the ASCII code of a lowercase English letter; 0 <= m <= 100000; for every j with 0 <= j < m, edges[j] is a vector of length 2, and if edges[j][0] = a and edges[j][1] = b then 0 <= a < n and 0 <= b < n. -/
  theorem spec_7
      (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
      (hm_max : edges.val.length ≤ 100000)
      (hcolors : ColorsAreLetters colors)
      (hedges : EdgesWellFormed colors.val.length edges) :
      ∀ r : Std.I64,
        Aegis.LargestPathValue.largest_path_value colors edges = ok r →
          Acyclic edges →
            ∃ P : List Nat,
              IsValidPath colors.val.length edges P ∧ (pathValue colors P : Int) = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
        (hm_max : edges.val.length ≤ 100000)
        (hcolors : ColorsAreLetters colors)
        (hedges : EdgesWellFormed colors.val.length edges), ∀ r : Std.I64,
          Aegis.LargestPathValue.largest_path_value colors edges = ok r →
            Acyclic edges →
              ∃ P : List Nat,
                IsValidPath colors.val.length edges P ∧ (pathValue colors P : Int) = r.val) := by
    sorry

  /-- Whenever largest_path_value returns a result r, if the directed graph determined by edges contains no directed cycle and there exists a nonempty valid path P = (x_0,...,x_{L-1}) and a lowercase English letter c such that colors[x_i] = c for every i with 0 <= i < L, then r >= L.
    Preconditions: Let n = len(colors) and m = len(edges). Preconditions: 1 <= n <= 100000; every byte colors[i] for 0 <= i < n is the ASCII code of a lowercase English letter; 0 <= m <= 100000; for every j with 0 <= j < m, edges[j] is a vector of length 2, and if edges[j][0] = a and edges[j][1] = b then 0 <= a < n and 0 <= b < n. -/
  theorem spec_8
      (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
      (hm_max : edges.val.length ≤ 100000)
      (hcolors : ColorsAreLetters colors)
      (hedges : EdgesWellFormed colors.val.length edges) :
      ∀ r : Std.I64,
        Aegis.LargestPathValue.largest_path_value colors edges = ok r →
          Acyclic edges →
            ∀ (P : List Nat), IsValidPath colors.val.length edges P →
              (∃ c : Nat, IsLetterCode c ∧ ∀ x : Nat, x ∈ P → colorAt colors x = c) →
                (P.length : Int) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
        (hm_max : edges.val.length ≤ 100000)
        (hcolors : ColorsAreLetters colors)
        (hedges : EdgesWellFormed colors.val.length edges), ∀ r : Std.I64,
          Aegis.LargestPathValue.largest_path_value colors edges = ok r →
            Acyclic edges →
              ∀ (P : List Nat), IsValidPath colors.val.length edges P →
                (∃ c : Nat, IsLetterCode c ∧ ∀ x : Nat, x ∈ P → colorAt colors x = c) →
                  (P.length : Int) ≤ r.val) := by
    sorry

  /-- Whenever largest_path_value returns a result r, if the directed graph determined by edges contains no directed cycle, then r <= Lmax, where Lmax is the maximum L such that there exists a nonempty valid path with exactly L nodes.
    Preconditions: Let n = len(colors) and m = len(edges). Preconditions: 1 <= n <= 100000; every byte colors[i] for 0 <= i < n is the ASCII code of a lowercase English letter; 0 <= m <= 100000; for every j with 0 <= j < m, edges[j] is a vector of length 2, and if edges[j][0] = a and edges[j][1] = b then 0 <= a < n and 0 <= b < n. -/
  theorem spec_9
      (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
      (hm_max : edges.val.length ≤ 100000)
      (hcolors : ColorsAreLetters colors)
      (hedges : EdgesWellFormed colors.val.length edges) :
      ∀ r : Std.I64,
        Aegis.LargestPathValue.largest_path_value colors edges = ok r →
          Acyclic edges →
            ∃ Lmax : Nat,
              IsMaxPathLength colors.val.length edges Lmax ∧ r.val ≤ (Lmax : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
        (hm_max : edges.val.length ≤ 100000)
        (hcolors : ColorsAreLetters colors)
        (hedges : EdgesWellFormed colors.val.length edges), ∀ r : Std.I64,
          Aegis.LargestPathValue.largest_path_value colors edges = ok r →
            Acyclic edges →
              ∃ Lmax : Nat,
                IsMaxPathLength colors.val.length edges Lmax ∧ r.val ≤ (Lmax : Int)) := by
    sorry

  /-- Whenever largest_path_value returns a result r, if the directed graph determined by edges contains no directed cycle and colors[i] != colors[j] for every pair 0 <= i < j < n, then r = 1.
    Preconditions: Let n = len(colors) and m = len(edges). Preconditions: 1 <= n <= 100000; every byte colors[i] for 0 <= i < n is the ASCII code of a lowercase English letter; 0 <= m <= 100000; for every j with 0 <= j < m, edges[j] is a vector of length 2, and if edges[j][0] = a and edges[j][1] = b then 0 <= a < n and 0 <= b < n. -/
  theorem spec_10
      (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
      (hm_max : edges.val.length ≤ 100000)
      (hcolors : ColorsAreLetters colors)
      (hedges : EdgesWellFormed colors.val.length edges) :
      ∀ r : Std.I64,
        Aegis.LargestPathValue.largest_path_value colors edges = ok r →
          Acyclic edges →
            (∀ i j : Nat, i < j → j < colors.val.length → colorAt colors i ≠ colorAt colors j) →
              r.val = 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
        (hm_max : edges.val.length ≤ 100000)
        (hcolors : ColorsAreLetters colors)
        (hedges : EdgesWellFormed colors.val.length edges), ∀ r : Std.I64,
          Aegis.LargestPathValue.largest_path_value colors edges = ok r →
            Acyclic edges →
              (∀ i j : Nat, i < j → j < colors.val.length → colorAt colors i ≠ colorAt colors j) →
                r.val = 1) := by
    sorry

  /-- Whenever largest_path_value returns a result r, if the directed graph determined by edges contains no directed cycle and for every j with 0 <= j < m we have colors[edges[j][0]] = colors[edges[j][1]], then r = Lmax, where Lmax is the maximum L such that there exists a nonempty valid path with exactly L nodes.
    Preconditions: Let n = len(colors) and m = len(edges). Preconditions: 1 <= n <= 100000; every byte colors[i] for 0 <= i < n is the ASCII code of a lowercase English letter; 0 <= m <= 100000; for every j with 0 <= j < m, edges[j] is a vector of length 2, and if edges[j][0] = a and edges[j][1] = b then 0 <= a < n and 0 <= b < n. -/
  theorem spec_11
      (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
      (hm_max : edges.val.length ≤ 100000)
      (hcolors : ColorsAreLetters colors)
      (hedges : EdgesWellFormed colors.val.length edges) :
      ∀ r : Std.I64,
        Aegis.LargestPathValue.largest_path_value colors edges = ok r →
          Acyclic edges →
            EdgesSameColor colors edges →
              ∃ Lmax : Nat,
                IsMaxPathLength colors.val.length edges Lmax ∧ r.val = (Lmax : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (colors : Slice Std.U8) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ colors.val.length) (hn_max : colors.val.length ≤ 100000)
        (hm_max : edges.val.length ≤ 100000)
        (hcolors : ColorsAreLetters colors)
        (hedges : EdgesWellFormed colors.val.length edges), ∀ r : Std.I64,
          Aegis.LargestPathValue.largest_path_value colors edges = ok r →
            Acyclic edges →
              EdgesSameColor colors edges →
                ∃ Lmax : Nat,
                  IsMaxPathLength colors.val.length edges Lmax ∧ r.val = (Lmax : Int)) := by
    sorry

  end AegisSpec.LargestPathValue
