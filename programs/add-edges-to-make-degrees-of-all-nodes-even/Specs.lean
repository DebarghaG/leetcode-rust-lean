import Aegis.IsPossible.Code.Funs

/-!
# Specifications of `Aegis.IsPossible.is_possible`

LeetCode problem `add-edges-to-make-degrees-of-all-nodes-even`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.IsPossible

  namespace AegisSpec.IsPossible

  def edgeAt (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : alloc.vec.Vec Std.I64 :=
    edges.val.getD i (alloc.vec.Vec.new Std.I64)

  def edgeEnds (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
    (edgeAt edges i).val.map (fun x => x.val)

  def edgeFirst (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    (edgeEnds edges i).getD 0 0

  def edgeSecond (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    (edgeEnds edges i).getD 1 0

  def edgePair (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Finset Int :=
    {edgeFirst edges i, edgeSecond edges i}

  def vertexSet (n : Int) : Finset Int :=
    ((List.range n.toNat).map (fun k => (k : Int) + 1)).toFinset

  def IsVertexPair (n : Int) (e : Finset Int) : Prop :=
    e.card = 2 ∧ ∀ x ∈ e, x ∈ vertexSet n

  instance (n : Int) (e : Finset Int) : Decidable (IsVertexPair n e) :=
    inferInstanceAs (Decidable (e.card = 2 ∧ ∀ x ∈ e, x ∈ vertexSet n))

  def edgeSet (edges : Slice (alloc.vec.Vec Std.I64)) : Finset (Finset Int) :=
    (Finset.range edges.val.length).image (edgePair edges)

  def degree (edges : Slice (alloc.vec.Vec Std.I64)) (v : Int) : Nat :=
    ((edgeSet edges).filter (fun e => v ∈ e)).card

  def incident (F : Finset (Finset Int)) (v : Int) : Nat :=
    (F.filter (fun e => v ∈ e)).card

  def oddSet (n : Int) (edges : Slice (alloc.vec.Vec Std.I64)) : Finset Int :=
    (vertexSet n).filter (fun v => degree edges v % 2 = 1)

  def IsTJoin (n : Int) (edges : Slice (alloc.vec.Vec Std.I64)) (F : Finset (Finset Int)) : Prop :=
    (∀ e ∈ F, IsVertexPair n e) ∧
    F.card ≤ 2 ∧
    (∀ e ∈ F, e ∉ edgeSet edges) ∧
    (∀ v ∈ vertexSet n, (degree edges v + incident F v) % 2 = 0)

  def ValidInput (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    3 ≤ n.val ∧ n.val ≤ 100000 ∧
    2 ≤ edges.val.length ∧ edges.val.length ≤ 100000 ∧
    (∀ i, i < edges.val.length → (edgeEnds edges i).length = 2) ∧
    (∀ i, i < edges.val.length →
      1 ≤ edgeFirst edges i ∧ edgeFirst edges i ≤ n.val ∧
      1 ≤ edgeSecond edges i ∧ edgeSecond edges i ≤ n.val) ∧
    (∀ i, i < edges.val.length → edgeFirst edges i ≠ edgeSecond edges i) ∧
    (∀ i j, i < j → j < edges.val.length → edgePair edges i ≠ edgePair edges j)

  /-- Define V = {1, 2, ..., n}. Define E = { {edges[i][0], edges[i][1]} : 0 ≤ i < len(edges) }. For v in V, define deg(v) = |{ e in E : v ∈ e }|. The function returns a result r and r = true if and only if there exists a set F of unordered pairs of distinct vertices from V such that: (1) |F| ≤ 2; (2) every pair in F is not in E; (3) the pairs in F are pairwise distinct; (4) for every v in V, deg(v) + |{ e in F : v ∈ e }| is even.
    Preconditions: n is a machine integer with 3 ≤ n ≤ 100000. edges is a list with 2 ≤ len(edges) ≤ 100000. For every i with 0 ≤ i < len(edges), len(edges[i]) = 2, and 1 ≤ edges[i][0] ≤ n, 1 ≤ edges[i][1] ≤ n, and edges[i][0] ≠ edges[i][1]. For every i,j with 0 ≤ i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
  theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges) :
      ∃ r : Bool, is_possible n edges = ok r ∧ (r = true ↔ ∃ F, IsTJoin n.val edges F) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges), ∃ r : Bool, is_possible n edges = ok r ∧ (r = true ↔ ∃ F, IsTJoin n.val edges F)) := by
    sorry

  /-- The function returns a result (i.e., it does not fail with overflow, out-of-bounds, or a panic) for every input satisfying the preconditions.
    Preconditions: n is a machine integer with 3 ≤ n ≤ 100000. edges is a list with 2 ≤ len(edges) ≤ 100000. For every i with 0 ≤ i < len(edges), len(edges[i]) = 2, and 1 ≤ edges[i][0] ≤ n, 1 ≤ edges[i][1] ≤ n, and edges[i][0] ≠ edges[i][1]. For every i,j with 0 ≤ i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
  theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges) :
      ∃ r : Bool, is_possible n edges = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges), ∃ r : Bool, is_possible n edges = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if n = 3 then r = true.
    Preconditions: n is a machine integer with 3 ≤ n ≤ 100000. edges is a list with 2 ≤ len(edges) ≤ 100000. For every i with 0 ≤ i < len(edges), len(edges[i]) = 2, and 1 ≤ edges[i][0] ≤ n, 1 ≤ edges[i][1] ≤ n, and edges[i][0] ≠ edges[i][1]. For every i,j with 0 ≤ i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
  theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
      (r : Bool) (hr : is_possible n edges = ok r) (hn : n.val = 3) : r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
        (r : Bool) (hr : is_possible n edges = ok r) (hn : n.val = 3), r = true) := by
    sorry

  /-- Define V = {1, 2, ..., n}. Define E = { {edges[i][0], edges[i][1]} : 0 ≤ i < len(edges) }. For v in V, define deg(v) = |{ e in E : v ∈ e }|. Whenever the function returns a result r, if for every v in V deg(v) is even, then r = true.
    Preconditions: n is a machine integer with 3 ≤ n ≤ 100000. edges is a list with 2 ≤ len(edges) ≤ 100000. For every i with 0 ≤ i < len(edges), len(edges[i]) = 2, and 1 ≤ edges[i][0] ≤ n, 1 ≤ edges[i][1] ≤ n, and edges[i][0] ≠ edges[i][1]. For every i,j with 0 ≤ i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
  theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
      (r : Bool) (hr : is_possible n edges = ok r)
      (heven : ∀ v ∈ vertexSet n.val, degree edges v % 2 = 0) : r = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
        (r : Bool) (hr : is_possible n edges = ok r)
        (heven : ∀ v ∈ vertexSet n.val, degree edges v % 2 = 0), r = true) := by
    sorry

  /-- Define V = {1, 2, ..., n}. Define E = { {edges[i][0], edges[i][1]} : 0 ≤ i < len(edges) }. For v in V, define deg(v) = |{ e in E : v ∈ e }|. Let O = { v in V : deg(v) is odd }. Whenever the function returns a result r, if |O| > 4 then r = false.
    Preconditions: n is a machine integer with 3 ≤ n ≤ 100000. edges is a list with 2 ≤ len(edges) ≤ 100000. For every i with 0 ≤ i < len(edges), len(edges[i]) = 2, and 1 ≤ edges[i][0] ≤ n, 1 ≤ edges[i][1] ≤ n, and edges[i][0] ≠ edges[i][1]. For every i,j with 0 ≤ i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
  theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
      (r : Bool) (hr : is_possible n edges = ok r) (hO : 4 < (oddSet n.val edges).card) :
      r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
        (r : Bool) (hr : is_possible n edges = ok r) (hO : 4 < (oddSet n.val edges).card), r = false) := by
    sorry

  /-- Define V = {1, 2, ..., n}. Define E = { {edges[i][0], edges[i][1]} : 0 ≤ i < len(edges) }. For v in V, define deg(v) = |{ e in E : v ∈ e }|. Let O = { v in V : deg(v) is odd }. Whenever the function returns a result r, if |O| = 2 and O = {a,b} with a ≠ b and {a,b} is not in E, then r = true.
    Preconditions: n is a machine integer with 3 ≤ n ≤ 100000. edges is a list with 2 ≤ len(edges) ≤ 100000. For every i with 0 ≤ i < len(edges), len(edges[i]) = 2, and 1 ≤ edges[i][0] ≤ n, 1 ≤ edges[i][1] ≤ n, and edges[i][0] ≠ edges[i][1]. For every i,j with 0 ≤ i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
  theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
      (r : Bool) (hr : is_possible n edges = ok r) (a b : Int)
      (hcard : (oddSet n.val edges).card = 2) (hO : oddSet n.val edges = {a, b})
      (hab : a ≠ b) (hE : ({a, b} : Finset Int) ∉ edgeSet edges) : r = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
        (r : Bool) (hr : is_possible n edges = ok r) (a b : Int)
        (hcard : (oddSet n.val edges).card = 2) (hO : oddSet n.val edges = {a, b})
        (hab : a ≠ b) (hE : ({a, b} : Finset Int) ∉ edgeSet edges), r = true) := by
    sorry

  /-- Define V = {1, 2, ..., n}. Define E = { {edges[i][0], edges[i][1]} : 0 ≤ i < len(edges) }. For v in V, define deg(v) = |{ e in E : v ∈ e }|. Let O = { v in V : deg(v) is odd }. Whenever the function returns a result r, if |O| = 2 and O = {a,b} with a ≠ b and {a,b} is in E, then r = true if and only if there exists a vertex w in V with w ≠ a and w ≠ b such that {a,w} is not in E and {b,w} is not in E.
    Preconditions: n is a machine integer with 3 ≤ n ≤ 100000. edges is a list with 2 ≤ len(edges) ≤ 100000. For every i with 0 ≤ i < len(edges), len(edges[i]) = 2, and 1 ≤ edges[i][0] ≤ n, 1 ≤ edges[i][1] ≤ n, and edges[i][0] ≠ edges[i][1]. For every i,j with 0 ≤ i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
  theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
      (r : Bool) (hr : is_possible n edges = ok r) (a b : Int)
      (hcard : (oddSet n.val edges).card = 2) (hO : oddSet n.val edges = {a, b})
      (hab : a ≠ b) (hE : ({a, b} : Finset Int) ∈ edgeSet edges) :
      (r = true ↔ ∃ w ∈ vertexSet n.val, w ≠ a ∧ w ≠ b ∧
        ({a, w} : Finset Int) ∉ edgeSet edges ∧ ({b, w} : Finset Int) ∉ edgeSet edges) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
        (r : Bool) (hr : is_possible n edges = ok r) (a b : Int)
        (hcard : (oddSet n.val edges).card = 2) (hO : oddSet n.val edges = {a, b})
        (hab : a ≠ b) (hE : ({a, b} : Finset Int) ∈ edgeSet edges), (r = true ↔ ∃ w ∈ vertexSet n.val, w ≠ a ∧ w ≠ b ∧
          ({a, w} : Finset Int) ∉ edgeSet edges ∧ ({b, w} : Finset Int) ∉ edgeSet edges)) := by
    sorry

  /-- Define V = {1, 2, ..., n}. Define E = { {edges[i][0], edges[i][1]} : 0 ≤ i < len(edges) }. For v in V, define deg(v) = |{ e in E : v ∈ e }|. Let O = { v in V : deg(v) is odd }. Whenever the function returns a result r, if |O| = 4 and O = {a,b,c,d} with a,b,c,d pairwise distinct, then r = true if and only if at least one of the following three conditions holds: (i) {a,b} is not in E and {c,d} is not in E; (ii) {a,c} is not in E and {b,d} is not in E; (iii) {a,d} is not in E and {b,c} is not in E.
    Preconditions: n is a machine integer with 3 ≤ n ≤ 100000. edges is a list with 2 ≤ len(edges) ≤ 100000. For every i with 0 ≤ i < len(edges), len(edges[i]) = 2, and 1 ≤ edges[i][0] ≤ n, 1 ≤ edges[i][1] ≤ n, and edges[i][0] ≠ edges[i][1]. For every i,j with 0 ≤ i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
  theorem spec_8 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
      (r : Bool) (hr : is_possible n edges = ok r) (a b c d : Int)
      (hcard : (oddSet n.val edges).card = 4) (hO : oddSet n.val edges = {a, b, c, d})
      (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
      (r = true ↔
        (({a, b} : Finset Int) ∉ edgeSet edges ∧ ({c, d} : Finset Int) ∉ edgeSet edges) ∨
        (({a, c} : Finset Int) ∉ edgeSet edges ∧ ({b, d} : Finset Int) ∉ edgeSet edges) ∨
        (({a, d} : Finset Int) ∉ edgeSet edges ∧ ({b, c} : Finset Int) ∉ edgeSet edges)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
        (r : Bool) (hr : is_possible n edges = ok r) (a b c d : Int)
        (hcard : (oddSet n.val edges).card = 4) (hO : oddSet n.val edges = {a, b, c, d})
        (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d), (r = true ↔
          (({a, b} : Finset Int) ∉ edgeSet edges ∧ ({c, d} : Finset Int) ∉ edgeSet edges) ∨
          (({a, c} : Finset Int) ∉ edgeSet edges ∧ ({b, d} : Finset Int) ∉ edgeSet edges) ∨
          (({a, d} : Finset Int) ∉ edgeSet edges ∧ ({b, c} : Finset Int) ∉ edgeSet edges))) := by
    sorry

  /-- Define V = {1, 2, ..., n}. Define E = { {edges[i][0], edges[i][1]} : 0 ≤ i < len(edges) }. For v in V, define deg(v) = |{ e in E : v ∈ e }|. Whenever the function returns a result r, if r = true then there exists a set F of unordered pairs of distinct vertices from V such that |F| ≤ 2, every pair in F is not in E, the pairs in F are pairwise distinct, and for every v in V, deg(v) + |{ e in F : v ∈ e }| is even.
    Preconditions: n is a machine integer with 3 ≤ n ≤ 100000. edges is a list with 2 ≤ len(edges) ≤ 100000. For every i with 0 ≤ i < len(edges), len(edges[i]) = 2, and 1 ≤ edges[i][0] ≤ n, 1 ≤ edges[i][1] ≤ n, and edges[i][0] ≠ edges[i][1]. For every i,j with 0 ≤ i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
  theorem spec_9 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
      (r : Bool) (hr : is_possible n edges = ok r) (hrtrue : r = true) :
      ∃ F, IsTJoin n.val edges F := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
        (r : Bool) (hr : is_possible n edges = ok r) (hrtrue : r = true), ∃ F, IsTJoin n.val edges F) := by
    sorry

  /-- Define V = {1, 2, ..., n}. Define E = { {edges[i][0], edges[i][1]} : 0 ≤ i < len(edges) }. For v in V, define deg(v) = |{ e in E : v ∈ e }|. Whenever the function returns a result r, if r = false then for every set F of unordered pairs of distinct vertices from V with |F| ≤ 2, if every pair in F is not in E and the pairs in F are pairwise distinct, then there exists a vertex v in V such that deg(v) + |{ e in F : v ∈ e }| is odd.
    Preconditions: n is a machine integer with 3 ≤ n ≤ 100000. edges is a list with 2 ≤ len(edges) ≤ 100000. For every i with 0 ≤ i < len(edges), len(edges[i]) = 2, and 1 ≤ edges[i][0] ≤ n, 1 ≤ edges[i][1] ≤ n, and edges[i][0] ≠ edges[i][1]. For every i,j with 0 ≤ i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
  theorem spec_10 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
      (r : Bool) (hr : is_possible n edges = ok r) (hrfalse : r = false)
      (F : Finset (Finset Int)) (hF : ∀ e ∈ F, IsVertexPair n.val e) (hFcard : F.card ≤ 2)
      (hFnonedge : ∀ e ∈ F, e ∉ edgeSet edges) :
      ∃ v ∈ vertexSet n.val, (degree edges v + incident F v) % 2 = 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
        (r : Bool) (hr : is_possible n edges = ok r) (hrfalse : r = false)
        (F : Finset (Finset Int)) (hF : ∀ e ∈ F, IsVertexPair n.val e) (hFcard : F.card ≤ 2)
        (hFnonedge : ∀ e ∈ F, e ∉ edgeSet edges), ∃ v ∈ vertexSet n.val, (degree edges v + incident F v) % 2 = 1) := by
    sorry

  /-- Define V = {1, 2, ..., n}. Define E = { {edges[i][0], edges[i][1]} : 0 ≤ i < len(edges) }. For v in V, define deg(v) = |{ e in E : v ∈ e }|. Let O = { v in V : deg(v) is odd }. Whenever the function returns a result r, if r = true then |O| ∈ {0, 2, 4}.
    Preconditions: n is a machine integer with 3 ≤ n ≤ 100000. edges is a list with 2 ≤ len(edges) ≤ 100000. For every i with 0 ≤ i < len(edges), len(edges[i]) = 2, and 1 ≤ edges[i][0] ≤ n, 1 ≤ edges[i][1] ≤ n, and edges[i][0] ≠ edges[i][1]. For every i,j with 0 ≤ i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
  theorem spec_11 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
      (r : Bool) (hr : is_possible n edges = ok r) (hrtrue : r = true) :
      (oddSet n.val edges).card = 0 ∨ (oddSet n.val edges).card = 2 ∨
        (oddSet n.val edges).card = 4 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
        (r : Bool) (hr : is_possible n edges = ok r) (hrtrue : r = true), (oddSet n.val edges).card = 0 ∨ (oddSet n.val edges).card = 2 ∨
          (oddSet n.val edges).card = 4) := by
    sorry

  /-- Define V = {1,...,n}, E = { {edges[i][0],edges[i][1]} : 0 <= i < len(edges) }, deg(v) = |{ e in E : v in e }|, and O = { v in V : deg(v) is odd }. Whenever the function returns a result r, r = false if and only if at least one of the following holds: (a) |O| > 4; (b) |O| = 2 with O = {a,b} and {a,b} in E and, for every w in V with w != a and w != b, {a,w} in E or {b,w} in E; (c) |O| = 4 with O = {a,b,c,d} pairwise distinct and none of (i) {a,b} not in E and {c,d} not in E, (ii) {a,c} not in E and {b,d} not in E, (iii) {a,d} not in E and {b,c} not in E. This is the complete structural characterisation of the false case (the missing complement of spec_1, making the trickiest sub-case explicit).
    Preconditions: n is a machine integer with 3 <= n <= 100000. edges is a list with 2 <= len(edges) <= 100000. For every i with 0 <= i < len(edges), len(edges[i]) = 2, and 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, and edges[i][0] != edges[i][1]. For every i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0],edges[i][1]} and {edges[j][0],edges[j][1]} are distinct. -/
  theorem spec_12 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
      (r : Bool) (hr : is_possible n edges = ok r) :
      (r = false ↔
        4 < (oddSet n.val edges).card ∨
        (∃ a b, (oddSet n.val edges).card = 2 ∧ oddSet n.val edges = {a, b} ∧ a ≠ b ∧
          ({a, b} : Finset Int) ∈ edgeSet edges ∧
          ∀ w ∈ vertexSet n.val, w ≠ a → w ≠ b →
            ({a, w} : Finset Int) ∈ edgeSet edges ∨
              ({b, w} : Finset Int) ∈ edgeSet edges) ∨
        (∃ a b c d, (oddSet n.val edges).card = 4 ∧ oddSet n.val edges = {a, b, c, d} ∧
          a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
          ¬ (({a, b} : Finset Int) ∉ edgeSet edges ∧
              ({c, d} : Finset Int) ∉ edgeSet edges) ∧
          ¬ (({a, c} : Finset Int) ∉ edgeSet edges ∧
              ({b, d} : Finset Int) ∉ edgeSet edges) ∧
          ¬ (({a, d} : Finset Int) ∉ edgeSet edges ∧
              ({b, c} : Finset Int) ∉ edgeSet edges))) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput n edges)
        (r : Bool) (hr : is_possible n edges = ok r), (r = false ↔
          4 < (oddSet n.val edges).card ∨
          (∃ a b, (oddSet n.val edges).card = 2 ∧ oddSet n.val edges = {a, b} ∧ a ≠ b ∧
            ({a, b} : Finset Int) ∈ edgeSet edges ∧
            ∀ w ∈ vertexSet n.val, w ≠ a → w ≠ b →
              ({a, w} : Finset Int) ∈ edgeSet edges ∨
                ({b, w} : Finset Int) ∈ edgeSet edges) ∨
          (∃ a b c d, (oddSet n.val edges).card = 4 ∧ oddSet n.val edges = {a, b, c, d} ∧
            a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
            ¬ (({a, b} : Finset Int) ∉ edgeSet edges ∧
                ({c, d} : Finset Int) ∉ edgeSet edges) ∧
            ¬ (({a, c} : Finset Int) ∉ edgeSet edges ∧
                ({b, d} : Finset Int) ∉ edgeSet edges) ∧
            ¬ (({a, d} : Finset Int) ∉ edgeSet edges ∧
                ({b, c} : Finset Int) ∉ edgeSet edges)))) := by
    sorry

  end AegisSpec.IsPossible
