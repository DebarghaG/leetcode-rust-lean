import Aegis.LeadsToDestination.Code.Funs

/-!
# Specifications of `Aegis.LeadsToDestination.leads_to_destination`

LeetCode problem `all-paths-from-source-lead-to-destination`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LeadsToDestination

  def Edge (edges : Slice (alloc.vec.Vec I64)) (u v : Int) : Prop :=
    ∃ e ∈ edges.val, e.val.map (fun x : I64 => x.val) = [u, v]

  def Walk (edges : Slice (alloc.vec.Vec I64)) (p : List Int) : Prop :=
    ∀ (i : Nat) (u v : Int), p[i]? = some u → p[i + 1]? = some v → Edge edges u v

  def Reaches (edges : Slice (alloc.vec.Vec I64)) (s t : Int) : Prop :=
    ∃ p : List Int, p.head? = some s ∧ p.getLast? = some t ∧ Walk edges p

  def NoOut (n : Int) (edges : Slice (alloc.vec.Vec I64)) (v : Int) : Prop :=
    ∀ w : Int, 0 ≤ w → w < n → ¬ Edge edges v w

  def TerminatesAt (n : Int) (edges : Slice (alloc.vec.Vec I64)) (s t : Int) : Prop :=
    ∃ p : List Int,
      p.head? = some s ∧ p.getLast? = some t ∧ Walk edges p ∧ NoOut n edges t

  def SimpleCycle (edges : Slice (alloc.vec.Vec I64)) (vs : List Int) : Prop :=
    vs ≠ [] ∧ vs.Nodup ∧ Walk edges (vs ++ vs.take 1)

  def HasReachableCycle (edges : Slice (alloc.vec.Vec I64)) (s : Int) : Prop :=
    ∃ v : Int, Reaches edges s v ∧ ∃ vs : List Int, SimpleCycle edges vs ∧ v ∈ vs

  def Paths (edges : Slice (alloc.vec.Vec I64)) (s t : Int) : Set (List Int) :=
    {p | p.head? = some s ∧ p.getLast? = some t ∧ Walk edges p}

  /-- The function returns a result r, and r = true iff all three conditions hold: (1) there is a finite path v0,...,vk from source to destination (k >= 0, v0 = source, vk = destination, and for each 0 <= i < k the pair [vi,vi+1] occurs in edges); (2) every finite path v0,...,vk with v0 = source whose last vertex vk is terminal (there is no w with 0 <= w < n such that [vk,w] occurs in edges) has vk = destination; (3) there is no infinite path starting at source, equivalently no directed cycle, including a one-vertex self-loop, is reachable from source by a finite path.
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_1
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000) :
      ∃ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r ∧
        (r = true ↔
          (Reaches edges source.val destination.val ∧
            (∀ v : Int, Reaches edges source.val v → NoOut n.val edges v →
              v = destination.val) ∧
            ¬ HasReachableCycle edges source.val)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000), ∃ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r ∧
          (r = true ↔
            (Reaches edges source.val destination.val ∧
              (∀ v : Int, Reaches edges source.val v → NoOut n.val edges v →
                v = destination.val) ∧
              ¬ HasReachableCycle edges source.val))) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (it does not fail, panic, overflow, or go out of bounds).
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_2
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000) :
      ∃ r : Bool, Aegis.LeadsToDestination.leads_to_destination n edges source destination =
        ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000), ∃ r : Bool, Aegis.LeadsToDestination.leads_to_destination n edges source destination =
          ok r) := by
    sorry

  /-- If there is no w with 0 <= w < n such that [source,w] occurs in edges, then the function returns a result r and r = true iff source = destination.
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_3
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000)
      (hNoOut : NoOut n.val edges source.val) :
      ∃ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r ∧
        (r = true ↔ source.val = destination.val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000)
        (hNoOut : NoOut n.val edges source.val), ∃ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r ∧
          (r = true ↔ source.val = destination.val)) := by
    sorry

  /-- If there exist k >= 0 and vertices v0,...,vk such that v0 = source, the pair [vi,vi+1] occurs in edges for every 0 <= i < k, vk has no outgoing edge (no w with [vk,w] in edges), and vk != destination, then the function returns a result r and r = false.
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_4
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000)
      (hwt : ∃ t : Int, TerminatesAt n.val edges source.val t ∧ t ≠ destination.val) :
      ∃ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r ∧
        r = false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000)
        (hwt : ∃ t : Int, TerminatesAt n.val edges source.val t ∧ t ≠ destination.val), ∃ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r ∧
          r = false) := by
    sorry

  /-- If there is a directed cycle (including a self-loop v->v) that is reachable from source by a finite path, then the function returns a result r and r = false.
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_5
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000)
      (hcycle : HasReachableCycle edges source.val) :
      ∃ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r ∧
        r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000)
        (hcycle : HasReachableCycle edges source.val), ∃ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r ∧
          r = false) := by
    sorry

  /-- Whenever the function returns a result r and r = true, there exist k >= 0 and vertices v0,...,vk such that v0 = source, vk = destination, and for every 0 <= i < k the pair [vi,vi+1] occurs in edges. (The case k = 0 is allowed when source = destination.)
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_6
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000) :
      ∀ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
        r = true → Reaches edges source.val destination.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000), ∀ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
          r = true → Reaches edges source.val destination.val) := by
    sorry

  /-- Whenever the function returns a result r and r = true, for every vertex v, if v is reachable from source by a finite path and v has no outgoing edge in edges, then v = destination.
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_7
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000) :
      ∀ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
        r = true → ∀ v : Int, Reaches edges source.val v → NoOut n.val edges v →
          v = destination.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000), ∀ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
          r = true → ∀ v : Int, Reaches edges source.val v → NoOut n.val edges v →
            v = destination.val) := by
    sorry

  /-- Whenever the function returns a result r and r = true, no directed cycle, including a self-loop, is reachable from source by a finite path.
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_8
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000) :
      ∀ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
        r = true → ¬ HasReachableCycle edges source.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000), ∀ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
          r = true → ¬ HasReachableCycle edges source.val) := by
    sorry

  /-- Whenever the function returns a result r and r = true, for every vertex v, if v is reachable from source by a finite path, then there exists a finite path from v to destination.
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_9
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000) :
      ∀ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
        r = true → ∀ v : Int, Reaches edges source.val v → Reaches edges v destination.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000), ∀ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
          r = true → ∀ v : Int, Reaches edges source.val v → Reaches edges v destination.val) := by
    sorry

  /-- Whenever the function returns a result r and r = true, destination has no outgoing edge: there is no w with 0 <= w < n such that [destination,w] occurs in edges.
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_10
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000) :
      ∀ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
        r = true → NoOut n.val edges destination.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000), ∀ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
          r = true → NoOut n.val edges destination.val) := by
    sorry

  /-- For every two edge lists edges1 and edges2 satisfying the preconditions, if for every u,v with 0 <= u < n and 0 <= v < n the pair [u,v] occurs as an element of edges1 exactly when it occurs as an element of edges2, then the function returns the same Boolean result for (n,edges1,source,destination) and for (n,edges2,source,destination).
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; n <= 10000; both edges1 and edges2 satisfy: every element e has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; len(edges1) <= 10000 and len(edges2) <= 10000. Parallel edges, self-loops, and empty edge lists are allowed. -/
  theorem spec_11
      (n : I64) (edges1 edges2 : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hn10000 : n.val ≤ 10000)
      (hLen1 : ∀ e ∈ edges1.val, e.val.length = 2)
      (hBounds1 : ∀ e ∈ edges1.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (heLen1 : edges1.val.length ≤ 10000)
      (hLen2 : ∀ e ∈ edges2.val, e.val.length = 2)
      (hBounds2 : ∀ e ∈ edges2.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (heLen2 : edges2.val.length ≤ 10000)
      (hagree : ∀ u v : Int, 0 ≤ u → u < n.val → 0 ≤ v → v < n.val →
        (Edge edges1 u v ↔ Edge edges2 u v)) :
      ∃ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges1 source destination = ok r ∧
        Aegis.LeadsToDestination.leads_to_destination n edges2 source destination = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (edges1 edges2 : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hn10000 : n.val ≤ 10000)
        (hLen1 : ∀ e ∈ edges1.val, e.val.length = 2)
        (hBounds1 : ∀ e ∈ edges1.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (heLen1 : edges1.val.length ≤ 10000)
        (hLen2 : ∀ e ∈ edges2.val, e.val.length = 2)
        (hBounds2 : ∀ e ∈ edges2.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (heLen2 : edges2.val.length ≤ 10000)
        (hagree : ∀ u v : Int, 0 ≤ u → u < n.val → 0 ≤ v → v < n.val →
          (Edge edges1 u v ↔ Edge edges2 u v)), ∃ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges1 source destination = ok r ∧
          Aegis.LeadsToDestination.leads_to_destination n edges2 source destination = ok r) := by
    sorry

  /-- The function returns the same Boolean result when called on (n',edges,source,destination) as when called on (n,edges,source,destination).
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; n <= 10000; n' is an integer with n <= n' <= 10000; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_12
      (n n' : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hn10000 : n.val ≤ 10000) (hn' : n.val ≤ n'.val) (hn'10000 : n'.val ≤ 10000)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (heLen : edges.val.length ≤ 10000) :
      ∃ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n' edges source destination = ok r ∧
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n n' : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hn10000 : n.val ≤ 10000) (hn' : n.val ≤ n'.val) (hn'10000 : n'.val ≤ 10000)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (heLen : edges.val.length ≤ 10000), ∃ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n' edges source destination = ok r ∧
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if r = false, then at least one of the following holds: (i) there is a directed cycle, including a self-loop, reachable from source by a finite path; (ii) there exist k >= 0 and vertices v0,...,vk such that v0 = source, each consecutive pair [vi,vi+1] occurs in edges for 0 <= i < k, vk has no outgoing edge, and vk != destination.
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_13
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000) :
      ∀ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
        r = false →
          HasReachableCycle edges source.val ∨
            ∃ t : Int, TerminatesAt n.val edges source.val t ∧ t ≠ destination.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000), ∀ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
          r = false →
            HasReachableCycle edges source.val ∨
              ∃ t : Int, TerminatesAt n.val edges source.val t ∧ t ≠ destination.val) := by
    sorry

  /-- Whenever the function returns a result r and r = true, the set of all finite paths from source to destination is finite. Here a finite path is identified by its vertex sequence v0,...,vk with k >= 0, v0 = source, vk = destination, and each consecutive pair [vi,vi+1] occurring in edges; paths of different lengths or different vertex sequences count as different.
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_14
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000) :
      ∀ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
        r = true → (Paths edges source.val destination.val).Finite := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000), ∀ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
          r = true → (Paths edges source.val destination.val).Finite) := by
    sorry

  /-- Whenever the function returns a result r and r = true, every finite path v0,...,vk with v0 = source and each consecutive pair [vi,vi+1] occurring in edges has length k <= n - 1.
    Preconditions: n >= 1; 0 <= source < n; 0 <= destination < n; every element e of edges satisfies len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; n <= 10000; len(edges) <= 10000. Parallel edges, self-loops, and the empty edge list are allowed. -/
  theorem spec_15
      (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
      (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
      (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
      (hLen : ∀ e ∈ edges.val, e.val.length = 2)
      (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
      (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000) :
      ∀ r : Bool,
        Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
        r = true → ∀ p : List Int, p.head? = some source.val → Walk edges p →
          (p.length : Int) - 1 ≤ n.val - 1 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (source destination : I64)
        (hn : 1 ≤ n.val) (hsrc0 : 0 ≤ source.val) (hsrc : source.val < n.val)
        (hdst0 : 0 ≤ destination.val) (hdst : destination.val < n.val)
        (hLen : ∀ e ∈ edges.val, e.val.length = 2)
        (hBounds : ∀ e ∈ edges.val, ∀ x ∈ e.val, 0 ≤ x.val ∧ x.val < n.val)
        (hn10000 : n.val ≤ 10000) (heLen : edges.val.length ≤ 10000), ∀ r : Bool,
          Aegis.LeadsToDestination.leads_to_destination n edges source destination = ok r →
          r = true → ∀ p : List Int, p.head? = some source.val → Walk edges p →
            (p.length : Int) - 1 ≤ n.val - 1) := by
    sorry

  end AegisSpec.LeadsToDestination
