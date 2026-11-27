import Aegis.MinimumTime.Code.Funs

/-!
# Specifications of `Aegis.MinimumTime.minimum_time`

LeetCode problem `minimum-time-to-visit-disappearing-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumTime

  def ivals (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

  def vvals (v : alloc.vec.Vec I64) : List ℤ := v.val.map (fun x => x.val)

  def listGet (l : List ℤ) (i : ℤ) : Option ℤ := if 0 ≤ i then l[i.toNat]? else none

  def disappearAt (disappear : Slice I64) (i : ℤ) : Option ℤ := listGet (ivals disappear) i

  def resAt (r : alloc.vec.Vec I64) (i : ℤ) : Option ℤ := listGet (vvals r) i

  def HasEdge (edges : Slice (alloc.vec.Vec I64)) (u v w : ℤ) : Prop :=
    ∃ e ∈ edges.val, vvals e = [u, v, w]

  def Adj (edges : Slice (alloc.vec.Vec I64)) (u v w : ℤ) : Prop :=
    HasEdge edges u v w ∨ HasEdge edges v u w

  def Step (edges : Slice (alloc.vec.Vec I64)) (x y : ℤ × ℤ) : Prop :=
    ∃ w : ℤ, Adj edges x.1 y.1 w ∧ y.2 = x.2 + w

  def Consec (R : (ℤ × ℤ) → (ℤ × ℤ) → Prop) : List (ℤ × ℤ) → Prop
    | [] => True
    | [_] => True
    | x :: y :: rest => R x y ∧ Consec R (y :: rest)

  def OnTime (disappear : Slice I64) (steps : List (ℤ × ℤ)) : Prop :=
    ∀ x ∈ steps, ∃ d : ℤ, disappearAt disappear x.1 = some d ∧ x.2 < d

  def WalkTo (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64) (i T : ℤ) : Prop :=
    ∃ steps : List (ℤ × ℤ),
      steps.head? = some (0, 0) ∧ steps.getLast? = some (i, T) ∧
        Consec (Step edges) steps ∧ OnTime disappear steps

  def WalkToSimple (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64) (i T : ℤ) :
      Prop :=
    ∃ steps : List (ℤ × ℤ),
      steps.head? = some (0, 0) ∧ steps.getLast? = some (i, T) ∧
        Consec (Step edges) steps ∧ OnTime disappear steps ∧
        (steps.map (fun x => x.1)).Nodup

  def Pre (n : ℤ) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64) : Prop :=
    (1 ≤ n ∧ n ≤ 50000) ∧
      ((disappear.val.length : ℤ) = n ∧ ∀ d ∈ ivals disappear, 1 ≤ d ∧ d ≤ 100000) ∧
      ((edges.val.length : ℤ) ≤ 100000 ∧
        ∀ e ∈ edges.val,
          ∃ u v L : ℤ,
            vvals e = [u, v, L] ∧ 0 ≤ u ∧ u < n ∧ 0 ≤ v ∧ v < n ∧ 1 ≤ L ∧ L ≤ 100000)

  /-- The function returns a result r (it does not fail). A valid walk from 0 to i is a sequence p_0,...,p_k with k >= 0, p_0 = 0, p_k = i, and for each 0 <= j < k some edge e_j with endpoints p_j and p_{j+1} in either order and length L_j = edges[e_j][2]; let t_0 = 0 and t_{j+1} = t_j + L_j, and require t_j < disappear[p_j] for every 0 <= j <= k. The total time of the walk is t_k. Then len(r) = n, and for every i with 0 <= i < n: if a valid walk from 0 to i exists, r[i] is the minimum total time over all valid walks from 0 to i; if no valid walk from 0 to i exists, r[i] = -1.
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_1 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r ∧
          (r.val.length : ℤ) = n.val ∧
          ∀ i : ℤ, 0 ≤ i → i < n.val →
            ((∃ T : ℤ, resAt r i = some T ∧ WalkTo edges disappear i T ∧
                ∀ T' : ℤ, WalkTo edges disappear i T' → T ≤ T') ∨
              (resAt r i = some (-1) ∧ ∀ T : ℤ, ¬ WalkTo edges disappear i T)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∃ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r ∧
            (r.val.length : ℤ) = n.val ∧
            ∀ i : ℤ, 0 ≤ i → i < n.val →
              ((∃ T : ℤ, resAt r i = some T ∧ WalkTo edges disappear i T ∧
                  ∀ T' : ℤ, WalkTo edges disappear i T' → T ≤ T') ∨
                (resAt r i = some (-1) ∧ ∀ T : ℤ, ¬ WalkTo edges disappear i T))) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = n.
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_2 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r → (r.val.length : ℤ) = n.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r → (r.val.length : ℤ) = n.val) := by
    sorry

  /-- Whenever the function returns a result r, r[0] = 0.
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_3 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r → resAt r 0 = some 0 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r → resAt r 0 = some 0) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] != -1 then there exists a valid walk from 0 to i whose total time is exactly r[i]. Here a valid walk from 0 to i is a sequence p_0,...,p_k with p_0 = 0, p_k = i, consecutive vertices joined by an edge of edges, and if t_j is the cumulative sum of the chosen edge lengths up to p_j then t_j < disappear[p_j] for every 0 <= j <= k.
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_4 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r →
          ∀ (i d : ℤ), 0 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 →
            WalkTo edges disappear i d := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r →
            ∀ (i d : ℤ), 0 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 →
              WalkTo edges disappear i d) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n and r[i] != -1, every valid walk from 0 to i with total time t satisfies r[i] <= t. Here a valid walk is a sequence p_0,...,p_k with p_0 = 0, p_k = i, consecutive vertices joined by an edge of edges, and cumulative times t_j satisfying t_j < disappear[p_j] for every 0 <= j <= k.
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_5 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r →
          ∀ (i d : ℤ), 0 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 →
            ∀ t : ℤ, WalkTo edges disappear i t → d ≤ t := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r →
            ∀ (i d : ℤ), 0 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 →
              ∀ t : ℤ, WalkTo edges disappear i t → d ≤ t) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] = -1 then there is no valid walk from 0 to i. Here a valid walk is a sequence p_0,...,p_k with p_0 = 0, p_k = i, consecutive vertices joined by an edge of edges, and cumulative times t_j satisfying t_j < disappear[p_j] for every 0 <= j <= k.
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_6 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r →
          ∀ i : ℤ, 0 ≤ i → i < n.val → resAt r i = some (-1) →
            ∀ t : ℤ, ¬ WalkTo edges disappear i t := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r →
            ∀ i : ℤ, 0 ≤ i → i < n.val → resAt r i = some (-1) →
              ∀ t : ℤ, ¬ WalkTo edges disappear i t) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] != -1 then 0 <= r[i] < disappear[i].
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_7 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r →
          ∀ (i d di : ℤ), 0 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 →
            disappearAt disappear i = some di → 0 ≤ d ∧ d < di := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r →
            ∀ (i d di : ℤ), 0 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 →
              disappearAt disappear i = some di → 0 ≤ d ∧ d < di) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i < n, if r[i] != -1 then r[i] >= 1.
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_8 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r →
          ∀ (i d : ℤ), 1 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 → 1 ≤ d := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r →
            ∀ (i d : ℤ), 1 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 → 1 ≤ d) := by
    sorry

  /-- Whenever the function returns a result r, if len(edges) = 0 then r[0] = 0 and for every i with 1 <= i < n, r[i] = -1.
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_9 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r → edges.val.length = 0 →
          resAt r 0 = some 0 ∧ ∀ i : ℤ, 1 ≤ i → i < n.val → resAt r i = some (-1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r → edges.val.length = 0 →
            resAt r 0 = some 0 ∧ ∀ i : ℤ, 1 ≤ i → i < n.val → resAt r i = some (-1)) := by
    sorry

  /-- Whenever the function returns a result r, for every ordered pair (u,v) with 0 <= u < n and 0 <= v < n such that some edge e has endpoints u and v and length L = edges[e][2], if r[u] != -1 and r[u] + L < disappear[v], then r[v] != -1 and r[v] <= r[u] + L.
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_10 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r →
          ∀ (u v L du dv : ℤ), 0 ≤ u → u < n.val → 0 ≤ v → v < n.val → Adj edges u v L →
            resAt r u = some du → du ≠ -1 → disappearAt disappear v = some dv → du + L < dv →
              ∃ dv' : ℤ, resAt r v = some dv' ∧ dv' ≠ -1 ∧ dv' ≤ du + L := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r →
            ∀ (u v L du dv : ℤ), 0 ≤ u → u < n.val → 0 ≤ v → v < n.val → Adj edges u v L →
              resAt r u = some du → du ≠ -1 → disappearAt disappear v = some dv → du + L < dv →
                ∃ dv' : ℤ, resAt r v = some dv' ∧ dv' ≠ -1 ∧ dv' ≤ du + L) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i < n and r[i] != -1, there exists an edge e with endpoints i and some u (0 <= u < n) and length L = edges[e][2] such that r[u] != -1 and r[i] = r[u] + L.
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_11 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r →
          ∀ (i d : ℤ), 1 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 →
            ∃ (u du L : ℤ), 0 ≤ u ∧ u < n.val ∧ Adj edges i u L ∧ resAt r u = some du ∧
              du ≠ -1 ∧ d = du + L := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r →
            ∀ (i d : ℤ), 1 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 →
              ∃ (u du L : ℤ), 0 ≤ u ∧ u < n.val ∧ Adj edges i u L ∧ resAt r u = some du ∧
                du ≠ -1 ∧ d = du + L) := by
    sorry

  /-- The function returns a result for every input satisfying the preconditions; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_12 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∃ r : alloc.vec.Vec I64, Aegis.MinimumTime.minimum_time n edges disappear = ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∃ r : alloc.vec.Vec I64, Aegis.MinimumTime.minimum_time n edges disappear = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n and r[i] = -1, for every edge e with endpoints u and i and length L = edges[e][2], either r[u] = -1 or r[u] + L >= disappear[i].
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_13 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r →
          ∀ (i u L du di : ℤ), 0 ≤ i → i < n.val → 0 ≤ u → u < n.val → Adj edges i u L →
            resAt r i = some (-1) → resAt r u = some du → disappearAt disappear i = some di →
              du = -1 ∨ du + L ≥ di := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r →
            ∀ (i u L du di : ℤ), 0 ≤ i → i < n.val → 0 ≤ u → u < n.val → Adj edges i u L →
              resAt r i = some (-1) → resAt r u = some du → disappearAt disappear i = some di →
                du = -1 ∨ du + L ≥ di) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] != -1 then there exists a valid walk from 0 to i with total time r[i] in which no vertex occurs more than once. Here a valid walk is a sequence p_0,...,p_k with p_0 = 0, p_k = i, consecutive vertices joined by an edge of edges, and cumulative times t_j satisfying t_j < disappear[p_j] for every 0 <= j <= k.
    Preconditions: n is an integer with 1 <= n <= 50000; disappear is a slice with len(disappear) = n and 1 <= disappear[i] <= 100000 for every 0 <= i < n; edges is a slice with 0 <= len(edges) <= 100000, and for every 0 <= e < len(edges), edges[e] is a vector of length 3, edges[e] = [u_e, v_e, L_e], with 0 <= u_e, v_e < n and 1 <= L_e <= 100000. The graph is undirected, multiple edges are allowed, and self-loops are allowed. -/
  theorem spec_14 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
      (hpre : Pre n.val edges disappear) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.MinimumTime.minimum_time n edges disappear = ok r →
          ∀ (i d : ℤ), 0 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 →
            WalkToSimple edges disappear i d := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (disappear : Slice I64)
        (hpre : Pre n.val edges disappear), ∀ r : alloc.vec.Vec I64,
          Aegis.MinimumTime.minimum_time n edges disappear = ok r →
            ∀ (i d : ℤ), 0 ≤ i → i < n.val → resAt r i = some d → d ≠ -1 →
              WalkToSimple edges disappear i d) := by
    sorry

  end AegisSpec.MinimumTime
