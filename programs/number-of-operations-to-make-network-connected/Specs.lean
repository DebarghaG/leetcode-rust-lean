import Aegis.MakeConnected.Code.Funs

/-!
# Specifications of `Aegis.MakeConnected.make_connected`

LeetCode problem `number-of-operations-to-make-network-connected`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MakeConnected

  abbrev Conn := alloc.vec.Vec Std.I64

  abbrev Connections := Slice Conn

  def vertexCount (n : Std.I64) : Nat := n.val.toNat

  def IsVertex (n : Std.I64) (v : Int) : Prop := 0 ≤ v ∧ v < n.val

  noncomputable def vertexFinset (n : Std.I64) : Finset Int :=
    (Finset.range (vertexCount n)).image (fun k : Nat => (k : Int))

  def connectionEndpoints (v : Conn) : Option (Std.I64 × Std.I64) :=
    match v.val with
    | [a, b] => some (a, b)
    | _ => none

  def edgeList (connections : Connections) : List (Int × Int) :=
    connections.val.filterMap (fun v =>
      match connectionEndpoints v with
      | some (a, b) => some (a.val, b.val)
      | none => none)

  def canonPair (p : Int × Int) : Int × Int :=
    if p.1 < p.2 then p else (p.2, p.1)

  def graphEdges (connections : Connections) : List (Int × Int) :=
    (edgeList connections).map canonPair

  noncomputable def graphEdgeSet (connections : Connections) : Finset (Int × Int) :=
    (graphEdges connections).toFinset

  def Adj (X : Finset (Int × Int)) (u v : Int) : Prop :=
    (u, v) ∈ X ∨ (v, u) ∈ X

  def Reach (X : Finset (Int × Int)) (u v : Int) : Prop :=
    Relation.ReflTransGen (Adj X) u v

  def IsConnected (n : Std.I64) (X : Finset (Int × Int)) : Prop :=
    ∀ u v : Int, IsVertex n u → IsVertex n v → Reach X u v

  noncomputable def componentCount (n : Std.I64) (X : Finset (Int × Int)) : Nat := by
    classical
    exact ((vertexFinset n).filter
      (fun v => ∀ u : Int, IsVertex n u → u < v → ¬ Reach X u v)).card

  def ValidConnections (n : Std.I64) (connections : Connections) : Prop :=
    (∀ i (h : i < connections.val.length),
        ∃ a b : Std.I64,
          (connections.val.get ⟨i, h⟩).val = [a, b] ∧
          IsVertex n a.val ∧ IsVertex n b.val ∧ a.val ≠ b.val) ∧
    (∀ i j (hi : i < connections.val.length) (hj : j < connections.val.length),
        i < j →
        ∀ a b c d : Std.I64,
          (connections.val.get ⟨i, hi⟩).val = [a, b] →
          (connections.val.get ⟨j, hj⟩).val = [c, d] →
          ¬ ((a.val = c.val ∧ b.val = d.val) ∨
             (a.val = d.val ∧ b.val = c.val)))

  def ValidInput (n : Std.I64) (connections : Connections) : Prop :=
    1 ≤ n.val ∧ n.val ≤ 100000 ∧
    (0 : Int) ≤ (connections.val.length : Int) ∧
    (connections.val.length : Int) ≤ 100000 ∧
    ValidConnections n connections

  def SameOrSwap (v v' : Conn) : Prop :=
    v'.val = v.val ∨
      ∃ a b : Std.I64, v.val = [a, b] ∧ v'.val = [b, a]

  def ConnectionsSwap (connections connections' : Connections) : Prop :=
    List.Forall₂ SameOrSwap connections connections'

  def IsVertexPair (n : Std.I64) (e : Int × Int) : Prop :=
    IsVertex n e.1 ∧ IsVertex n e.2 ∧ e.1 < e.2

  def IsMoveSet (n : Std.I64) (X : Finset (Int × Int))
      (S T : Finset (Int × Int)) : Prop :=
    S ⊆ X ∧
    (∀ e ∈ T, IsVertexPair n e) ∧
    (∀ e ∈ T, e ∈ X → e ∈ S) ∧
    IsConnected n ((X \ S) ∪ T)

  def MinMoves (n : Std.I64) (X : Finset (Int × Int)) (r : Nat) : Prop :=
    (∃ S T : Finset (Int × Int), S.card = r ∧ T.card = r ∧ IsMoveSet n X S T) ∧
    (∀ r' : Nat, r' < r →
      ¬ ∃ S T : Finset (Int × Int), S.card = r' ∧ T.card = r' ∧ IsMoveSet n X S T)

  /-- The function returns a result r and: if m < n - 1 then r = -1; otherwise r = c - 1, where c is the number of connected components of the undirected graph G with vertex set {0,1,...,n-1} and edge set { {a_i, b_i} : 0 <= i < m }.
    Preconditions: n is an integer with 1 <= n <= 10^5. Let m = len(connections). We have 0 <= m <= 10^5. For every i with 0 <= i < m, len(connections[i]) = 2; writing a_i = connections[i][0] and b_i = connections[i][1], we have 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i. For every i, j with 0 <= i < j < m, the unordered pairs {a_i, b_i} and {a_j, b_j} are distinct. -/
  theorem spec_1 (n : Std.I64) (connections : Connections)
      (h : ValidInput n connections) :
      ∃ r : Std.I64,
        Aegis.MakeConnected.make_connected n connections = ok r ∧
        r.val =
          (if (connections.val.length : Int) < n.val - 1 then -1
           else (componentCount n (graphEdgeSet connections) : Int) - 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (connections : Connections)
        (h : ValidInput n connections), ∃ r : Std.I64,
          Aegis.MakeConnected.make_connected n connections = ok r ∧
          r.val =
            (if (connections.val.length : Int) < n.val - 1 then -1
             else (componentCount n (graphEdgeSet connections) : Int) - 1)) := by
    sorry

  /-- The function returns a result r (i.e., it does not fail, panic, or overflow).
    Preconditions: n is an integer with 1 <= n <= 10^5. Let m = len(connections). We have 0 <= m <= 10^5. For every i with 0 <= i < m, len(connections[i]) = 2; writing a_i = connections[i][0] and b_i = connections[i][1], we have 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i. For every i, j with 0 <= i < j < m, the unordered pairs {a_i, b_i} and {a_j, b_j} are distinct. -/
  theorem spec_2 (n : Std.I64) (connections : Connections)
      (h : ValidInput n connections) :
      ∃ r : Std.I64, Aegis.MakeConnected.make_connected n connections = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (connections : Connections)
        (h : ValidInput n connections), ∃ r : Std.I64, Aegis.MakeConnected.make_connected n connections = ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have -1 <= r <= n - 1.
    Preconditions: n is an integer with 1 <= n <= 10^5. Let m = len(connections). We have 0 <= m <= 10^5. For every i with 0 <= i < m, len(connections[i]) = 2; writing a_i = connections[i][0] and b_i = connections[i][1], we have 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i. For every i, j with 0 <= i < j < m, the unordered pairs {a_i, b_i} and {a_j, b_j} are distinct. -/
  theorem spec_3 (n : Std.I64) (connections : Connections)
      (h : ValidInput n connections) :
      ∀ r : Std.I64,
        Aegis.MakeConnected.make_connected n connections = ok r →
          -1 ≤ r.val ∧ r.val ≤ n.val - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (connections : Connections)
        (h : ValidInput n connections), ∀ r : Std.I64,
          Aegis.MakeConnected.make_connected n connections = ok r →
            -1 ≤ r.val ∧ r.val ≤ n.val - 1) := by
    sorry

  /-- The function returns -1 if and only if m < n - 1.
    Preconditions: n is an integer with 1 <= n <= 10^5. Let m = len(connections). We have 0 <= m <= 10^5. For every i with 0 <= i < m, len(connections[i]) = 2; writing a_i = connections[i][0] and b_i = connections[i][1], we have 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i. For every i, j with 0 <= i < j < m, the unordered pairs {a_i, b_i} and {a_j, b_j} are distinct. -/
  theorem spec_4 (n : Std.I64) (connections : Connections)
      (h : ValidInput n connections) :
      ∀ r : Std.I64,
        Aegis.MakeConnected.make_connected n connections = ok r →
          (r.val = -1 ↔ (connections.val.length : Int) < n.val - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (connections : Connections)
        (h : ValidInput n connections), ∀ r : Std.I64,
          Aegis.MakeConnected.make_connected n connections = ok r →
            (r.val = -1 ↔ (connections.val.length : Int) < n.val - 1)) := by
    sorry

  /-- The function returns 0 if and only if c = 1 (equivalently, G is connected).
    Preconditions: n is an integer with 1 <= n <= 10^5. Let m = len(connections). We have 0 <= m <= 10^5. For every i with 0 <= i < m, len(connections[i]) = 2; writing a_i = connections[i][0] and b_i = connections[i][1], we have 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i. For every i, j with 0 <= i < j < m, the unordered pairs {a_i, b_i} and {a_j, b_j} are distinct. Let G be the undirected graph with vertex set {0,1,...,n-1} and edge set E = { {a_i,b_i} : 0 <= i < m }, and let c be the number of connected components of G. -/
  theorem spec_5 (n : Std.I64) (connections : Connections)
      (h : ValidInput n connections) :
      ∀ r : Std.I64,
        Aegis.MakeConnected.make_connected n connections = ok r →
          (r.val = 0 ↔ componentCount n (graphEdgeSet connections) = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (connections : Connections)
        (h : ValidInput n connections), ∀ r : Std.I64,
          Aegis.MakeConnected.make_connected n connections = ok r →
            (r.val = 0 ↔ componentCount n (graphEdgeSet connections) = 1)) := by
    sorry

  /-- The function returns a value r with r >= 1 if and only if m >= n - 1 and c >= 2.
    Preconditions: n is an integer with 1 <= n <= 10^5. Let m = len(connections). We have 0 <= m <= 10^5. For every i with 0 <= i < m, len(connections[i]) = 2; writing a_i = connections[i][0] and b_i = connections[i][1], we have 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i. For every i, j with 0 <= i < j < m, the unordered pairs {a_i, b_i} and {a_j, b_j} are distinct. Let G be the undirected graph with vertex set {0,1,...,n-1} and edge set E = { {a_i,b_i} : 0 <= i < m }, and let c be the number of connected components of G. -/
  theorem spec_6 (n : Std.I64) (connections : Connections)
      (h : ValidInput n connections) :
      ∀ r : Std.I64,
        Aegis.MakeConnected.make_connected n connections = ok r →
          (1 ≤ r.val ↔
            (n.val - 1 ≤ (connections.val.length : Int) ∧
              componentCount n (graphEdgeSet connections) ≥ 2)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (connections : Connections)
        (h : ValidInput n connections), ∀ r : Std.I64,
          Aegis.MakeConnected.make_connected n connections = ok r →
            (1 ≤ r.val ↔
              (n.val - 1 ≤ (connections.val.length : Int) ∧
                componentCount n (graphEdgeSet connections) ≥ 2))) := by
    sorry

  /-- If n >= 2 and the function returns a result r with r >= 0, then r <= n - 2.
    Preconditions: n is an integer with 1 <= n <= 10^5. Let m = len(connections). We have 0 <= m <= 10^5. For every i with 0 <= i < m, len(connections[i]) = 2; writing a_i = connections[i][0] and b_i = connections[i][1], we have 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i. For every i, j with 0 <= i < j < m, the unordered pairs {a_i, b_i} and {a_j, b_j} are distinct. -/
  theorem spec_7 (n : Std.I64) (connections : Connections)
      (h : ValidInput n connections) :
      ∀ r : Std.I64,
        2 ≤ n.val →
          Aegis.MakeConnected.make_connected n connections = ok r →
            0 ≤ r.val → r.val ≤ n.val - 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (connections : Connections)
        (h : ValidInput n connections), ∀ r : Std.I64,
          2 ≤ n.val →
            Aegis.MakeConnected.make_connected n connections = ok r →
              0 ≤ r.val → r.val ≤ n.val - 2) := by
    sorry

  /-- The returned value r is unchanged if the list connections is permuted arbitrarily, or if the two elements of any individual connection are swapped (i.e., [a,b] replaced by [b,a]).
    Preconditions: n is an integer with 1 <= n <= 10^5. Let m = len(connections). We have 0 <= m <= 10^5. For every i with 0 <= i < m, len(connections[i]) = 2; writing a_i = connections[i][0] and b_i = connections[i][1], we have 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i. For every i, j with 0 <= i < j < m, the unordered pairs {a_i, b_i} and {a_j, b_j} are distinct. -/
  theorem spec_8 (n : Std.I64) (connections : Connections)
      (h : ValidInput n connections) :
      (∀ connections' : Connections, connections'.val.Perm connections.val →
          ∀ r : Std.I64,
            Aegis.MakeConnected.make_connected n connections = ok r →
              Aegis.MakeConnected.make_connected n connections' = ok r) ∧
      (∀ connections' : Connections, ConnectionsSwap connections connections' →
          ∀ r : Std.I64,
            Aegis.MakeConnected.make_connected n connections = ok r →
              Aegis.MakeConnected.make_connected n connections' = ok r) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (connections : Connections)
        (h : ValidInput n connections), (∀ connections' : Connections, connections'.val.Perm connections.val →
            ∀ r : Std.I64,
              Aegis.MakeConnected.make_connected n connections = ok r →
                Aegis.MakeConnected.make_connected n connections' = ok r) ∧
        (∀ connections' : Connections, ConnectionsSwap connections connections' →
            ∀ r : Std.I64,
              Aegis.MakeConnected.make_connected n connections = ok r →
                Aegis.MakeConnected.make_connected n connections' = ok r)) := by
    sorry

  /-- If m = m' and c = c', then the two calls return the same value.
    Preconditions: n is an integer with 1 <= n <= 10^5. Consider two inputs (n, connections) and (n, connections'). Let m = len(connections) and m' = len(connections'). We have 0 <= m <= 10^5 and 0 <= m' <= 10^5. For every i with 0 <= i < m, len(connections[i]) = 2; writing a_i = connections[i][0] and b_i = connections[i][1], we have 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i. For every i with 0 <= i < m', len(connections'[i]) = 2; writing a'_i = connections'[i][0] and b'_i = connections'[i][1], we have 0 <= a'_i < n, 0 <= b'_i < n, and a'_i != b'_i. Within each list the unordered endpoint pairs are distinct. Let G be the undirected graph for connections with vertex set {0,1,...,n-1} and edge set E = { {a_i,b_i} : 0 <= i < m }, and let G' be the undirected graph for connections' with edge set E' = { {a'_i,b'_i} : 0 <= i < m' }. Let c and c' be the numbers of connected components of G and G', respectively. -/
  theorem spec_9 (n : Std.I64) (connections connections' : Connections)
      (h : ValidInput n connections) (h' : ValidInput n connections')
      (hm : connections.val.length = connections'.val.length)
      (hc : componentCount n (graphEdgeSet connections) =
        componentCount n (graphEdgeSet connections')) :
      ∀ r r' : Std.I64,
        Aegis.MakeConnected.make_connected n connections = ok r →
          Aegis.MakeConnected.make_connected n connections' = ok r' →
            r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (connections connections' : Connections)
        (h : ValidInput n connections) (h' : ValidInput n connections')
        (hm : connections.val.length = connections'.val.length)
        (hc : componentCount n (graphEdgeSet connections) =
          componentCount n (graphEdgeSet connections')), ∀ r r' : Std.I64,
          Aegis.MakeConnected.make_connected n connections = ok r →
            Aegis.MakeConnected.make_connected n connections' = ok r' →
              r = r') := by
    sorry

  /-- Let r be the value returned on (n, connections), and assume r >= 0. For any pair of distinct vertices u, v in {0,1,...,n-1} such that {u,v} is not an edge of G, let connections' be the list obtained by appending [u,v]. Then the call on (n, connections') returns a value r' satisfying 0 <= r' <= r.
    Preconditions: n is an integer with 1 <= n <= 10^5. Let m = len(connections). We have 0 <= m <= 10^5. For every i with 0 <= i < m, len(connections[i]) = 2; writing a_i = connections[i][0] and b_i = connections[i][1], we have 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i. For every i, j with 0 <= i < j < m, the unordered pairs {a_i, b_i} and {a_j, b_j} are distinct. Let G be the undirected graph with vertex set {0,1,...,n-1} and edge set E = { {a_i,b_i} : 0 <= i < m }. -/
  theorem spec_10 (n : Std.I64) (connections : Connections)
      (h : ValidInput n connections)
      (u v : Std.I64) (hu : IsVertex n u.val) (hv : IsVertex n v.val)
      (huv : u.val ≠ v.val)
      (hnot : ¬ Adj (graphEdgeSet connections) u.val v.val)
      (connections' : Connections) (newConn : Conn)
      (hnew : newConn.val = [u, v])
      (happ : connections'.val = connections.val ++ [newConn])
      (r : Std.I64)
      (hr : Aegis.MakeConnected.make_connected n connections = ok r)
      (hr0 : 0 ≤ r.val) :
      ∀ r' : Std.I64,
        Aegis.MakeConnected.make_connected n connections' = ok r' →
          0 ≤ r'.val ∧ r'.val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (connections : Connections)
        (h : ValidInput n connections)
        (u v : Std.I64) (hu : IsVertex n u.val) (hv : IsVertex n v.val)
        (huv : u.val ≠ v.val)
        (hnot : ¬ Adj (graphEdgeSet connections) u.val v.val)
        (connections' : Connections) (newConn : Conn)
        (hnew : newConn.val = [u, v])
        (happ : connections'.val = connections.val ++ [newConn])
        (r : Std.I64)
        (hr : Aegis.MakeConnected.make_connected n connections = ok r)
        (hr0 : 0 ≤ r.val), ∀ r' : Std.I64,
          Aegis.MakeConnected.make_connected n connections' = ok r' →
            0 ≤ r'.val ∧ r'.val ≤ r.val) := by
    sorry

  /-- If the function returns a value r with r >= 0, then r is the minimum number of cable moves needed to make the network connected: there exists a set S of r edges of G and a set T of r unordered pairs of distinct vertices such that no pair in T is an original edge outside S, the graph with edge set (E minus S) union T is connected, and no such pair (S,T) with |S| = |T| < r exists.
    Preconditions: n is an integer with 1 <= n <= 10^5. Let m = len(connections). We have 0 <= m <= 10^5. For every i with 0 <= i < m, len(connections[i]) = 2; writing a_i = connections[i][0] and b_i = connections[i][1], we have 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i. For every i, j with 0 <= i < j < m, the unordered pairs {a_i, b_i} and {a_j, b_j} are distinct. Let G be the undirected graph with vertex set {0,1,...,n-1} and edge set E = { {a_i,b_i} : 0 <= i < m }. -/
  theorem spec_11 (n : Std.I64) (connections : Connections)
      (h : ValidInput n connections) :
      ∀ r : Std.I64,
        Aegis.MakeConnected.make_connected n connections = ok r →
          0 ≤ r.val →
            MinMoves n (graphEdgeSet connections) r.val.toNat := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (connections : Connections)
        (h : ValidInput n connections), ∀ r : Std.I64,
          Aegis.MakeConnected.make_connected n connections = ok r →
            0 ≤ r.val →
              MinMoves n (graphEdgeSet connections) r.val.toNat) := by
    sorry

  end AegisSpec.MakeConnected
