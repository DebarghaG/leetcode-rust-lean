import Aegis.FriendRequests.Code.Funs

/-!
# Specifications of `Aegis.FriendRequests.friend_requests`

LeetCode problem `process-restricted-friend-requests`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FriendRequests

  open Classical

  def vecInts (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

  def sliceInts (s : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    s.val.map vecInts

  def pairOk (n : Int) (p : List Int) : Prop :=
    ∃ x y, p = [x, y] ∧ 0 ≤ x ∧ x < n ∧ 0 ≤ y ∧ y < n ∧ x ≠ y

  def Reach (edges : List (Int × Int)) (p q : Int) : Prop :=
    Relation.ReflTransGen (fun a b => (a, b) ∈ edges ∨ (b, a) ∈ edges) p q

  def Conflict (restrictions : List (List Int)) (edges : List (Int × Int)) (u v : Int) : Prop :=
    ∃ p ∈ restrictions, ∃ x y, p = [x, y] ∧
      ((Reach edges x u ∧ Reach edges y v) ∨ (Reach edges x v ∧ Reach edges y u))

  noncomputable def acceptedEdges (restrictions requests : List (List Int)) :
      Nat → List (Int × Int)
    | 0 => []
    | j + 1 =>
      let prev := acceptedEdges restrictions requests j
      match requests[j]? with
      | some [u, v] =>
        if Reach prev u v ∨ ¬ Conflict restrictions prev u v then prev ++ [(u, v)] else prev
      | _ => prev

  def Equiv (restrictions requests : List (List Int)) (j : Nat) (p q : Int) : Prop :=
    Reach (acceptedEdges restrictions requests j) p q

  def accepted (restrictions requests : List (List Int)) (j : Nat) : Prop :=
    match requests[j]? with
    | some [u, v] => Reach (acceptedEdges restrictions requests j) u v ∨
        ¬ Conflict restrictions (acceptedEdges restrictions requests j) u v
    | _ => True

  def requestNotEquiv (restrictions requests : List (List Int)) (k : Nat) : Prop :=
    ∀ u v, requests[k]? = some [u, v] → ¬ Equiv restrictions requests k u v

  noncomputable def merges (restrictions requests : List (List Int)) (res : List Bool)
      (j : Nat) : Nat :=
    ((List.range j).filter
      (fun k => decide (res[k]? = some true ∧ requestNotEquiv restrictions requests k))).length

  noncomputable def numClasses (n : Nat) (rel : Int → Int → Prop) : Nat :=
    ((List.range n).filter
      (fun p => decide (∀ q : Nat, q < p → ¬ rel (q : Int) (p : Int)))).length

  def acceptedRequestEdges (requests : List (List Int)) (res : List Bool) (j : Nat) :
      List (Int × Int) :=
    (List.range j).filterMap (fun k =>
      match res[k]?, requests[k]? with
      | some true, some [u, v] => some (u, v)
      | _, _ => none)

  /-- Whenever friend_requests(n, restrictions, requests) returns a result r, len(r) = len(requests) and for every j with 0 <= j < len(requests), r[j] = true if and only if accepted(j).
    Preconditions: 2 <= n <= 1000; 0 <= len(restrictions) <= 1000; for every i with 0 <= i < len(restrictions), restrictions[i] is a pair [x,y] with 0 <= x,y < n and x != y; 1 <= len(requests) <= 1000; for every j with 0 <= j < len(requests), requests[j] is a pair [u,v] with 0 <= u,v < n and u != v. Define, for each j with 0 <= j <= len(requests), an equivalence relation ≈_j on {0,...,n-1} recursively: ≈_0 is equality; for each j < len(requests), let u = requests[j][0], v = requests[j][1]; let conflict(j) be the statement that there exists i with 0 <= i < len(restrictions) such that, writing x = restrictions[i][0] and y = restrictions[i][1], (x ≈_j u and y ≈_j v) or (x ≈_j v and y ≈_j u); let accepted(j) be (u ≈_j v) or (not conflict(j)); then ≈_{j+1} is the smallest equivalence relation on {0,...,n-1} containing ≈_j and the pair (u,v) if accepted(j), and ≈_{j+1} = ≈_j otherwise. -/
  theorem spec_1 (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hres_hi : (sliceInts restrictions).length ≤ 1000)
      (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
      (hreq_lo : 1 ≤ (sliceInts requests).length)
      (hreq_hi : (sliceInts requests).length ≤ 1000)
      (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p) :
      ∃ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r ∧
        r.val.length = (sliceInts requests).length ∧
        ∀ j, j < (sliceInts requests).length →
          (r.val[j]? = some true ↔ accepted (sliceInts restrictions) (sliceInts requests) j) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hres_hi : (sliceInts restrictions).length ≤ 1000)
        (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
        (hreq_lo : 1 ≤ (sliceInts requests).length)
        (hreq_hi : (sliceInts requests).length ≤ 1000)
        (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p), ∃ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r ∧
          r.val.length = (sliceInts requests).length ∧
          ∀ j, j < (sliceInts requests).length →
            (r.val[j]? = some true ↔ accepted (sliceInts restrictions) (sliceInts requests) j)) := by
    sorry

  /-- For every n, restrictions, requests satisfying the preconditions, friend_requests(n, restrictions, requests) returns a result r (it does not fail: no overflow, panic, or out-of-bounds access).
    Preconditions: 2 <= n <= 1000; 0 <= len(restrictions) <= 1000; for every i with 0 <= i < len(restrictions), restrictions[i] is a pair [x,y] with 0 <= x,y < n and x != y; 1 <= len(requests) <= 1000; for every j with 0 <= j < len(requests), requests[j] is a pair [u,v] with 0 <= u,v < n and u != v. -/
  theorem spec_2 (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hres_hi : (sliceInts restrictions).length ≤ 1000)
      (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
      (hreq_lo : 1 ≤ (sliceInts requests).length)
      (hreq_hi : (sliceInts requests).length ≤ 1000)
      (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p) :
      ∃ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hres_hi : (sliceInts restrictions).length ≤ 1000)
        (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
        (hreq_lo : 1 ≤ (sliceInts requests).length)
        (hreq_hi : (sliceInts requests).length ≤ 1000)
        (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p), ∃ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r) := by
    sorry

  /-- Whenever friend_requests(n, restrictions, requests) returns r, for every j with 0 <= j <= len(requests) and every p,q in {0,...,n-1}, p ≈_j q if and only if p and q are connected in the undirected graph with vertex set {0,...,n-1} and edge set consisting of the unordered pairs {requests[k][0], requests[k][1]} for all k with 0 <= k < j and r[k] = true.
    Preconditions: 2 <= n <= 1000; 0 <= len(restrictions) <= 1000; for every i with 0 <= i < len(restrictions), restrictions[i] is a pair [x,y] with 0 <= x,y < n and x != y; 1 <= len(requests) <= 1000; for every j with 0 <= j < len(requests), requests[j] is a pair [u,v] with 0 <= u,v < n and u != v. Define, for each j with 0 <= j <= len(requests), an equivalence relation ≈_j on {0,...,n-1} recursively: ≈_0 is equality; for each j < len(requests), let u = requests[j][0], v = requests[j][1]; let conflict(j) be the statement that there exists i with 0 <= i < len(restrictions) such that, writing x = restrictions[i][0] and y = restrictions[i][1], (x ≈_j u and y ≈_j v) or (x ≈_j v and y ≈_j u); let accepted(j) be (u ≈_j v) or (not conflict(j)); then ≈_{j+1} is the smallest equivalence relation on {0,...,n-1} containing ≈_j and the pair (u,v) if accepted(j), and ≈_{j+1} = ≈_j otherwise. -/
  theorem spec_3 (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hres_hi : (sliceInts restrictions).length ≤ 1000)
      (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
      (hreq_lo : 1 ≤ (sliceInts requests).length)
      (hreq_hi : (sliceInts requests).length ≤ 1000)
      (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p) :
      ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
        ∀ j, j ≤ (sliceInts requests).length →
          ∀ p q : Int, 0 ≤ p → p < n.val → 0 ≤ q → q < n.val →
            (Equiv (sliceInts restrictions) (sliceInts requests) j p q ↔
              Reach (acceptedRequestEdges (sliceInts requests) r.val j) p q) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hres_hi : (sliceInts restrictions).length ≤ 1000)
        (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
        (hreq_lo : 1 ≤ (sliceInts requests).length)
        (hreq_hi : (sliceInts requests).length ≤ 1000)
        (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p), ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
          ∀ j, j ≤ (sliceInts requests).length →
            ∀ p q : Int, 0 ≤ p → p < n.val → 0 ≤ q → q < n.val →
              (Equiv (sliceInts restrictions) (sliceInts requests) j p q ↔
                Reach (acceptedRequestEdges (sliceInts requests) r.val j) p q)) := by
    sorry

  /-- Whenever friend_requests(n, restrictions, requests) returns r, for every j with 0 <= j < len(requests), if requests[j][0] ≈_j requests[j][1] then r[j] = true.
    Preconditions: 2 <= n <= 1000; 0 <= len(restrictions) <= 1000; for every i with 0 <= i < len(restrictions), restrictions[i] is a pair [x,y] with 0 <= x,y < n and x != y; 1 <= len(requests) <= 1000; for every j with 0 <= j < len(requests), requests[j] is a pair [u,v] with 0 <= u,v < n and u != v. Define, for each j with 0 <= j <= len(requests), an equivalence relation ≈_j on {0,...,n-1} recursively: ≈_0 is equality; for each j < len(requests), let u = requests[j][0], v = requests[j][1]; let conflict(j) be the statement that there exists i with 0 <= i < len(restrictions) such that, writing x = restrictions[i][0] and y = restrictions[i][1], (x ≈_j u and y ≈_j v) or (x ≈_j v and y ≈_j u); let accepted(j) be (u ≈_j v) or (not conflict(j)); then ≈_{j+1} is the smallest equivalence relation on {0,...,n-1} containing ≈_j and the pair (u,v) if accepted(j), and ≈_{j+1} = ≈_j otherwise. -/
  theorem spec_4 (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hres_hi : (sliceInts restrictions).length ≤ 1000)
      (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
      (hreq_lo : 1 ≤ (sliceInts requests).length)
      (hreq_hi : (sliceInts requests).length ≤ 1000)
      (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p) :
      ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
        ∀ j, j < (sliceInts requests).length →
          ∀ u v : Int, (sliceInts requests)[j]? = some [u, v] →
            Equiv (sliceInts restrictions) (sliceInts requests) j u v → r.val[j]? = some true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hres_hi : (sliceInts restrictions).length ≤ 1000)
        (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
        (hreq_lo : 1 ≤ (sliceInts requests).length)
        (hreq_hi : (sliceInts requests).length ≤ 1000)
        (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p), ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
          ∀ j, j < (sliceInts requests).length →
            ∀ u v : Int, (sliceInts requests)[j]? = some [u, v] →
              Equiv (sliceInts restrictions) (sliceInts requests) j u v → r.val[j]? = some true) := by
    sorry

  /-- Whenever friend_requests(n, restrictions, requests) returns r, for every j with 0 <= j < len(requests), if conflict(j) is false then r[j] = true.
    Preconditions: 2 <= n <= 1000; 0 <= len(restrictions) <= 1000; for every i with 0 <= i < len(restrictions), restrictions[i] is a pair [x,y] with 0 <= x,y < n and x != y; 1 <= len(requests) <= 1000; for every j with 0 <= j < len(requests), requests[j] is a pair [u,v] with 0 <= u,v < n and u != v. Define, for each j with 0 <= j <= len(requests), an equivalence relation ≈_j on {0,...,n-1} recursively: ≈_0 is equality; for each j < len(requests), let u = requests[j][0], v = requests[j][1]; let conflict(j) be the statement that there exists i with 0 <= i < len(restrictions) such that, writing x = restrictions[i][0] and y = restrictions[i][1], (x ≈_j u and y ≈_j v) or (x ≈_j v and y ≈_j u); let accepted(j) be (u ≈_j v) or (not conflict(j)); then ≈_{j+1} is the smallest equivalence relation on {0,...,n-1} containing ≈_j and the pair (u,v) if accepted(j), and ≈_{j+1} = ≈_j otherwise. -/
  theorem spec_5 (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hres_hi : (sliceInts restrictions).length ≤ 1000)
      (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
      (hreq_lo : 1 ≤ (sliceInts requests).length)
      (hreq_hi : (sliceInts requests).length ≤ 1000)
      (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p) :
      ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
        ∀ j, j < (sliceInts requests).length →
          ∀ u v : Int, (sliceInts requests)[j]? = some [u, v] →
            ¬ Conflict (sliceInts restrictions)
                (acceptedEdges (sliceInts restrictions) (sliceInts requests) j) u v →
              r.val[j]? = some true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hres_hi : (sliceInts restrictions).length ≤ 1000)
        (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
        (hreq_lo : 1 ≤ (sliceInts requests).length)
        (hreq_hi : (sliceInts requests).length ≤ 1000)
        (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p), ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
          ∀ j, j < (sliceInts requests).length →
            ∀ u v : Int, (sliceInts requests)[j]? = some [u, v] →
              ¬ Conflict (sliceInts restrictions)
                  (acceptedEdges (sliceInts restrictions) (sliceInts requests) j) u v →
                r.val[j]? = some true) := by
    sorry

  /-- Whenever friend_requests(n, restrictions, requests) returns r, for every j with 0 <= j < len(requests), if r[j] = false then requests[j][0] is not ≈_j requests[j][1] and conflict(j) is true.
    Preconditions: 2 <= n <= 1000; 0 <= len(restrictions) <= 1000; for every i with 0 <= i < len(restrictions), restrictions[i] is a pair [x,y] with 0 <= x,y < n and x != y; 1 <= len(requests) <= 1000; for every j with 0 <= j < len(requests), requests[j] is a pair [u,v] with 0 <= u,v < n and u != v. Define, for each j with 0 <= j <= len(requests), an equivalence relation ≈_j on {0,...,n-1} recursively: ≈_0 is equality; for each j < len(requests), let u = requests[j][0], v = requests[j][1]; let conflict(j) be the statement that there exists i with 0 <= i < len(restrictions) such that, writing x = restrictions[i][0] and y = restrictions[i][1], (x ≈_j u and y ≈_j v) or (x ≈_j v and y ≈_j u); let accepted(j) be (u ≈_j v) or (not conflict(j)); then ≈_{j+1} is the smallest equivalence relation on {0,...,n-1} containing ≈_j and the pair (u,v) if accepted(j), and ≈_{j+1} = ≈_j otherwise. -/
  theorem spec_6 (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hres_hi : (sliceInts restrictions).length ≤ 1000)
      (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
      (hreq_lo : 1 ≤ (sliceInts requests).length)
      (hreq_hi : (sliceInts requests).length ≤ 1000)
      (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p) :
      ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
        ∀ j, j < (sliceInts requests).length →
          ∀ u v : Int, (sliceInts requests)[j]? = some [u, v] → r.val[j]? = some false →
            ¬ Equiv (sliceInts restrictions) (sliceInts requests) j u v ∧
              Conflict (sliceInts restrictions)
                (acceptedEdges (sliceInts restrictions) (sliceInts requests) j) u v := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hres_hi : (sliceInts restrictions).length ≤ 1000)
        (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
        (hreq_lo : 1 ≤ (sliceInts requests).length)
        (hreq_hi : (sliceInts requests).length ≤ 1000)
        (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p), ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
          ∀ j, j < (sliceInts requests).length →
            ∀ u v : Int, (sliceInts requests)[j]? = some [u, v] → r.val[j]? = some false →
              ¬ Equiv (sliceInts restrictions) (sliceInts requests) j u v ∧
                Conflict (sliceInts restrictions)
                  (acceptedEdges (sliceInts restrictions) (sliceInts requests) j) u v) := by
    sorry

  /-- Whenever friend_requests(n, restrictions, requests) returns r, for every j with 0 <= j < len(requests), if there exists i with 0 <= i < len(restrictions) such that {requests[j][0], requests[j][1]} = {restrictions[i][0], restrictions[i][1]}, then r[j] = false.
    Preconditions: 2 <= n <= 1000; 0 <= len(restrictions) <= 1000; for every i with 0 <= i < len(restrictions), restrictions[i] is a pair [x,y] with 0 <= x,y < n and x != y; 1 <= len(requests) <= 1000; for every j with 0 <= j < len(requests), requests[j] is a pair [u,v] with 0 <= u,v < n and u != v. Define, for each j with 0 <= j <= len(requests), an equivalence relation ≈_j on {0,...,n-1} recursively: ≈_0 is equality; for each j < len(requests), let u = requests[j][0], v = requests[j][1]; let conflict(j) be the statement that there exists i with 0 <= i < len(restrictions) such that, writing x = restrictions[i][0] and y = restrictions[i][1], (x ≈_j u and y ≈_j v) or (x ≈_j v and y ≈_j u); let accepted(j) be (u ≈_j v) or (not conflict(j)); then ≈_{j+1} is the smallest equivalence relation on {0,...,n-1} containing ≈_j and the pair (u,v) if accepted(j), and ≈_{j+1} = ≈_j otherwise. -/
  theorem spec_7 (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hres_hi : (sliceInts restrictions).length ≤ 1000)
      (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
      (hreq_lo : 1 ≤ (sliceInts requests).length)
      (hreq_hi : (sliceInts requests).length ≤ 1000)
      (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p) :
      ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
        ∀ j, j < (sliceInts requests).length →
          ∀ u v : Int, (sliceInts requests)[j]? = some [u, v] →
            (∃ p ∈ sliceInts restrictions, ∃ x y, p = [x, y] ∧
              ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) →
              r.val[j]? = some false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hres_hi : (sliceInts restrictions).length ≤ 1000)
        (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
        (hreq_lo : 1 ≤ (sliceInts requests).length)
        (hreq_hi : (sliceInts requests).length ≤ 1000)
        (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p), ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
          ∀ j, j < (sliceInts requests).length →
            ∀ u v : Int, (sliceInts requests)[j]? = some [u, v] →
              (∃ p ∈ sliceInts restrictions, ∃ x y, p = [x, y] ∧
                ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) →
                r.val[j]? = some false) := by
    sorry

  /-- Whenever friend_requests(n, restrictions, requests) returns r, if len(restrictions) = 0 then for every j with 0 <= j < len(requests), r[j] = true.
    Preconditions: 2 <= n <= 1000; 0 <= len(restrictions) <= 1000; for every i with 0 <= i < len(restrictions), restrictions[i] is a pair [x,y] with 0 <= x,y < n and x != y; 1 <= len(requests) <= 1000; for every j with 0 <= j < len(requests), requests[j] is a pair [u,v] with 0 <= u,v < n and u != v. Define, for each j with 0 <= j <= len(requests), an equivalence relation ≈_j on {0,...,n-1} recursively: ≈_0 is equality; for each j < len(requests), let u = requests[j][0], v = requests[j][1]; let conflict(j) be the statement that there exists i with 0 <= i < len(restrictions) such that, writing x = restrictions[i][0] and y = restrictions[i][1], (x ≈_j u and y ≈_j v) or (x ≈_j v and y ≈_j u); let accepted(j) be (u ≈_j v) or (not conflict(j)); then ≈_{j+1} is the smallest equivalence relation on {0,...,n-1} containing ≈_j and the pair (u,v) if accepted(j), and ≈_{j+1} = ≈_j otherwise. -/
  theorem spec_8 (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hres_hi : (sliceInts restrictions).length ≤ 1000)
      (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
      (hreq_lo : 1 ≤ (sliceInts requests).length)
      (hreq_hi : (sliceInts requests).length ≤ 1000)
      (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p) :
      ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
        (sliceInts restrictions).length = 0 →
          ∀ j, j < (sliceInts requests).length → r.val[j]? = some true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hres_hi : (sliceInts restrictions).length ≤ 1000)
        (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
        (hreq_lo : 1 ≤ (sliceInts requests).length)
        (hreq_hi : (sliceInts requests).length ≤ 1000)
        (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p), ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
          (sliceInts restrictions).length = 0 →
            ∀ j, j < (sliceInts requests).length → r.val[j]? = some true) := by
    sorry

  /-- Whenever friend_requests(n, restrictions, requests) returns r, for every j with 0 <= j <= len(requests), let merges(j) be the number of indices k with 0 <= k < j such that r[k] = true and requests[k][0] is not ≈_k requests[k][1]. Then the number of equivalence classes of ≈_j is n - merges(j).
    Preconditions: 2 <= n <= 1000; 0 <= len(restrictions) <= 1000; for every i with 0 <= i < len(restrictions), restrictions[i] is a pair [x,y] with 0 <= x,y < n and x != y; 1 <= len(requests) <= 1000; for every j with 0 <= j < len(requests), requests[j] is a pair [u,v] with 0 <= u,v < n and u != v. Define, for each j with 0 <= j <= len(requests), an equivalence relation ≈_j on {0,...,n-1} recursively: ≈_0 is equality; for each j < len(requests), let u = requests[j][0], v = requests[j][1]; let conflict(j) be the statement that there exists i with 0 <= i < len(restrictions) such that, writing x = restrictions[i][0] and y = restrictions[i][1], (x ≈_j u and y ≈_j v) or (x ≈_j v and y ≈_j u); let accepted(j) be (u ≈_j v) or (not conflict(j)); then ≈_{j+1} is the smallest equivalence relation on {0,...,n-1} containing ≈_j and the pair (u,v) if accepted(j), and ≈_{j+1} = ≈_j otherwise. -/
  theorem spec_9 (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hres_hi : (sliceInts restrictions).length ≤ 1000)
      (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
      (hreq_lo : 1 ≤ (sliceInts requests).length)
      (hreq_hi : (sliceInts requests).length ≤ 1000)
      (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p) :
      ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
        ∀ j, j ≤ (sliceInts requests).length →
          (numClasses n.val.toNat
              (Equiv (sliceInts restrictions) (sliceInts requests) j) : Int) =
            n.val - (merges (sliceInts restrictions) (sliceInts requests) r.val j : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hres_hi : (sliceInts restrictions).length ≤ 1000)
        (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
        (hreq_lo : 1 ≤ (sliceInts requests).length)
        (hreq_hi : (sliceInts requests).length ≤ 1000)
        (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p), ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
          ∀ j, j ≤ (sliceInts requests).length →
            (numClasses n.val.toNat
                (Equiv (sliceInts restrictions) (sliceInts requests) j) : Int) =
              n.val - (merges (sliceInts restrictions) (sliceInts requests) r.val j : Int)) := by
    sorry

  /-- Whenever friend_requests(n, restrictions, requests) returns r, for every j with 0 <= j < len(requests), if r[j] = true and requests[j][0] is not ≈_j requests[j][1], then conflict(j) is false.
    Preconditions: 2 <= n <= 1000; 0 <= len(restrictions) <= 1000; for every i with 0 <= i < len(restrictions), restrictions[i] is a pair [x,y] with 0 <= x,y < n and x != y; 1 <= len(requests) <= 1000; for every j with 0 <= j < len(requests), requests[j] is a pair [u,v] with 0 <= u,v < n and u != v. Define, for each j with 0 <= j <= len(requests), an equivalence relation ≈_j on {0,...,n-1} recursively: ≈_0 is equality; for each j < len(requests), let u = requests[j][0], v = requests[j][1]; let conflict(j) be the statement that there exists i with 0 <= i < len(restrictions) such that, writing x = restrictions[i][0] and y = restrictions[i][1], (x ≈_j u and y ≈_j v) or (x ≈_j v and y ≈_j u); let accepted(j) be (u ≈_j v) or (not conflict(j)); then ≈_{j+1} is the smallest equivalence relation on {0,...,n-1} containing ≈_j and the pair (u,v) if accepted(j), and ≈_{j+1} = ≈_j otherwise. -/
  theorem spec_10 (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hres_hi : (sliceInts restrictions).length ≤ 1000)
      (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
      (hreq_lo : 1 ≤ (sliceInts requests).length)
      (hreq_hi : (sliceInts requests).length ≤ 1000)
      (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p) :
      ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
        ∀ j, j < (sliceInts requests).length →
          ∀ u v : Int, (sliceInts requests)[j]? = some [u, v] → r.val[j]? = some true →
            ¬ Equiv (sliceInts restrictions) (sliceInts requests) j u v →
              ¬ Conflict (sliceInts restrictions)
                (acceptedEdges (sliceInts restrictions) (sliceInts requests) j) u v := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hres_hi : (sliceInts restrictions).length ≤ 1000)
        (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
        (hreq_lo : 1 ≤ (sliceInts requests).length)
        (hreq_hi : (sliceInts requests).length ≤ 1000)
        (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p), ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
          ∀ j, j < (sliceInts requests).length →
            ∀ u v : Int, (sliceInts requests)[j]? = some [u, v] → r.val[j]? = some true →
              ¬ Equiv (sliceInts restrictions) (sliceInts requests) j u v →
                ¬ Conflict (sliceInts restrictions)
                  (acceptedEdges (sliceInts restrictions) (sliceInts requests) j) u v) := by
    sorry

  /-- Whenever friend_requests(n, restrictions, requests) returns r, for every j with 0 <= j < len(requests), if r[j] = false then ≈_{j+1} = ≈_j.
    Preconditions: 2 <= n <= 1000; 0 <= len(restrictions) <= 1000; for every i with 0 <= i < len(restrictions), restrictions[i] is a pair [x,y] with 0 <= x,y < n and x != y; 1 <= len(requests) <= 1000; for every j with 0 <= j < len(requests), requests[j] is a pair [u,v] with 0 <= u,v < n and u != v. Define, for each j with 0 <= j <= len(requests), an equivalence relation ≈_j on {0,...,n-1} recursively: ≈_0 is equality; for each j < len(requests), let u = requests[j][0], v = requests[j][1]; let conflict(j) be the statement that there exists i with 0 <= i < len(restrictions) such that, writing x = restrictions[i][0] and y = restrictions[i][1], (x ≈_j u and y ≈_j v) or (x ≈_j v and y ≈_j u); let accepted(j) be (u ≈_j v) or (not conflict(j)); then ≈_{j+1} is the smallest equivalence relation on {0,...,n-1} containing ≈_j and the pair (u,v) if accepted(j), and ≈_{j+1} = ≈_j otherwise. -/
  theorem spec_11 (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hres_hi : (sliceInts restrictions).length ≤ 1000)
      (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
      (hreq_lo : 1 ≤ (sliceInts requests).length)
      (hreq_hi : (sliceInts requests).length ≤ 1000)
      (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p) :
      ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
        ∀ j, j < (sliceInts requests).length → r.val[j]? = some false →
          ∀ p q : Int, 0 ≤ p → p < n.val → 0 ≤ q → q < n.val →
            (Equiv (sliceInts restrictions) (sliceInts requests) (j + 1) p q ↔
              Equiv (sliceInts restrictions) (sliceInts requests) j p q) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (restrictions requests : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hres_hi : (sliceInts restrictions).length ≤ 1000)
        (hres_ok : ∀ p ∈ sliceInts restrictions, pairOk n.val p)
        (hreq_lo : 1 ≤ (sliceInts requests).length)
        (hreq_hi : (sliceInts requests).length ≤ 1000)
        (hreq_ok : ∀ p ∈ sliceInts requests, pairOk n.val p), ∀ r, Aegis.FriendRequests.friend_requests n restrictions requests = ok r →
          ∀ j, j < (sliceInts requests).length → r.val[j]? = some false →
            ∀ p q : Int, 0 ≤ p → p < n.val → 0 ≤ q → q < n.val →
              (Equiv (sliceInts restrictions) (sliceInts requests) (j + 1) p q ↔
                Equiv (sliceInts restrictions) (sliceInts requests) j p q)) := by
    sorry

  section Smoke

  private lemma reach_nil (p q : Int) (h : Reach ([] : List (Int × Int)) p q) : p = q := by
    induction h with
    | refl => rfl
    | tail _ hstep _ => exact absurd hstep (by simp)

  private lemma not_reach_nil_01 : ¬ Reach ([] : List (Int × Int)) (0 : Int) 1 := by
    intro h
    exact absurd (reach_nil 0 1 h) (by decide)

  private lemma not_conflict_02_nil_01 :
      ¬ Conflict [[0, 2]] ([] : List (Int × Int)) (0 : Int) 1 := by
    rintro ⟨p, hp, x, y, hxy, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [hp] at hxy
    simp only [List.cons.injEq, and_true] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    rcases hc with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact absurd (reach_nil 2 1 hy) (by decide)
    · exact absurd (reach_nil 0 1 hx) (by decide)

  private lemma reach_single_endpoints (p q : Int) (h : Reach [(0, 1)] p q) :
      q = p ∨ q = 0 ∨ q = 1 := by
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hstep _ =>
      rcases hstep with hstep | hstep
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hstep
        exact Or.inr (Or.inr (congrArg Prod.snd hstep))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hstep
        exact Or.inr (Or.inl (congrArg Prod.fst hstep))

  end Smoke

  end AegisSpec.FriendRequests
