import Aegis.NumOfMinutes.Code.Funs

/-!
# Specifications of `Aegis.NumOfMinutes.num_of_minutes`

LeetCode problem `time-needed-to-inform-all-employees`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumOfMinutes

  def values (s : Aeneas.Std.Slice Aeneas.Std.I64) : List Int :=
    s.val.map (fun x => x.val)

  def lget (l : List Int) (i : Int) : Option Int :=
    if 0 ≤ i then l[i.toNat]? else none

  def parent (manager : List Int) (v : Int) : Option Int :=
    match lget manager v with
    | none => none
    | some m => if 0 ≤ m then some m else none

  def ancestors (manager : List Int) : Nat → Int → List Int
    | 0, _ => []
    | k + 1, v =>
      match parent manager v with
      | none => []
      | some m => m :: ancestors manager k m

  def reachesHead (manager : List Int) (k : Nat) (headID v : Int) : Prop :=
    v = headID ∨ headID ∈ ancestors manager k v

  def learnTime (manager informTime : List Int) (k : Nat) (v : Int) : Int :=
    ((ancestors manager k v).map (fun u => (lget informTime u).getD 0)).sum

  def tabulate (n : Nat) (f : Int → Int) : List Int :=
    (List.range n).map (fun i => f (Int.ofNat i))

  def hasSubordinate (manager : List Int) (i : Int) : Bool :=
    manager.any (fun m => m == i)

  def rangeMaxWhere (n : Nat) (p : Int → Bool) (f : Int → Int) : Int :=
    (((List.range n).filter (fun i => p (Int.ofNat i))).map (fun i => f (Int.ofNat i))).foldr max 0

  def rangeMax (n : Nat) (f : Int → Int) : Int :=
    rangeMaxWhere n (fun _ => true) f

  def maxSupervisorTime (manager informTime : List Int) (n : Nat) : Int :=
    rangeMaxWhere n (fun i => hasSubordinate manager i) (fun i => (lget informTime i).getD 0)

  def supervisorTimeSum (manager informTime : List Int) (n : Nat) : Int :=
    (((List.range n).filter (fun i => hasSubordinate manager (Int.ofNat i))).map
      (fun i => (lget informTime (Int.ofNat i)).getD 0)).sum

  def maxLeafTime (manager informTime : List Int) (n : Nat) : Int :=
    rangeMaxWhere n (fun v => !hasSubordinate manager v) (learnTime manager informTime n)

  /-- The function returns a result r and r = max { A(v) | 0 <= v < n }, where A(v) is defined as follows: if v = headID then A(v) = 0; otherwise form the unique list v, manager[v], manager[manager[v]], ..., headID obtained by repeatedly applying manager until headID is reached, and let A(v) be the sum of informTime[u] over all entries u of this list except the first entry v (i.e., the sum over all proper ancestors of v). Equivalently, A(v) is the minute at which employee v learns the news, and r is the maximum such minute.
    Preconditions: n is an integer with 1 <= n <= 100000; headID is an integer with 0 <= headID < n; len(manager) = n and len(informTime) = n; manager[headID] = -1; for every i with 0 <= i < n and i != headID, 0 <= manager[i] < n; for every i with 0 <= i < n, 0 <= informTime[i] <= 1000; the directed graph with an edge manager[i] -> i for each i != headID is a tree rooted at headID (equivalently, starting from any employee and repeatedly taking manager reaches headID and no cycle occurs); and informTime[i] = 0 for every employee i with no direct subordinate (i.e., with no j such that 0 <= j < n and manager[j] = i). -/
  theorem spec_1
      (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
      (hman_len : (values manager).length = n.val.toNat)
      (hinfo_len : (values informTime).length = n.val.toNat)
      (hman_head : lget (values manager) headID.val = some (-1))
      (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
        ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
      (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
        ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
      (htree : ∀ v : Int, 0 ≤ v → v < n.val →
        reachesHead (values manager) n.val.toNat headID.val v)
      (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
        lget (values informTime) i = some 0) :
      ∃ r : Aeneas.Std.I64, Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r ∧
        r.val = rangeMax n.val.toNat (learnTime (values manager) (values informTime) n.val.toNat) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
        (hman_len : (values manager).length = n.val.toNat)
        (hinfo_len : (values informTime).length = n.val.toNat)
        (hman_head : lget (values manager) headID.val = some (-1))
        (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
          ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
        (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
          ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
        (htree : ∀ v : Int, 0 ≤ v → v < n.val →
          reachesHead (values manager) n.val.toNat headID.val v)
        (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
          lget (values informTime) i = some 0), ∃ r : Aeneas.Std.I64, Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r ∧
          r.val = rangeMax n.val.toNat (learnTime (values manager) (values informTime) n.val.toNat)) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, arithmetic overflow, or out-of-bounds access occurs).
    Preconditions: n is an integer with 1 <= n <= 100000; headID is an integer with 0 <= headID < n; len(manager) = n and len(informTime) = n; manager[headID] = -1; for every i with 0 <= i < n and i != headID, 0 <= manager[i] < n; for every i with 0 <= i < n, 0 <= informTime[i] <= 1000; the directed graph with an edge manager[i] -> i for each i != headID is a tree rooted at headID (equivalently, starting from any employee and repeatedly taking manager reaches headID and no cycle occurs); and informTime[i] = 0 for every employee i with no direct subordinate (i.e., with no j such that 0 <= j < n and manager[j] = i). -/
  theorem spec_2
      (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
      (hman_len : (values manager).length = n.val.toNat)
      (hinfo_len : (values informTime).length = n.val.toNat)
      (hman_head : lget (values manager) headID.val = some (-1))
      (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
        ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
      (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
        ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
      (htree : ∀ v : Int, 0 ≤ v → v < n.val →
        reachesHead (values manager) n.val.toNat headID.val v)
      (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
        lget (values informTime) i = some 0) :
      ∃ r : Aeneas.Std.I64,
        Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
        (hman_len : (values manager).length = n.val.toNat)
        (hinfo_len : (values informTime).length = n.val.toNat)
        (hman_head : lget (values manager) headID.val = some (-1))
        (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
          ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
        (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
          ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
        (htree : ∀ v : Int, 0 ≤ v → v < n.val →
          reachesHead (values manager) n.val.toNat headID.val v)
        (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
          lget (values informTime) i = some 0), ∃ r : Aeneas.Std.I64,
          Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= M, where M is the maximum of 0 and all values informTime[i] with 0 <= i < n such that employee i has at least one direct subordinate (i.e., there exists j with 0 <= j < n and manager[j] = i).
    Preconditions: n is an integer with 1 <= n <= 100000; headID is an integer with 0 <= headID < n; len(manager) = n and len(informTime) = n; manager[headID] = -1; for every i with 0 <= i < n and i != headID, 0 <= manager[i] < n; for every i with 0 <= i < n, 0 <= informTime[i] <= 1000; the directed graph with an edge manager[i] -> i for each i != headID is a tree rooted at headID (equivalently, starting from any employee and repeatedly taking manager reaches headID and no cycle occurs); and informTime[i] = 0 for every employee i with no direct subordinate (i.e., with no j such that 0 <= j < n and manager[j] = i). -/
  theorem spec_3
      (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
      (hman_len : (values manager).length = n.val.toNat)
      (hinfo_len : (values informTime).length = n.val.toNat)
      (hman_head : lget (values manager) headID.val = some (-1))
      (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
        ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
      (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
        ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
      (htree : ∀ v : Int, 0 ≤ v → v < n.val →
        reachesHead (values manager) n.val.toNat headID.val v)
      (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
        lget (values informTime) i = some 0) :
      ∀ r : Aeneas.Std.I64, Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r →
        maxSupervisorTime (values manager) (values informTime) n.val.toNat ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
        (hman_len : (values manager).length = n.val.toNat)
        (hinfo_len : (values informTime).length = n.val.toNat)
        (hman_head : lget (values manager) headID.val = some (-1))
        (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
          ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
        (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
          ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
        (htree : ∀ v : Int, 0 ≤ v → v < n.val →
          reachesHead (values manager) n.val.toNat headID.val v)
        (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
          lget (values informTime) i = some 0), ∀ r : Aeneas.Std.I64, Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r →
          maxSupervisorTime (values manager) (values informTime) n.val.toNat ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= S, where S is the sum of informTime[i] over all employees i with 0 <= i < n that have at least one direct subordinate (if there are none, S = 0).
    Preconditions: n is an integer with 1 <= n <= 100000; headID is an integer with 0 <= headID < n; len(manager) = n and len(informTime) = n; manager[headID] = -1; for every i with 0 <= i < n and i != headID, 0 <= manager[i] < n; for every i with 0 <= i < n, 0 <= informTime[i] <= 1000; the directed graph with an edge manager[i] -> i for each i != headID is a tree rooted at headID (equivalently, starting from any employee and repeatedly taking manager reaches headID and no cycle occurs); and informTime[i] = 0 for every employee i with no direct subordinate (i.e., with no j such that 0 <= j < n and manager[j] = i). -/
  theorem spec_4
      (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
      (hman_len : (values manager).length = n.val.toNat)
      (hinfo_len : (values informTime).length = n.val.toNat)
      (hman_head : lget (values manager) headID.val = some (-1))
      (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
        ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
      (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
        ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
      (htree : ∀ v : Int, 0 ≤ v → v < n.val →
        reachesHead (values manager) n.val.toNat headID.val v)
      (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
        lget (values informTime) i = some 0) :
      ∀ r : Aeneas.Std.I64, Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r →
        r.val ≤ supervisorTimeSum (values manager) (values informTime) n.val.toNat := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
        (hman_len : (values manager).length = n.val.toNat)
        (hinfo_len : (values informTime).length = n.val.toNat)
        (hman_head : lget (values manager) headID.val = some (-1))
        (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
          ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
        (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
          ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
        (htree : ∀ v : Int, 0 ≤ v → v < n.val →
          reachesHead (values manager) n.val.toNat headID.val v)
        (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
          lget (values informTime) i = some 0), ∀ r : Aeneas.Std.I64, Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r →
          r.val ≤ supervisorTimeSum (values manager) (values informTime) n.val.toNat) := by
    sorry

  /-- The function returns a result r and r = max { A(v) | 0 <= v < n and v has no direct subordinate }, where A(v) is defined as follows: if v = headID then A(v) = 0; otherwise form the unique list v, manager[v], manager[manager[v]], ..., headID obtained by repeatedly applying manager until headID is reached, and let A(v) be the sum of informTime[u] over all entries u of this list except the first entry v; 'v has no direct subordinate' means there is no j with 0 <= j < n and manager[j] = v.
    Preconditions: n is an integer with 1 <= n <= 100000; headID is an integer with 0 <= headID < n; len(manager) = n and len(informTime) = n; manager[headID] = -1; for every i with 0 <= i < n and i != headID, 0 <= manager[i] < n; for every i with 0 <= i < n, 0 <= informTime[i] <= 1000; the directed graph with an edge manager[i] -> i for each i != headID is a tree rooted at headID (equivalently, starting from any employee and repeatedly taking manager reaches headID and no cycle occurs); and informTime[i] = 0 for every employee i with no direct subordinate (i.e., with no j such that 0 <= j < n and manager[j] = i). -/
  theorem spec_5
      (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
      (hman_len : (values manager).length = n.val.toNat)
      (hinfo_len : (values informTime).length = n.val.toNat)
      (hman_head : lget (values manager) headID.val = some (-1))
      (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
        ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
      (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
        ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
      (htree : ∀ v : Int, 0 ≤ v → v < n.val →
        reachesHead (values manager) n.val.toNat headID.val v)
      (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
        lget (values informTime) i = some 0) :
      ∃ r : Aeneas.Std.I64, Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r ∧
        r.val = maxLeafTime (values manager) (values informTime) n.val.toNat := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
        (hman_len : (values manager).length = n.val.toNat)
        (hinfo_len : (values informTime).length = n.val.toNat)
        (hman_head : lget (values manager) headID.val = some (-1))
        (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
          ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
        (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
          ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
        (htree : ∀ v : Int, 0 ≤ v → v < n.val →
          reachesHead (values manager) n.val.toNat headID.val v)
        (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
          lget (values informTime) i = some 0), ∃ r : Aeneas.Std.I64, Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r ∧
          r.val = maxLeafTime (values manager) (values informTime) n.val.toNat) := by
    sorry

  /-- For every permutation p of {0, ..., n-1} with p(headID) = headID, define manager' and informTime' by manager'[p(i)] = p(manager[i]) for every i with 0 <= i < n and i != headID, manager'[headID] = -1, and informTime'[p(i)] = informTime[i] for every i with 0 <= i < n. If the function called with (n, headID, manager, informTime) returns r, then the function called with (n, headID, manager', informTime') also returns r.
    Preconditions: n is an integer with 1 <= n <= 100000; headID is an integer with 0 <= headID < n; len(manager) = n and len(informTime) = n; manager[headID] = -1; for every i with 0 <= i < n and i != headID, 0 <= manager[i] < n; for every i with 0 <= i < n, 0 <= informTime[i] <= 1000; the directed graph with an edge manager[i] -> i for each i != headID is a tree rooted at headID (equivalently, starting from any employee and repeatedly taking manager reaches headID and no cycle occurs); and informTime[i] = 0 for every employee i with no direct subordinate (i.e., with no j such that 0 <= j < n and manager[j] = i). -/
  theorem spec_6
      (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
      (hman_len : (values manager).length = n.val.toNat)
      (hinfo_len : (values informTime).length = n.val.toNat)
      (hman_head : lget (values manager) headID.val = some (-1))
      (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
        ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
      (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
        ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
      (htree : ∀ v : Int, 0 ≤ v → v < n.val →
        reachesHead (values manager) n.val.toNat headID.val v)
      (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
        lget (values informTime) i = some 0)
      (p q : Int → Int)
      (hp_head : p headID.val = headID.val)
      (hp_range : ∀ i : Int, 0 ≤ i → i < n.val → 0 ≤ p i ∧ p i < n.val)
      (hpq : ∀ i : Int, 0 ≤ i → i < n.val → p (q i) = i)
      (hqp : ∀ i : Int, 0 ≤ i → i < n.val → q (p i) = i)
      (manager' informTime' : Aeneas.Std.Slice Aeneas.Std.I64)
      (hman' : values manager' = tabulate n.val.toNat
        (fun j => if j = headID.val then (-1) else p ((lget (values manager) (q j)).getD 0)))
      (hinfo' : values informTime' = tabulate n.val.toNat
        (fun j => (lget (values informTime) (q j)).getD 0)) :
      ∀ r : Aeneas.Std.I64,
        Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r →
        Aegis.NumOfMinutes.num_of_minutes n headID manager' informTime' = ok r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
        (hman_len : (values manager).length = n.val.toNat)
        (hinfo_len : (values informTime).length = n.val.toNat)
        (hman_head : lget (values manager) headID.val = some (-1))
        (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
          ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
        (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
          ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
        (htree : ∀ v : Int, 0 ≤ v → v < n.val →
          reachesHead (values manager) n.val.toNat headID.val v)
        (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
          lget (values informTime) i = some 0)
        (p q : Int → Int)
        (hp_head : p headID.val = headID.val)
        (hp_range : ∀ i : Int, 0 ≤ i → i < n.val → 0 ≤ p i ∧ p i < n.val)
        (hpq : ∀ i : Int, 0 ≤ i → i < n.val → p (q i) = i)
        (hqp : ∀ i : Int, 0 ≤ i → i < n.val → q (p i) = i)
        (manager' informTime' : Aeneas.Std.Slice Aeneas.Std.I64)
        (hman' : values manager' = tabulate n.val.toNat
          (fun j => if j = headID.val then (-1) else p ((lget (values manager) (q j)).getD 0)))
        (hinfo' : values informTime' = tabulate n.val.toNat
          (fun j => (lget (values informTime) (q j)).getD 0)), ∀ r : Aeneas.Std.I64,
          Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r →
          Aegis.NumOfMinutes.num_of_minutes n headID manager' informTime' = ok r) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if informTime[i] = 0 for every employee i with 0 <= i < n that has at least one direct subordinate.
    Preconditions: n is an integer with 1 <= n <= 100000; headID is an integer with 0 <= headID < n; len(manager) = n and len(informTime) = n; manager[headID] = -1; for every i with 0 <= i < n and i != headID, 0 <= manager[i] < n; for every i with 0 <= i < n, 0 <= informTime[i] <= 1000; the directed graph with an edge manager[i] -> i for each i != headID is a tree rooted at headID (equivalently, starting from any employee and repeatedly taking manager reaches headID and no cycle occurs); and informTime[i] = 0 for every employee i with no direct subordinate (i.e., with no j such that 0 <= j < n and manager[j] = i). -/
  theorem spec_7
      (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
      (hman_len : (values manager).length = n.val.toNat)
      (hinfo_len : (values informTime).length = n.val.toNat)
      (hman_head : lget (values manager) headID.val = some (-1))
      (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
        ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
      (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
        ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
      (htree : ∀ v : Int, 0 ≤ v → v < n.val →
        reachesHead (values manager) n.val.toNat headID.val v)
      (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
        lget (values informTime) i = some 0) :
      ∃ r : Aeneas.Std.I64, Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r ∧
        (r.val = 0 ↔ ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = true →
          lget (values informTime) i = some 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n headID : Aeneas.Std.I64) (manager informTime : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
        (hman_len : (values manager).length = n.val.toNat)
        (hinfo_len : (values informTime).length = n.val.toNat)
        (hman_head : lget (values manager) headID.val = some (-1))
        (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
          ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
        (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
          ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
        (htree : ∀ v : Int, 0 ≤ v → v < n.val →
          reachesHead (values manager) n.val.toNat headID.val v)
        (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
          lget (values informTime) i = some 0), ∃ r : Aeneas.Std.I64, Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r ∧
          (r.val = 0 ↔ ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = true →
            lget (values informTime) i = some 0)) := by
    sorry

  /-- If the function called with (n, headID, manager, informTime) returns r and the function called with (n, headID, manager, informTime') returns r', then r' <= r.
    Preconditions: n is an integer with 1 <= n <= 100000; headID is an integer with 0 <= headID < n; len(manager) = n; len(informTime) = n and len(informTime') = n; manager[headID] = -1; for every i with 0 <= i < n and i != headID, 0 <= manager[i] < n; for every i with 0 <= i < n, 0 <= informTime[i] <= 1000 and 0 <= informTime'[i] <= informTime[i]; the directed graph with an edge manager[i] -> i for each i != headID is a tree rooted at headID (equivalently, starting from any employee and repeatedly taking manager reaches headID and no cycle occurs); and informTime[i] = 0 and informTime'[i] = 0 for every employee i with no direct subordinate (i.e., with no j such that 0 <= j < n and manager[j] = i). -/
  theorem spec_8
      (n headID : Aeneas.Std.I64)
      (manager informTime informTime' : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
      (hman_len : (values manager).length = n.val.toNat)
      (hinfo_len : (values informTime).length = n.val.toNat)
      (hinfo'_len : (values informTime').length = n.val.toNat)
      (hman_head : lget (values manager) headID.val = some (-1))
      (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
        ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
      (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
        ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
      (hinfo'_range : ∀ i : Int, 0 ≤ i → i < n.val →
        ∃ t t' : Int, lget (values informTime') i = some t ∧ lget (values informTime) i = some t' ∧
          0 ≤ t ∧ t ≤ t')
      (htree : ∀ v : Int, 0 ≤ v → v < n.val →
        reachesHead (values manager) n.val.toNat headID.val v)
      (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
        lget (values informTime) i = some 0)
      (hleaf' : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
        lget (values informTime') i = some 0) :
      ∀ r r' : Aeneas.Std.I64,
        Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r →
        Aegis.NumOfMinutes.num_of_minutes n headID manager informTime' = ok r' →
          r'.val ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n headID : Aeneas.Std.I64)
        (manager informTime informTime' : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hhead_lo : 0 ≤ headID.val) (hhead_hi : headID.val < n.val)
        (hman_len : (values manager).length = n.val.toNat)
        (hinfo_len : (values informTime).length = n.val.toNat)
        (hinfo'_len : (values informTime').length = n.val.toNat)
        (hman_head : lget (values manager) headID.val = some (-1))
        (hman_range : ∀ i : Int, 0 ≤ i → i < n.val → i ≠ headID.val →
          ∃ m : Int, lget (values manager) i = some m ∧ 0 ≤ m ∧ m < n.val)
        (hinfo_range : ∀ i : Int, 0 ≤ i → i < n.val →
          ∃ t : Int, lget (values informTime) i = some t ∧ 0 ≤ t ∧ t ≤ 1000)
        (hinfo'_range : ∀ i : Int, 0 ≤ i → i < n.val →
          ∃ t t' : Int, lget (values informTime') i = some t ∧ lget (values informTime) i = some t' ∧
            0 ≤ t ∧ t ≤ t')
        (htree : ∀ v : Int, 0 ≤ v → v < n.val →
          reachesHead (values manager) n.val.toNat headID.val v)
        (hleaf : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
          lget (values informTime) i = some 0)
        (hleaf' : ∀ i : Int, 0 ≤ i → i < n.val → hasSubordinate (values manager) i = false →
          lget (values informTime') i = some 0), ∀ r r' : Aeneas.Std.I64,
          Aegis.NumOfMinutes.num_of_minutes n headID manager informTime = ok r →
          Aegis.NumOfMinutes.num_of_minutes n headID manager informTime' = ok r' →
            r'.val ≤ r.val) := by
    sorry

  end AegisSpec.NumOfMinutes
