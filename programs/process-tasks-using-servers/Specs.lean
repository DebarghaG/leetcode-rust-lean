import Aegis.AssignTasks.Code.Funs

/-!
# Specifications of `Aegis.AssignTasks.assign_tasks`

LeetCode problem `process-tasks-using-servers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.AssignTasks

  def vals (s : Slice Std.I64) : List ℤ := s.val.map fun v => v.val

  def intAt (l : List Std.I64) (i : ℕ) : ℤ :=
    match l[i]? with
    | some v => v.val
    | none => 0

  def vecVals (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map fun w => w.val

  structure Proc where
    free : List ℤ
    times : List ℤ
    ans : List ℕ

  def srvW (servers : List ℤ) (s : ℕ) : ℤ := servers.getD s 0

  def freeAt (F : List ℤ) (s : ℕ) : ℤ := F.getD s 0

  def keyLe (servers : List ℤ) (a b : ℕ) : Prop :=
    srvW servers a < srvW servers b ∨ (srvW servers a = srvW servers b ∧ a ≤ b)

  def keyLeB (servers : List ℤ) (a b : ℕ) : Bool :=
    if srvW servers a < srvW servers b then true
    else if srvW servers b < srvW servers a then false
    else a ≤ b

  def pickAux (servers F : List ℤ) (A : ℤ) : ℕ → Option ℕ → Option ℕ
    | 0, acc => acc
    | k + 1, acc =>
      pickAux servers F A k
        (if freeAt F k ≤ A then
          match acc with
          | none => some k
          | some b => if keyLeB servers k b then some k else acc
        else acc)

  def pickServer (servers F : List ℤ) (A : ℤ) : ℕ :=
    (pickAux servers F A servers.length none).getD 0

  def stepTime (j : ℕ) (F : List ℤ) : ℤ := max (j : ℤ) (F.min?.getD (j : ℤ))

  def stepFree (servers F : List ℤ) (j : ℕ) (t : ℤ) : List ℤ :=
    let A := stepTime j F
    F.set (pickServer servers F A) (A + t)

  def runFrom (servers : List ℤ) (j : ℕ) : List ℤ → List ℤ → List ℤ → List ℕ → Proc
    | [], F, Ts, R => ⟨F, Ts, R⟩
    | t :: ts, F, Ts, R =>
      let A := stepTime j F
      let r := pickServer servers F A
      runFrom servers (j + 1) ts (stepFree servers F j t) (Ts ++ [A]) (R ++ [r])

  def zeroFree (n : ℕ) : List ℤ := List.replicate n 0

  def stateAfter (servers tasks : List ℤ) (j : ℕ) : Proc :=
    runFrom servers 0 (tasks.take j) (zeroFree servers.length) [] []

  def freeState (servers tasks : List ℤ) (j : ℕ) : List ℤ := (stateAfter servers tasks j).free

  def assignTimeOf (servers tasks : List ℤ) (j : ℕ) : ℤ :=
    (stateAfter servers tasks (j + 1)).times.getD j 0

  def assignOf (servers tasks : List ℤ) (j : ℕ) : ℕ :=
    (stateAfter servers tasks (j + 1)).ans.getD j 0

  def answer (servers tasks : List ℤ) : List ℕ :=
    (runFrom servers 0 tasks (zeroFree servers.length) [] []).ans

  def answerInt (servers tasks : List ℤ) : List ℤ :=
    (answer servers tasks).map fun s => (s : ℤ)

  def freeBefore (servers tasks : List ℤ) (j s : ℕ) : Prop :=
    freeAt (freeState servers tasks j) s ≤ assignTimeOf servers tasks j

  /-- The function returns a result r such that len(r)=m and r is exactly the answer array of the task-queue process, characterized as follows. Let n=len(servers) and m=len(tasks). For each server index s with 0<=s<n set F_0[s]=0. For j=0,1,...,m-1 recursively define A_j = max(j, min{F_j[s] | 0<=s<n}). Let r[j] be the unique server index s with 0<=s<n such that F_j[s]<=A_j and, for every server index t with 0<=t<n and F_j[t]<=A_j, either servers[s]<servers[t], or servers[s]=servers[t] and s<=t. Then define F_{j+1}[s] = A_j + tasks[j] if s=r[j], and F_{j+1}[s] = F_j[s] otherwise. The returned vector r is the sequence r[0],r[1],...,r[m-1] obtained by these recursive choices. Here F_j[s] is the time when server s is free after tasks 0 through j-1 have been assigned, and A_j is the time at which task j is assigned.
    Preconditions: len(servers)=n, len(tasks)=m, 1<=n,m<=200000, for every i with 0<=i<n, 1<=servers[i]<=200000, and for every j with 0<=j<m, 1<=tasks[j]<=200000. -/
  theorem spec_1 (servers tasks : Slice Std.I64) (n m : ℕ)
      (hslen : servers.val.length = n) (htlen : tasks.val.length = m)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 200000) (hm1 : 1 ≤ m) (hm2 : m ≤ 200000)
      (hsrv : ∀ i, i < n → 1 ≤ intAt servers.val i ∧ intAt servers.val i ≤ 200000)
      (htsk : ∀ j, j < m → 1 ≤ intAt tasks.val j ∧ intAt tasks.val j ≤ 200000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.AssignTasks.assign_tasks servers tasks = ok r ∧ r.val.length = m ∧
        vecVals r = answerInt (vals servers) (vals tasks) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (servers tasks : Slice Std.I64) (n m : ℕ)
        (hslen : servers.val.length = n) (htlen : tasks.val.length = m)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 200000) (hm1 : 1 ≤ m) (hm2 : m ≤ 200000)
        (hsrv : ∀ i, i < n → 1 ≤ intAt servers.val i ∧ intAt servers.val i ≤ 200000)
        (htsk : ∀ j, j < m → 1 ≤ intAt tasks.val j ∧ intAt tasks.val j ≤ 200000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.AssignTasks.assign_tasks servers tasks = ok r ∧ r.val.length = m ∧
          vecVals r = answerInt (vals servers) (vals tasks)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or go out of bounds.
    Preconditions: len(servers)=n, len(tasks)=m, 1<=n,m<=200000, for every i with 0<=i<n, 1<=servers[i]<=200000, and for every j with 0<=j<m, 1<=tasks[j]<=200000. -/
  theorem spec_2 (servers tasks : Slice Std.I64) (n m : ℕ)
      (hslen : servers.val.length = n) (htlen : tasks.val.length = m)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 200000) (hm1 : 1 ≤ m) (hm2 : m ≤ 200000)
      (hsrv : ∀ i, i < n → 1 ≤ intAt servers.val i ∧ intAt servers.val i ≤ 200000)
      (htsk : ∀ j, j < m → 1 ≤ intAt tasks.val j ∧ intAt tasks.val j ≤ 200000) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.AssignTasks.assign_tasks servers tasks = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (servers tasks : Slice Std.I64) (n m : ℕ)
        (hslen : servers.val.length = n) (htlen : tasks.val.length = m)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 200000) (hm1 : 1 ≤ m) (hm2 : m ≤ 200000)
        (hsrv : ∀ i, i < n → 1 ≤ intAt servers.val i ∧ intAt servers.val i ≤ 200000)
        (htsk : ∀ j, j < m → 1 ≤ intAt tasks.val j ∧ intAt tasks.val j ≤ 200000), ∃ r : alloc.vec.Vec Std.I64, Aegis.AssignTasks.assign_tasks servers tasks = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r)=m, so the answer contains exactly one entry for each task.
    Preconditions: len(servers)=n, len(tasks)=m, 1<=n,m<=200000, for every i with 0<=i<n, 1<=servers[i]<=200000, and for every j with 0<=j<m, 1<=tasks[j]<=200000. -/
  theorem spec_3 (servers tasks : Slice Std.I64) (n m : ℕ)
      (hslen : servers.val.length = n) (htlen : tasks.val.length = m)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 200000) (hm1 : 1 ≤ m) (hm2 : m ≤ 200000)
      (hsrv : ∀ i, i < n → 1 ≤ intAt servers.val i ∧ intAt servers.val i ≤ 200000)
      (htsk : ∀ j, j < m → 1 ≤ intAt tasks.val j ∧ intAt tasks.val j ≤ 200000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.AssignTasks.assign_tasks servers tasks = ok r) :
      r.val.length = m := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (servers tasks : Slice Std.I64) (n m : ℕ)
        (hslen : servers.val.length = n) (htlen : tasks.val.length = m)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 200000) (hm1 : 1 ≤ m) (hm2 : m ≤ 200000)
        (hsrv : ∀ i, i < n → 1 ≤ intAt servers.val i ∧ intAt servers.val i ≤ 200000)
        (htsk : ∀ j, j < m → 1 ≤ intAt tasks.val j ∧ intAt tasks.val j ≤ 200000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.AssignTasks.assign_tasks servers tasks = ok r), r.val.length = m) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0<=j<m, r[j] is an integer satisfying 0<=r[j]<n. Thus every answer is a valid 0-based index into servers.
    Preconditions: len(servers)=n, len(tasks)=m, 1<=n,m<=200000, for every i with 0<=i<n, 1<=servers[i]<=200000, and for every j with 0<=j<m, 1<=tasks[j]<=200000. -/
  theorem spec_4 (servers tasks : Slice Std.I64) (n m : ℕ)
      (hslen : servers.val.length = n) (htlen : tasks.val.length = m)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 200000) (hm1 : 1 ≤ m) (hm2 : m ≤ 200000)
      (hsrv : ∀ i, i < n → 1 ≤ intAt servers.val i ∧ intAt servers.val i ≤ 200000)
      (htsk : ∀ j, j < m → 1 ≤ intAt tasks.val j ∧ intAt tasks.val j ≤ 200000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.AssignTasks.assign_tasks servers tasks = ok r) :
      ∀ j, j < m → 0 ≤ intAt r.val j ∧ intAt r.val j < (n : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (servers tasks : Slice Std.I64) (n m : ℕ)
        (hslen : servers.val.length = n) (htlen : tasks.val.length = m)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 200000) (hm1 : 1 ≤ m) (hm2 : m ≤ 200000)
        (hsrv : ∀ i, i < n → 1 ≤ intAt servers.val i ∧ intAt servers.val i ≤ 200000)
        (htsk : ∀ j, j < m → 1 ≤ intAt tasks.val j ∧ intAt tasks.val j ≤ 200000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.AssignTasks.assign_tasks servers tasks = ok r), ∀ j, j < m → 0 ≤ intAt r.val j ∧ intAt r.val j < (n : ℤ)) := by
    sorry

  /-- Whenever assign_tasks(servers,tasks) returns r and assign_tasks(servers2,tasks) returns r2, we have len(r)=len(r2)=m and r[j]=r2[j] for every j with 0<=j<m.
    Preconditions: len(servers)=len(servers2)=n, len(tasks)=m, 1<=n,m<=200000, all entries of servers and servers2 are in the range 1..200000, all entries of tasks are in the range 1..200000, and for all i,k with 0<=i,k<n, servers[i]<servers[k] if and only if servers2[i]<servers2[k], and servers[i]=servers[k] if and only if servers2[i]=servers2[k]. -/
  theorem spec_5 (servers servers2 tasks : Slice Std.I64) (n m : ℕ)
      (hslen : servers.val.length = n) (hslen2 : servers2.val.length = n)
      (htlen : tasks.val.length = m)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 200000) (hm1 : 1 ≤ m) (hm2 : m ≤ 200000)
      (hsrv : ∀ i, i < n → 1 ≤ intAt servers.val i ∧ intAt servers.val i ≤ 200000)
      (hsrv2 : ∀ i, i < n → 1 ≤ intAt servers2.val i ∧ intAt servers2.val i ≤ 200000)
      (htsk : ∀ j, j < m → 1 ≤ intAt tasks.val j ∧ intAt tasks.val j ≤ 200000)
      (hlt : ∀ i k, i < n → k < n →
        (intAt servers.val i < intAt servers.val k ↔ intAt servers2.val i < intAt servers2.val k))
      (heq : ∀ i k, i < n → k < n →
        (intAt servers.val i = intAt servers.val k ↔ intAt servers2.val i = intAt servers2.val k))
      (r r2 : alloc.vec.Vec Std.I64)
      (hr : Aegis.AssignTasks.assign_tasks servers tasks = ok r)
      (hr2 : Aegis.AssignTasks.assign_tasks servers2 tasks = ok r2) :
      r.val.length = m ∧ r2.val.length = m ∧
        ∀ j, j < m → r.val[j]? = r2.val[j]? := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (servers servers2 tasks : Slice Std.I64) (n m : ℕ)
        (hslen : servers.val.length = n) (hslen2 : servers2.val.length = n)
        (htlen : tasks.val.length = m)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 200000) (hm1 : 1 ≤ m) (hm2 : m ≤ 200000)
        (hsrv : ∀ i, i < n → 1 ≤ intAt servers.val i ∧ intAt servers.val i ≤ 200000)
        (hsrv2 : ∀ i, i < n → 1 ≤ intAt servers2.val i ∧ intAt servers2.val i ≤ 200000)
        (htsk : ∀ j, j < m → 1 ≤ intAt tasks.val j ∧ intAt tasks.val j ≤ 200000)
        (hlt : ∀ i k, i < n → k < n →
          (intAt servers.val i < intAt servers.val k ↔ intAt servers2.val i < intAt servers2.val k))
        (heq : ∀ i k, i < n → k < n →
          (intAt servers.val i = intAt servers.val k ↔ intAt servers2.val i = intAt servers2.val k))
        (r r2 : alloc.vec.Vec Std.I64)
        (hr : Aegis.AssignTasks.assign_tasks servers tasks = ok r)
        (hr2 : Aegis.AssignTasks.assign_tasks servers2 tasks = ok r2), r.val.length = m ∧ r2.val.length = m ∧
          ∀ j, j < m → r.val[j]? = r2.val[j]?) := by
    sorry

  end AegisSpec.AssignTasks
