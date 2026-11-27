import Aegis.GetOrder.Code.Funs

/-!
# Specifications of `Aegis.GetOrder.get_order`

LeetCode problem `single-threaded-cpu`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetOrder

abbrev TaskArray : Type := Aeneas.Std.Slice (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

abbrev OrderVec : Type := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

def listEntry (l : List Aeneas.Std.I64) (k : Nat) : Int :=
  match l[k]? with
  | some x => x.val
  | none => 0

def row (tasks : TaskArray) (i : Nat) : List Aeneas.Std.I64 :=
  match tasks.val[i]? with
  | some v => v.val
  | none => []

def enqTime (tasks : TaskArray) (i : Nat) : Int := listEntry (row tasks i) 0

def procTime (tasks : TaskArray) (i : Nat) : Int := listEntry (row tasks i) 1

def numTasks (tasks : TaskArray) : Nat := tasks.val.length

def outEntry (r : OrderVec) (k : Nat) : Int := listEntry r.val k

def outLabel (r : OrderVec) (k : Nat) : Nat := (outEntry r k).toNat

def keyLt (tasks : TaskArray) (i j : Nat) : Bool :=
  if procTime tasks i < procTime tasks j then true
  else if procTime tasks j < procTime tasks i then false
  else decide (i < j)

def pickBest (tasks : TaskArray) (cands : List Nat) : Nat :=
  match cands with
  | [] => 0
  | c :: cs => cs.foldl (fun best i => if keyLt tasks i best then i else best) c

def minEnqOf (tasks : TaskArray) (labels : List Nat) : Int :=
  match labels with
  | [] => 0
  | i :: is => is.foldl (fun acc j => min acc (enqTime tasks j)) (enqTime tasks i)

def minEnqTime (tasks : TaskArray) : Int :=
  minEnqOf tasks (List.range (numTasks tasks))

def IsMinEnq (tasks : TaskArray) (m : Int) : Prop :=
  (∀ i, i < numTasks tasks → m ≤ enqTime tasks i) ∧
    ∃ i, i < numTasks tasks ∧ enqTime tasks i = m

def IsPerm (tasks : TaskArray) (r : OrderVec) : Prop :=
  List.Perm ((List.range (numTasks tasks)).map (fun i => (i : Int))) (r.val.map (fun x => x.val))

def OccursBefore (r : OrderVec) (i j : Nat) : Prop :=
  ∃ u v, u < v ∧ v < r.val.length ∧ outLabel r u = i ∧ outLabel r v = j

def Remaining (tasks : TaskArray) (r : OrderVec) (k i : Nat) : Prop :=
  i < numTasks tasks ∧ ∀ k', k' < k → outLabel r k' ≠ i

structure GreedyState where

  time : Int

  done : List Nat

  todo : List Nat

def greedyInit (tasks : TaskArray) : GreedyState :=
  { time := 0, done := [], todo := List.range (numTasks tasks) }

def greedyStep (tasks : TaskArray) (st : GreedyState) : Int × Nat × GreedyState :=
  let avail : List Nat := st.todo.filter (fun i => decide (enqTime tasks i ≤ st.time))
  let a : Int := if avail.isEmpty then minEnqOf tasks st.todo else st.time
  let cands : List Nat := st.todo.filter (fun i => decide (enqTime tasks i ≤ a))
  let chosen : Nat := pickBest tasks cands
  (a, chosen,
    { time := a + procTime tasks chosen
      done := st.done ++ [chosen]
      todo := st.todo.filter (fun i => decide (i ≠ chosen)) })

def greedyState (tasks : TaskArray) : Nat → GreedyState
  | 0 => greedyInit tasks
  | k + 1 => (greedyStep tasks (greedyState tasks k)).2.2

def greedyTime (tasks : TaskArray) (k : Nat) : Int := (greedyState tasks k).time

def greedyStart (tasks : TaskArray) (k : Nat) : Int := (greedyStep tasks (greedyState tasks k)).1

def greedyOrder (tasks : TaskArray) (k : Nat) : Nat := (greedyStep tasks (greedyState tasks k)).2.1

def startTime (tasks : TaskArray) (r : OrderVec) : Nat → Int
  | 0 => minEnqTime tasks
  | k + 1 =>
    max (startTime tasks r k + procTime tasks (outLabel r k))
      (enqTime tasks (outLabel r (k + 1)))

def finishTime (tasks : TaskArray) (r : OrderVec) (k : Nat) : Int :=
  startTime tasks r k + procTime tasks (outLabel r k)

/-- Let r be the returned vector. Define a sequence o and times t_k as follows. Set t_0 = 0. For k = 0,1,...,n-1, let R_k be the set of labels i with 0 <= i < n that do not occur among o[0],...,o[k-1]. Let a_k = t_k if there exists i in R_k with e_i <= t_k; otherwise let a_k = min_{i in R_k} e_i. Let o[k] be the unique i in R_k with e_i <= a_k such that for every j in R_k with e_j <= a_k, either p_i < p_j, or p_i = p_j and i <= j. Set t_{k+1} = a_k + p_{o[k]}. Then len(r) = n and r[k] = o[k] for every k with 0 <= k < n. Thus r is exactly the order in which the CPU processes the tasks, including idle jumps to the next enqueue time when no remaining task is available.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_1 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∃ r : OrderVec,
      Aegis.GetOrder.get_order tasks = ok r ∧
        r.val.length = numTasks tasks ∧
          ∀ k, k < numTasks tasks → outLabel r k = greedyOrder tasks k := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∃ r : OrderVec,
      Aegis.GetOrder.get_order tasks = ok r ∧
        r.val.length = numTasks tasks ∧
          ∀ k, k < numTasks tasks → outLabel r k = greedyOrder tasks k) := by
  sorry

/-- The function returns a result r and does not fail: no panic, no out-of-bounds access, and no arithmetic overflow occurs.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_2 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∃ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∃ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = n.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_3 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r → r.val.length = numTasks tasks := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r → r.val.length = numTasks tasks) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(r), 0 <= r[k] < n.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_4 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r →
      ∀ k, k < r.val.length → 0 ≤ outEntry r k ∧ outEntry r k < (numTasks tasks : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r →
      ∀ k, k < r.val.length → 0 ≤ outEntry r k ∧ outEntry r k < (numTasks tasks : Int)) := by
  sorry

/-- Whenever the function returns a result r, the entries of r are pairwise distinct: for all k,l with 0 <= k < len(r) and 0 <= l < len(r), if r[k] = r[l], then k = l.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_5 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r →
      ∀ k l, k < r.val.length → l < r.val.length → outLabel r k = outLabel r l → k = l := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r →
      ∀ k l, k < r.val.length → l < r.val.length → outLabel r k = outLabel r l → k = l) := by
  sorry

/-- Whenever the function returns a result r, every label from 0 to n-1 occurs in r: for every i with 0 <= i < n, there exists k with 0 <= k < len(r) and r[k] = i.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_6 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r →
      ∀ i, i < numTasks tasks → ∃ k, k < r.val.length ∧ outLabel r k = i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r →
      ∀ i, i < numTasks tasks → ∃ k, k < r.val.length ∧ outLabel r k = i) := by
  sorry

/-- Whenever the function returns a result r that is a permutation of 0..n-1, define s_0 = min_{0<=i<n} e_i and, for 0 <= k < n-1, s_{k+1} = max(s_k + p_{r[k]}, e_{r[k+1]}). Then for every k with 0 <= k < n, s_k >= e_{r[k]}. In particular, s_0 = e_{r[0]} = min_i e_i, so the first processed task has the minimum enqueue time.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_7 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r → IsPerm tasks r →
      (∀ k, k < numTasks tasks → enqTime tasks (outLabel r k) ≤ startTime tasks r k) ∧
        startTime tasks r 0 = enqTime tasks (outLabel r 0) ∧
          IsMinEnq tasks (startTime tasks r 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r → IsPerm tasks r →
      (∀ k, k < numTasks tasks → enqTime tasks (outLabel r k) ≤ startTime tasks r k) ∧
        startTime tasks r 0 = enqTime tasks (outLabel r 0) ∧
          IsMinEnq tasks (startTime tasks r 0)) := by
  sorry

/-- Whenever the function returns a result r that is a permutation of 0..n-1, define s_0 = min_i e_i and s_{k+1} = max(s_k + p_{r[k]}, e_{r[k+1]}) for 0 <= k < n-1. For 0 <= k <= n let R_k = {i | 0 <= i < n and i does not occur among r[0],...,r[k-1]}. Then for every k with 0 <= k < n, r[k] is in R_k, e_{r[k]} <= s_k, and for every j in R_k with e_j <= s_k, either p_{r[k]} < p_j, or p_{r[k]} = p_j and r[k] <= j.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_8 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r → IsPerm tasks r →
      ∀ k, k < numTasks tasks →
        Remaining tasks r k (outLabel r k) ∧
          enqTime tasks (outLabel r k) ≤ startTime tasks r k ∧
            ∀ j, Remaining tasks r k j → enqTime tasks j ≤ startTime tasks r k →
              procTime tasks (outLabel r k) < procTime tasks j ∨
                (procTime tasks (outLabel r k) = procTime tasks j ∧ outLabel r k ≤ j) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r → IsPerm tasks r →
      ∀ k, k < numTasks tasks →
        Remaining tasks r k (outLabel r k) ∧
          enqTime tasks (outLabel r k) ≤ startTime tasks r k ∧
            ∀ j, Remaining tasks r k j → enqTime tasks j ≤ startTime tasks r k →
              procTime tasks (outLabel r k) < procTime tasks j ∨
                (procTime tasks (outLabel r k) = procTime tasks j ∧ outLabel r k ≤ j)) := by
  sorry

/-- Whenever the function returns a result r that is a permutation of 0..n-1, define s_0 = min_i e_i, f_k = s_k + p_{r[k]}, and s_{k+1} = max(f_k, e_{r[k+1]}) for 0 <= k < n-1. For 0 <= k < n let R_{k+1} = {i | 0 <= i < n and i does not occur among r[0],...,r[k]}. Then for every k with 0 <= k < n-1: if there exists j in R_{k+1} with e_j <= f_k, then s_{k+1} = f_k; if no j in R_{k+1} has e_j <= f_k, then s_{k+1} = e_{r[k+1]} and e_{r[k+1]} > f_k.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_9 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r → IsPerm tasks r →
      ∀ k, k + 1 < numTasks tasks →
        ((∃ j, Remaining tasks r (k + 1) j ∧ enqTime tasks j ≤ finishTime tasks r k) →
            startTime tasks r (k + 1) = finishTime tasks r k) ∧
          ((¬∃ j, Remaining tasks r (k + 1) j ∧ enqTime tasks j ≤ finishTime tasks r k) →
            startTime tasks r (k + 1) = enqTime tasks (outLabel r (k + 1)) ∧
              finishTime tasks r k < enqTime tasks (outLabel r (k + 1))) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r → IsPerm tasks r →
      ∀ k, k + 1 < numTasks tasks →
        ((∃ j, Remaining tasks r (k + 1) j ∧ enqTime tasks j ≤ finishTime tasks r k) →
            startTime tasks r (k + 1) = finishTime tasks r k) ∧
          ((¬∃ j, Remaining tasks r (k + 1) j ∧ enqTime tasks j ≤ finishTime tasks r k) →
            startTime tasks r (k + 1) = enqTime tasks (outLabel r (k + 1)) ∧
              finishTime tasks r k < enqTime tasks (outLabel r (k + 1)))) := by
  sorry

/-- Whenever the function returns a result r, for any two distinct labels i,j with 0 <= i,j < n, if e_i <= e_j and (p_i < p_j or (p_i = p_j and i < j)), then i occurs before j in r: there exist u,v with 0 <= u < v < len(r), r[u] = i, and r[v] = j.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_10 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r →
      ∀ i j, i < numTasks tasks → j < numTasks tasks → i ≠ j →
        enqTime tasks i ≤ enqTime tasks j →
          (procTime tasks i < procTime tasks j ∨
              (procTime tasks i = procTime tasks j ∧ i < j)) →
            OccursBefore r i j := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r →
      ∀ i j, i < numTasks tasks → j < numTasks tasks → i ≠ j →
        enqTime tasks i ≤ enqTime tasks j →
          (procTime tasks i < procTime tasks j ∨
              (procTime tasks i = procTime tasks j ∧ i < j)) →
            OccursBefore r i j) := by
  sorry

/-- Whenever the function returns a result r, for any two distinct labels i,j with 0 <= i,j < n, if i occurs before j in r and e_i > e_j, then p_i < p_j or (p_i = p_j and i < j).
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_11 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r →
      ∀ i j, i < numTasks tasks → j < numTasks tasks → i ≠ j →
        OccursBefore r i j → enqTime tasks i > enqTime tasks j →
          procTime tasks i < procTime tasks j ∨
            (procTime tasks i = procTime tasks j ∧ i < j) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r →
      ∀ i j, i < numTasks tasks → j < numTasks tasks → i ≠ j →
        OccursBefore r i j → enqTime tasks i > enqTime tasks j →
          procTime tasks i < procTime tasks j ∨
            (procTime tasks i = procTime tasks j ∧ i < j)) := by
  sorry

/-- Whenever the function returns a result r that is a permutation of 0..n-1, define s_0 = min_i e_i and s_{k+1} = max(s_k + p_{r[k]}, e_{r[k+1]}) for 0 <= k < n-1. For any two distinct labels i,j with 0 <= i,j < n, if e_i > e_j and (p_i < p_j or (p_i = p_j and i < j)), and if j occurs before i in r, then the start time of j is strictly less than e_i: if r[v] = j, then s_v < e_i.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_12 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000) :
    ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r → IsPerm tasks r →
      ∀ i j, i < numTasks tasks → j < numTasks tasks → i ≠ j →
        enqTime tasks i > enqTime tasks j →
          (procTime tasks i < procTime tasks j ∨
              (procTime tasks i = procTime tasks j ∧ i < j)) →
            OccursBefore r j i →
              ∀ v, v < r.val.length → outLabel r v = j → startTime tasks r v < enqTime tasks i := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000), ∀ r : OrderVec, Aegis.GetOrder.get_order tasks = ok r → IsPerm tasks r →
      ∀ i j, i < numTasks tasks → j < numTasks tasks → i ≠ j →
        enqTime tasks i > enqTime tasks j →
          (procTime tasks i < procTime tasks j ∨
              (procTime tasks i = procTime tasks j ∧ i < j)) →
            OccursBefore r j i →
              ∀ v, v < r.val.length → outLabel r v = j → startTime tasks r v < enqTime tasks i) := by
  sorry

/-- The function returns r with r[k] = k for every k with 0 <= k < n; that is, r = [0,1,...,n-1].
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. Additionally assume e_0 <= e_1 <= ... <= e_{n-1} and p_0 <= p_1 <= ... <= p_{n-1}. -/
theorem spec_13 (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000)
    (he : ∀ i j, i < j → j < numTasks tasks → enqTime tasks i ≤ enqTime tasks j)
    (hp : ∀ i j, i < j → j < numTasks tasks → procTime tasks i ≤ procTime tasks j) :
    ∃ r : OrderVec,
      Aegis.GetOrder.get_order tasks = ok r ∧
        ∀ k, k < numTasks tasks → outLabel r k = k := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (tasks : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000)
    (he : ∀ i j, i < j → j < numTasks tasks → enqTime tasks i ≤ enqTime tasks j)
    (hp : ∀ i j, i < j → j < numTasks tasks → procTime tasks i ≤ procTime tasks j), ∃ r : OrderVec,
      Aegis.GetOrder.get_order tasks = ok r ∧
        ∀ k, k < numTasks tasks → outLabel r k = k) := by
  sorry

/-- Let tasks' be the input array with tasks'[i][0] = e_i + c and tasks'[i][1] = p_i for all i. Then get_order(tasks') = get_order(tasks): adding the same constant c to every enqueue time leaves the returned processing order unchanged.
  Preconditions: Let n = len(tasks). For every i with 0 <= i < n, len(tasks[i]) = 2; write e_i = tasks[i][0] and p_i = tasks[i][1]. Assume 1 <= n <= 100000 and 1 <= e_i, p_i <= 1000000000 for every i with 0 <= i < n. Let c be an integer with c >= 0 and (max_{0<=i<n} e_i) + c <= 1000000000. -/
theorem spec_14 (tasks tasks' : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000)
    (c : Int) (hc : 0 ≤ c)
    (hcMax : ∀ i, i < numTasks tasks → enqTime tasks i + c ≤ 1000000000)
    (hcard : numTasks tasks' = numTasks tasks)
    (hrow' : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks'.val[i]? = some v ∧ v.val.length = 2)
    (henq : ∀ i, i < numTasks tasks → enqTime tasks' i = enqTime tasks i + c)
    (hprc : ∀ i, i < numTasks tasks → procTime tasks' i = procTime tasks i) :
    Aegis.GetOrder.get_order tasks' = Aegis.GetOrder.get_order tasks := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (tasks tasks' : TaskArray)
    (hn1 : 1 ≤ numTasks tasks) (hn2 : numTasks tasks ≤ 100000)
    (hrow : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks.val[i]? = some v ∧ v.val.length = 2)
    (hb : ∀ i, i < numTasks tasks →
      1 ≤ enqTime tasks i ∧ enqTime tasks i ≤ 1000000000 ∧
        1 ≤ procTime tasks i ∧ procTime tasks i ≤ 1000000000)
    (c : Int) (hc : 0 ≤ c)
    (hcMax : ∀ i, i < numTasks tasks → enqTime tasks i + c ≤ 1000000000)
    (hcard : numTasks tasks' = numTasks tasks)
    (hrow' : ∀ i, i < numTasks tasks →
      ∃ v : OrderVec, tasks'.val[i]? = some v ∧ v.val.length = 2)
    (henq : ∀ i, i < numTasks tasks → enqTime tasks' i = enqTime tasks i + c)
    (hprc : ∀ i, i < numTasks tasks → procTime tasks' i = procTime tasks i), Aegis.GetOrder.get_order tasks' = Aegis.GetOrder.get_order tasks) := by
  sorry

end AegisSpec.GetOrder
