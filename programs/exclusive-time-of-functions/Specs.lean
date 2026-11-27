import Aegis.ExclusiveTime.Code.Funs

/-!
# Specifications of `Aegis.ExclusiveTime.exclusive_time`

LeetCode problem `exclusive-time-of-functions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ExclusiveTime

namespace AegisSpec.ExclusiveTime

abbrev LogEntry := Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8

abbrev Logs := Aeneas.Std.Slice LogEntry

abbrev Ans := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

structure Event where

  fid : ℕ

  isStart : Bool

  ts : ℤ
deriving DecidableEq, Repr

def isDigitB (b : Aeneas.Std.U8) : Bool := decide (48 ≤ b.val ∧ b.val ≤ 57)

def digitsVal (l : List Aeneas.Std.U8) : ℕ :=
  l.foldl (fun acc b => acc * 10 + (b.val - 48)) 0

def startWord : List Aeneas.Std.U8 := [115#u8, 116#u8, 97#u8, 114#u8, 116#u8]

def endWord : List Aeneas.Std.U8 := [101#u8, 110#u8, 100#u8]

def ParsesTo (s : List Aeneas.Std.U8) (ev : Event) : Prop :=
  ∃ fid kind ts : List Aeneas.Std.U8,
    s = fid ++ [58#u8] ++ kind ++ [58#u8] ++ ts ∧
      fid ≠ [] ∧ ts ≠ [] ∧
      (∀ b ∈ fid, isDigitB b = true) ∧
      (∀ b ∈ ts, isDigitB b = true) ∧
      (kind = startWord ∨ kind = endWord) ∧
      ev.fid = digitsVal fid ∧
      ev.isStart = (kind = startWord) ∧
      ev.ts = (digitsVal ts : ℤ)

def Decodes (logs : List LogEntry) (evs : List Event) : Prop :=
  logs.length = evs.length ∧
    ∀ (k : ℕ) (s : LogEntry), logs[k]? = some s →
      ∃ ev : Event, evs[k]? = some ev ∧ ParsesTo s.val ev

def Chronological (evs : List Event) : Prop :=
  ∀ (i j : ℕ) (ei ej : Event), evs[i]? = some ei → evs[j]? = some ej → i < j →
    ei.ts ≤ ej.ts ∧ (ei.ts = ej.ts → ej.isStart = true → ei.isStart = true)

def NoTwoSameKindSameTs (evs : List Event) : Prop :=
  ∀ (i j : ℕ) (ei ej : Event), evs[i]? = some ei → evs[j]? = some ej → i ≠ j →
    ei.isStart = ej.isStart → ei.ts ≠ ej.ts

structure Call where

  startIdx : ℕ

  endIdx : ℕ

  fid : ℕ

  startTs : ℤ

  endTs : ℤ

  parent : Option ℕ
deriving DecidableEq, Repr

def pairCallsFrom : List Event → ℕ → List Call → List Call → Option (List Call)
  | [], _, stack, done => if stack.isEmpty then some done.reverse else none
  | ev :: rest, k, stack, done =>
    if ev.isStart then
      pairCallsFrom rest (k + 1)
        ({ startIdx := k, endIdx := 0, fid := ev.fid, startTs := ev.ts, endTs := 0,
           parent := stack.head?.map (fun c => c.startIdx) } :: stack)
        done
    else
      match stack with
      | [] => none
      | top :: stack' =>
        if top.fid == ev.fid then
          pairCallsFrom rest (k + 1) stack' ({ top with endTs := ev.ts, endIdx := k } :: done)
        else none

def pairCalls (evs : List Event) : Option (List Call) := pairCallsFrom evs 0 [] []

def callsOf (evs : List Event) : List Call := (pairCalls evs).getD []

def topCallAt (calls : List Call) (t : ℤ) : Option Call :=
  match calls.filter (fun c => decide (c.startTs ≤ t ∧ t ≤ c.endTs)) with
  | [] => none
  | c :: rest =>
    some (rest.foldl (fun acc c' => if acc.startTs < c'.startTs then c' else acc) c)

def topAt (calls : List Call) (t : ℤ) : Option ℕ := (topCallAt calls t).map (fun c => c.fid)

def countUnits (lo hi : ℤ) (p : ℤ → Bool) : ℕ :=
  ((List.range (Int.toNat (hi - lo + 1))).filter (fun k => p (lo + (k : ℤ)))).length

def callsLo (calls : List Call) : ℤ :=
  calls.foldr (fun c acc => if c.startTs ≤ acc then c.startTs else acc) 0

def callsHi (calls : List Call) : ℤ :=
  calls.foldr (fun c acc => if acc ≤ c.endTs then c.endTs else acc) 0

def exclTime (evs : List Event) (i : ℕ) : ℕ :=
  countUnits (callsLo (callsOf evs)) (callsHi (callsOf evs))
    (fun t => decide (topAt (callsOf evs) t = some i))

def busyUnits (evs : List Event) : ℕ :=
  countUnits (callsLo (callsOf evs)) (callsHi (callsOf evs))
    (fun t => decide (topAt (callsOf evs) t ≠ none))

def wCount (evs : List Event) (c : Call) : ℕ :=
  countUnits c.startTs c.endTs (fun t => decide (topCallAt (callsOf evs) t = some c))

def callSpan (c : Call) : ℤ := c.endTs - c.startTs + 1

def childrenOf (calls : List Call) (c : Call) : List Call :=
  calls.filter (fun c' => decide (c'.parent = some c.startIdx))

def sumInts (l : List ℤ) : ℤ := l.foldr (fun a b => a + b) 0

def sumNats (l : List ℕ) : ℕ := l.foldr (fun a b => a + b) 0

def callContribution (calls : List Call) (c : Call) : ℤ :=
  callSpan c - sumInts ((childrenOf calls c).map callSpan)

def totalAns (r : Ans) : ℤ := sumInts (r.val.map (fun v => v.val))

def exclTimeByWitness (evs : List Event) (i : ℕ) : ℕ :=
  sumNats (((callsOf evs).filter (fun c => decide (c.fid = i))).map (wCount evs))

def spanSumOf (evs : List Event) (i : ℕ) : ℤ :=
  sumInts (((callsOf evs).filter (fun c => decide (c.fid = i))).map callSpan)

def contributionSumOf (evs : List Event) (i : ℕ) : ℤ :=
  sumInts
    (((callsOf evs).filter (fun c => decide (c.fid = i))).map (callContribution (callsOf evs)))

def topLevelOf (evs : List Event) : List Call :=
  (callsOf evs).filter (fun c => c.parent.isNone)

def topLevelSpanSum (evs : List Event) : ℤ := sumInts ((topLevelOf evs).map callSpan)

def RenamedLogs (π : ℕ → ℕ) (logs logs_pi : Logs) : Prop :=
  logs_pi.val.length = logs.val.length ∧
    ∀ (k : ℕ) (s s' : LogEntry) (ev : Event), logs.val[k]? = some s →
      logs_pi.val[k]? = some s' → ParsesTo s.val ev →
        ∃ ev' : Event,
          ParsesTo s'.val ev' ∧ ev'.fid = π ev.fid ∧ ev'.isStart = ev.isStart ∧
            ev'.ts = ev.ts

def ShiftedLogs (c : ℤ) (logs logs_c : Logs) : Prop :=
  logs_c.val.length = logs.val.length ∧
    ∀ (k : ℕ) (s s' : LogEntry) (ev : Event), logs.val[k]? = some s →
      logs_c.val[k]? = some s' → ParsesTo s.val ev →
        ∃ ev' : Event,
          ParsesTo s'.val ev' ∧ ev'.fid = ev.fid ∧ ev'.isStart = ev.isStart ∧
            ev'.ts = ev.ts + c

def Pre (n : Std.I64) (logs : Logs) (evs : List Event) : Prop :=
  (1 : ℤ) ≤ n.val ∧ n.val ≤ 100 ∧
    1 ≤ logs.val.length ∧ logs.val.length ≤ 500 ∧
    Decodes logs.val evs ∧
    (∀ ev ∈ evs, (ev.fid : ℤ) < n.val) ∧
    (∀ ev ∈ evs, 0 ≤ ev.ts ∧ ev.ts ≤ 1000000000) ∧
    Chronological evs ∧
    NoTwoSameKindSameTs evs ∧
    (pairCalls evs).isSome

/-- Whenever exclusive_time(n, logs) returns a result r, len(r) = n (n viewed as a natural number), and for every i with 0 <= i < n, r[i] = E_i, where E_i is the exclusive time of function i: the number of integer time units t for which function i is the current function (top of the call stack) during unit t when the logs are processed in order. Processing a start event at timestamp t pushes its call before unit t is counted, so that call is current for unit t; processing an end event at timestamp t counts unit t for the call being ended and then pops it; a call with start s and matching end e is active on the integer units s, s+1, ..., e inclusive, and while a nested call is active on its inclusive interval its parent is not current.
  Preconditions: n is an integer with 1 <= n <= 100 (viewed as a natural number), and logs is a list of L byte strings with 1 <= L <= 500. Each string has the format '<function_id>:<start|end>:<timestamp>' in ASCII, where <function_id> and <timestamp> are decimal numerals, 0 <= function_id < n, and 0 <= timestamp <= 1000000000. The logs are in chronological order: timestamps are nondecreasing; for equal timestamps, every 'start' event at that timestamp precedes every 'end' event at that timestamp, so a start and an end with the same timestamp can only be the start and matching end of the same call. No two start events have the same timestamp and no two end events have the same timestamp. Processing the events in this order with a stack (push on start, pop on end) is valid: no pop occurs on an empty stack, every end names the function currently on top, the stack is empty after the last log, and every start has a matching later end in the list, so calls are properly nested. -/
theorem spec_1 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r) :
    r.val.length = n.val.toNat ∧
      ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
        v.val = (exclTime evs i : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r), r.val.length = n.val.toNat ∧
      ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
        v.val = (exclTime evs i : ℤ)) := by
  sorry

/-- Whenever exclusive_time(n, logs) returns r, for every i with 0 <= i < n, 0 <= r[i] <= 1000000001.
  Preconditions: Same as spec_1. -/
theorem spec_2 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r) :
    ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      0 ≤ v.val ∧ v.val ≤ 1000000001 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r), ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      0 ≤ v.val ∧ v.val ≤ 1000000001) := by
  sorry

/-- Whenever exclusive_time(n, logs) returns r, the sum sum_{i=0}^{n-1} r[i] equals the number of integer time units t during the execution described by logs for which the call stack is nonempty; equivalently, it equals the total number of time units covered by all top-level calls (calls with no parent call).
  Preconditions: Same as spec_1. -/
theorem spec_3 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r) :
    totalAns r = (busyUnits evs : ℤ) ∧ totalAns r = topLevelSpanSum evs := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r), totalAns r = (busyUnits evs : ℤ) ∧ totalAns r = topLevelSpanSum evs) := by
  sorry

/-- Whenever exclusive_time(n, logs) returns r, for every i with 0 <= i < n, r[i] = 0 if and only if no log entry in logs has function_id i.
  Preconditions: Same as spec_1. -/
theorem spec_4 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r) :
    ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      (v.val = 0 ↔ ∀ ev ∈ evs, ev.fid ≠ i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r), ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      (v.val = 0 ↔ ∀ ev ∈ evs, ev.fid ≠ i)) := by
  sorry

/-- Whenever exclusive_time(n, logs) returns r, for every i with 0 <= i < n, r[i] is at least the number of start logs in logs whose function_id is i (that is, at least the number of calls of function i).
  Preconditions: Same as spec_1. -/
theorem spec_5 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r) :
    ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      ((evs.filter (fun ev => decide (ev.fid = i ∧ ev.isStart = true))).length : ℤ) ≤ v.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r), ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      ((evs.filter (fun ev => decide (ev.fid = i ∧ ev.isStart = true))).length : ℤ) ≤ v.val) := by
  sorry

/-- Whenever exclusive_time(n, logs) returns r, for every i with 0 <= i < n, r[i] is at most the sum over all calls c of function i of (e(c) - s(c) + 1), where s(c) and e(c) are the start and matching end timestamps of that call.
  Preconditions: Same as spec_1. -/
theorem spec_6 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r) :
    ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      v.val ≤ spanSumOf evs i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r), ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      v.val ≤ spanSumOf evs i) := by
  sorry

/-- If every log entry in logs has the same function_id f, then whenever exclusive_time(n, logs) returns r, r[f] equals the sum over all top-level calls of f of (e(c) - s(c) + 1), and r[j] = 0 for every j with 0 <= j < n and j != f.
  Preconditions: Same as spec_1. -/
theorem spec_7 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (f : ℕ) (hf : ∀ ev ∈ evs, ev.fid = f)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r) :
    ∀ (j : ℕ), j < n.val.toNat → ∀ v : Std.I64, r.val[j]? = some v →
      (j = f → v.val = topLevelSpanSum evs) ∧ (j ≠ f → v.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (f : ℕ) (hf : ∀ ev ∈ evs, ev.fid = f)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r), ∀ (j : ℕ), j < n.val.toNat → ∀ v : Std.I64, r.val[j]? = some v →
      (j = f → v.val = topLevelSpanSum evs) ∧ (j ≠ f → v.val = 0)) := by
  sorry

/-- If the call stack never contains more than one call at a time (equivalently, every start is matched by an end before any other start occurs), then whenever exclusive_time(n, logs) returns r, for every i with 0 <= i < n, r[i] equals the sum over all calls of function i of (e(c) - s(c) + 1), where s(c) and e(c) are the call's start and matching end timestamps.
  Preconditions: Same as spec_1. -/
theorem spec_8 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (hstack : ∀ c ∈ callsOf evs, c.parent.isNone = true)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r) :
    ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      v.val = spanSumOf evs i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (hstack : ∀ c ∈ callsOf evs, c.parent.isNone = true)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r), ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      v.val = spanSumOf evs i) := by
  sorry

/-- For every permutation pi of {0,...,n-1}, let logs_pi be obtained from logs by replacing the function_id x in every log entry by pi(x). Whenever exclusive_time(n, logs) returns r and exclusive_time(n, logs_pi) returns r_pi, for every i with 0 <= i < n, r_pi[pi(i)] = r[i].
  Preconditions: Same as spec_1. -/
theorem spec_9 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (π : ℕ → ℕ) (hπ : ∀ i, i < n.val.toNat → π i < n.val.toNat)
    (hπinj : ∀ i j, i < n.val.toNat → j < n.val.toNat → π i = π j → i = j)
    (logs_pi : Logs) (evs_pi : List Event) (hdec : Decodes logs_pi.val evs_pi)
    (hren : RenamedLogs π logs logs_pi)
    (r r_pi : Ans)
    (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r)
    (hr_pi : Aegis.ExclusiveTime.exclusive_time n logs_pi = ok r_pi) :
    ∀ (i : ℕ), i < n.val.toNat → ∀ v v' : Std.I64,
      r.val[i]? = some v → r_pi.val[π i]? = some v' → v'.val = v.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (π : ℕ → ℕ) (hπ : ∀ i, i < n.val.toNat → π i < n.val.toNat)
    (hπinj : ∀ i j, i < n.val.toNat → j < n.val.toNat → π i = π j → i = j)
    (logs_pi : Logs) (evs_pi : List Event) (hdec : Decodes logs_pi.val evs_pi)
    (hren : RenamedLogs π logs logs_pi)
    (r r_pi : Ans)
    (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r)
    (hr_pi : Aegis.ExclusiveTime.exclusive_time n logs_pi = ok r_pi), ∀ (i : ℕ), i < n.val.toNat → ∀ v v' : Std.I64,
      r.val[i]? = some v → r_pi.val[π i]? = some v' → v'.val = v.val) := by
  sorry

/-- For every integer c such that adding c to every timestamp in logs leaves all timestamps in [0, 1000000000], let logs_c be the resulting log list. Whenever exclusive_time(n, logs) returns r and exclusive_time(n, logs_c) returns r_c, for every i with 0 <= i < n, r_c[i] = r[i].
  Preconditions: Same as spec_1. -/
theorem spec_10 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (c : ℤ) (logs_c : Logs) (evs_c : List Event) (hdec : Decodes logs_c.val evs_c)
    (hshift : ShiftedLogs c logs logs_c)
    (hrange : ∀ ev ∈ evs, 0 ≤ ev.ts + c ∧ ev.ts + c ≤ 1000000000)
    (r r_c : Ans)
    (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r)
    (hr_c : Aegis.ExclusiveTime.exclusive_time n logs_c = ok r_c) :
    ∀ (i : ℕ), i < n.val.toNat → ∀ v v' : Std.I64,
      r.val[i]? = some v → r_c.val[i]? = some v' → v'.val = v.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (c : ℤ) (logs_c : Logs) (evs_c : List Event) (hdec : Decodes logs_c.val evs_c)
    (hshift : ShiftedLogs c logs logs_c)
    (hrange : ∀ ev ∈ evs, 0 ≤ ev.ts + c ∧ ev.ts + c ≤ 1000000000)
    (r r_c : Ans)
    (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r)
    (hr_c : Aegis.ExclusiveTime.exclusive_time n logs_c = ok r_c), ∀ (i : ℕ), i < n.val.toNat → ∀ v v' : Std.I64,
      r.val[i]? = some v → r_c.val[i]? = some v' → v'.val = v.val) := by
  sorry

/-- Whenever the preconditions hold, exclusive_time(n, logs) returns a result r; in particular it does not fail, panic, or overflow.
  Preconditions: Same as spec_1. -/
theorem spec_11 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs) :
    ∃ r : Ans, Aegis.ExclusiveTime.exclusive_time n logs = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs), ∃ r : Ans, Aegis.ExclusiveTime.exclusive_time n logs = ok r) := by
  sorry

/-- Whenever exclusive_time(n, logs) returns r, for every function i let C_i be the set of calls of i (start logs for i paired with their matching end logs by the stack). For each c in C_i let s(c) and e(c) be its start and end timestamps, and let w(c) be the number of integer timestamps t with s(c) <= t <= e(c) at which the currently executing call (the call object on top of the stack) is c. Then r[i] = sum_{c in C_i} w(c), and for every c in C_i, 1 <= w(c) <= e(c) - s(c) + 1.
  Preconditions: Same as spec_1. -/
theorem spec_12 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r) :
    (∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
        v.val = (exclTimeByWitness evs i : ℤ)) ∧
      (∀ (i : ℕ), i < n.val.toNat → ∀ c : Call, c ∈ callsOf evs → c.fid = i →
        1 ≤ wCount evs c ∧ wCount evs c ≤ (callSpan c).toNat) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r), (∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
        v.val = (exclTimeByWitness evs i : ℤ)) ∧
      (∀ (i : ℕ), i < n.val.toNat → ∀ c : Call, c ∈ callsOf evs → c.fid = i →
        1 ≤ wCount evs c ∧ wCount evs c ≤ (callSpan c).toNat)) := by
  sorry

/-- Whenever exclusive_time(n, logs) returns r, if min_t and max_t are respectively the minimum and maximum timestamps appearing in logs, then for every i with 0 <= i < n, r[i] <= max_t - min_t + 1.
  Preconditions: Same as spec_1. -/
theorem spec_13 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (mn mx : ℤ) (hmin : ∀ ev ∈ evs, mn ≤ ev.ts) (hmin' : ∃ ev ∈ evs, ev.ts = mn)
    (hmax : ∀ ev ∈ evs, ev.ts ≤ mx) (hmax' : ∃ ev ∈ evs, ev.ts = mx)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r) :
    ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      v.val ≤ mx - mn + 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (mn mx : ℤ) (hmin : ∀ ev ∈ evs, mn ≤ ev.ts) (hmin' : ∃ ev ∈ evs, ev.ts = mn)
    (hmax : ∀ ev ∈ evs, ev.ts ≤ mx) (hmax' : ∃ ev ∈ evs, ev.ts = mx)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r), ∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
      v.val ≤ mx - mn + 1) := by
  sorry

/-- Whenever exclusive_time(n, logs) returns r, for every call c of a function i with start s(c), matching end e(c), and immediate child calls c_1,...,c_k (the calls whose start logs lie between c's start and end and whose parent call is c), the exclusive contribution of c is (e(c)-s(c)+1) - sum_{j=1}^k (e(c_j)-s(c_j)+1); consequently r[i] is the sum of these contributions over all calls c of i.
  Preconditions: Same as spec_1. -/
theorem spec_14 (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r) :
    (∀ c : Call, c ∈ callsOf evs →
        (wCount evs c : ℤ) = callContribution (callsOf evs) c) ∧
      (∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
        v.val = contributionSumOf evs i) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (logs : Logs) (evs : List Event) (hpre : Pre n logs evs)
    (r : Ans) (hr : Aegis.ExclusiveTime.exclusive_time n logs = ok r), (∀ c : Call, c ∈ callsOf evs →
        (wCount evs c : ℤ) = callContribution (callsOf evs) c) ∧
      (∀ (i : ℕ), i < n.val.toNat → ∀ v : Std.I64, r.val[i]? = some v →
        v.val = contributionSumOf evs i)) := by
  sorry

end AegisSpec.ExclusiveTime
