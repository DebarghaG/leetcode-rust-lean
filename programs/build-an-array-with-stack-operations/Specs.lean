import Aegis.BuildArray.Code.Funs

/-!
# Specifications of `Aegis.BuildArray.build_array`

LeetCode problem `build-an-array-with-stack-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.BuildArray

def pushBytes : List Std.U8 := [80#u8, 117#u8, 115#u8, 104#u8]

def popBytes : List Std.U8 := [80#u8, 111#u8, 112#u8]

def opsOf (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
  r.val.map (fun v => v.val)

def targetVals (target : Slice Std.I64) : List Int :=
  target.val.map (fun x => x.val)

def StrictlyIncreasing (l : List Int) : Prop :=
  ∀ (i j : Nat) (hij : i < j) (hj : j < l.length), l[i]'(by omega) < l[j]'hj

structure Machine where

  stack : List Int

  pushes : Int

  popped : List Int

def Machine.init : Machine := { stack := [], pushes := 0, popped := [] }

def step? (stream : Int) (m : Machine) (op : List Std.U8) : Option Machine :=
  if op = pushBytes then
    (if m.pushes + 1 ≤ stream then
      some { stack := m.stack ++ [m.pushes + 1], pushes := m.pushes + 1, popped := m.popped }
     else none)
  else if op = popBytes then
    match m.stack.getLast? with
    | none => none
    | some v => some { stack := m.stack.dropLast, pushes := m.pushes, popped := m.popped ++ [v] }
  else none

def exec (stream : Int) (ops : List (List Std.U8)) (m : Machine) : Option Machine :=
  ops.foldl (fun acc op => acc.bind (fun m => step? stream m op)) (some m)

def run (stream : Int) (ops : List (List Std.U8)) : Option Machine :=
  exec stream ops Machine.init

def Legal (stream : Int) (ops : List (List Std.U8)) : Prop :=
  ∃ m, run stream ops = some m

def finalStack (stream : Int) (ops : List (List Std.U8)) : Option (List Int) :=
  (run stream ops).map (fun m => m.stack)

def stackAfter (stream : Int) (ops : List (List Std.U8)) (k : Nat) : Option (List Int) :=
  finalStack stream (ops.take k)

def popCount (stream : Int) (ops : List (List Std.U8)) (v : Int) : Option Nat :=
  (run stream ops).map (fun m => (m.popped.filter (fun x => x = v)).length)

/-- The function returns a result r (it does not fail), and r is a valid answer in the following complete sense. Let PushBytes be [80,117,115,104] and PopBytes be [80,111,112]. Every entry of r is exactly PushBytes or exactly PopBytes. Execute r from an empty stack: scan entries left to right; a Push entry appends the next unused integer from the stream 1,2,...,n (the first Push appends 1, the second appends 2, and so on), and a Pop entry removes the current top element. This execution is legal: no Push attempts to append an integer greater than n, and no Pop is applied to an empty stack. After executing all entries of r, the stack from bottom to top is exactly target (same length and same elements in the same order). Finally, for every k with 0 <= k < len(r), after executing only the first k entries of r the stack is not equal to target; so target is first reached exactly at the end of r.
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_1 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target)) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.BuildArray.build_array target n = ok r ∧
      (∀ op ∈ opsOf r, op = pushBytes ∨ op = popBytes) ∧
      finalStack n.val (opsOf r) = some (targetVals target) ∧
      (∀ k, k < (opsOf r).length → stackAfter n.val (opsOf r) k ≠ some (targetVals target)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target)), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.BuildArray.build_array target n = ok r ∧
      (∀ op ∈ opsOf r, op = pushBytes ∨ op = popBytes) ∧
      finalStack n.val (opsOf r) = some (targetVals target) ∧
      (∀ k, k < (opsOf r).length → stackAfter n.val (opsOf r) k ≠ some (targetVals target))) := by
  sorry

/-- The function returns a result r; that is, there exists an r with build_array target n = Result.ok r. In particular, on every input satisfying the preconditions the function does not fail, overflow, or panic.
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_2 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target)) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), Aegis.BuildArray.build_array target n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target)), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), Aegis.BuildArray.build_array target n = ok r) := by
  sorry

/-- Whenever build_array target n returns a result r, for every j with 0 <= j < len(r), the entry r[j] is either the byte vector [80,117,115,104] (ASCII Push) or the byte vector [80,111,112] (ASCII Pop). No other bytes or lengths occur.
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_3 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    ∀ (j : Nat) (hj : j < (opsOf r).length),
      (opsOf r)[j]'hj = pushBytes ∨ (opsOf r)[j]'hj = popBytes := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), ∀ (j : Nat) (hj : j < (opsOf r).length),
      (opsOf r)[j]'hj = pushBytes ∨ (opsOf r)[j]'hj = popBytes) := by
  sorry

/-- Whenever build_array target n returns a result r, interpret entries as Push = [80,117,115,104] and Pop = [80,111,112] and execute r as described in the problem (the k-th Push appends k; Pop removes the top). Then this execution is legal: for every prefix of r, the number of Pop entries in that prefix is at most the number of Push entries in that prefix, and the total number of Push entries in r is at most n. Equivalently, no Pop is applied to an empty stack and no Push reads an integer larger than n.
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_4 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    Legal n.val (opsOf r) ∧
      (∀ k, k ≤ (opsOf r).length →
        (((opsOf r).take k).filter (fun op => op = popBytes)).length ≤
          (((opsOf r).take k).filter (fun op => op = pushBytes)).length) ∧
      (((opsOf r).filter (fun op => op = pushBytes)).length : Int) ≤ n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), Legal n.val (opsOf r) ∧
      (∀ k, k ≤ (opsOf r).length →
        (((opsOf r).take k).filter (fun op => op = popBytes)).length ≤
          (((opsOf r).take k).filter (fun op => op = pushBytes)).length) ∧
      (((opsOf r).filter (fun op => op = pushBytes)).length : Int) ≤ n.val) := by
  sorry

/-- Whenever build_array target n returns a result r, with entries interpreted as Push = [80,117,115,104] and Pop = [80,111,112] and executed legally from the empty stack (the k-th Push appends k; Pop removes the top), the final stack is exactly target: its length is len(target), and for every i with 0 <= i < len(target), the i-th element from the bottom equals target[i].
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_5 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    finalStack n.val (opsOf r) = some (targetVals target) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), finalStack n.val (opsOf r) = some (targetVals target)) := by
  sorry

/-- Whenever build_array target n returns a result r, no proper prefix of r builds target. That is, for every k with 0 <= k < len(r), if the first k entries of r are executed legally under the standard Push/Pop interpretation, the resulting stack is not equal to target. Hence target is reached for the first time only after the whole sequence r has been executed.
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_6 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    ∀ k, k < (opsOf r).length → stackAfter n.val (opsOf r) k ≠ some (targetVals target) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), ∀ k, k < (opsOf r).length → stackAfter n.val (opsOf r) k ≠ some (targetVals target)) := by
  sorry

/-- Whenever build_array target n returns a result r, r is nonempty and its last entry r[len(r)-1] is the Push byte vector [80,117,115,104].
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_7 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    opsOf r ≠ [] ∧ (opsOf r).getLast? = some pushBytes := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), opsOf r ≠ [] ∧ (opsOf r).getLast? = some pushBytes) := by
  sorry

/-- Whenever build_array target n returns a result r, the number of entries of r equal to the Push byte vector [80,117,115,104] is exactly target[len(target)-1], which is the largest element of target.
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_8 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    (((opsOf r).filter (fun op => op = pushBytes)).length : Int)
      = (target.val[target.val.length - 1]'(by omega)).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), (((opsOf r).filter (fun op => op = pushBytes)).length : Int)
      = (target.val[target.val.length - 1]'(by omega)).val) := by
  sorry

/-- Whenever build_array target n returns a result r, the number of entries of r equal to the Pop byte vector [80,111,112] is exactly target[len(target)-1] - len(target) (as a mathematical integer).
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_9 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    (((opsOf r).filter (fun op => op = popBytes)).length : Int)
      = (target.val[target.val.length - 1]'(by omega)).val - (target.val.length : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), (((opsOf r).filter (fun op => op = popBytes)).length : Int)
      = (target.val[target.val.length - 1]'(by omega)).val - (target.val.length : Int)) := by
  sorry

/-- Whenever build_array target n returns a result r, execute r legally with Push = [80,117,115,104] and Pop = [80,111,112] (the k-th Push appends k). For every integer v with 1 <= v <= target[len(target)-1], v is removed by a Pop exactly once if v is not an entry of target, and v is never removed by a Pop if v is an entry of target.
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_10 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    ∀ v : Int, 1 ≤ v → v ≤ (target.val[target.val.length - 1]'(by omega)).val →
      ((v ∈ targetVals target → popCount n.val (opsOf r) v = some 0) ∧
        (v ∉ targetVals target → popCount n.val (opsOf r) v = some 1)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), ∀ v : Int, 1 ≤ v → v ≤ (target.val[target.val.length - 1]'(by omega)).val →
      ((v ∈ targetVals target → popCount n.val (opsOf r) v = some 0) ∧
        (v ∉ targetVals target → popCount n.val (opsOf r) v = some 1))) := by
  sorry

/-- Whenever build_array target n returns a result r, execute r legally as above. For every k with 0 <= k < len(target), immediately before the unique Push operation that appends the value target[k], the stack from bottom to top is exactly [target[0], target[1], ..., target[k-1]] (the empty stack when k=0).
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_11 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    ∀ (k : Nat) (hk : k < target.val.length),
      ∃ (p : Nat) (hp : p < (opsOf r).length),
        (opsOf r)[p]'hp = pushBytes ∧
        (((((opsOf r).take p).filter (fun op => op = pushBytes)).length : Int) + 1
            = (target.val[k]'hk).val) ∧
        stackAfter n.val (opsOf r) p = some ((targetVals target).take k) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), ∀ (k : Nat) (hk : k < target.val.length),
      ∃ (p : Nat) (hp : p < (opsOf r).length),
        (opsOf r)[p]'hp = pushBytes ∧
        (((((opsOf r).take p).filter (fun op => op = pushBytes)).length : Int) + 1
            = (target.val[k]'hk).val) ∧
        stackAfter n.val (opsOf r) p = some ((targetVals target).take k)) := by
  sorry

/-- Whenever build_array target n returns a result r, execute any prefix of r legally under the Push/Pop interpretation (the k-th Push appends k). After that prefix, the stack elements from bottom to top are strictly increasing; the empty stack is vacuously strictly increasing.
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_12 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    ∀ (k : Nat), k ≤ (opsOf r).length →
      ∀ s : List Int, stackAfter n.val (opsOf r) k = some s → StrictlyIncreasing s := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), ∀ (k : Nat), k ≤ (opsOf r).length →
      ∀ s : List Int, stackAfter n.val (opsOf r) k = some s → StrictlyIncreasing s) := by
  sorry

/-- Whenever build_array target n returns a result r, the number of operations in r is exactly 2*target[len(target)-1] - len(target).
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_13 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    ((opsOf r).length : Int)
      = 2 * (target.val[target.val.length - 1]'(by omega)).val - (target.val.length : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), ((opsOf r).length : Int)
      = 2 * (target.val[target.val.length - 1]'(by omega)).val - (target.val.length : Int)) := by
  sorry

/-- Whenever build_array target n returns a result r, every Push in r appends some integer v with 1 <= v <= target[len(target)-1]. Consequently, for every integer n' with target[len(target)-1] <= n', the same r is still a legal operation sequence that first builds target against the stream 1,2,...,n'.
  Preconditions: target is a list with 1 <= len(target) <= 100; 1 <= n <= 100; for every i with 0 <= i < len(target), 1 <= target[i] <= n; and target is strictly increasing (for every i,j with 0 <= i < j < len(target), target[i] < target[j]). -/
theorem spec_14 (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r) :
    (∀ k, k ≤ (opsOf r).length →
        ((((opsOf r).take k).filter (fun op => op = pushBytes)).length : Int)
          ≤ (target.val[target.val.length - 1]'(by omega)).val) ∧
      (∀ n' : Int, (target.val[target.val.length - 1]'(by omega)).val ≤ n' →
        (∃ m : Machine, run n' (opsOf r) = some m ∧ m.stack = targetVals target) ∧
        (∀ k, k < (opsOf r).length →
          stackAfter n' (opsOf r) k ≠ some (targetVals target))) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (target : Slice Std.I64) (n : Std.I64)
    (hlen_lb : 1 ≤ target.val.length) (hlen_ub : target.val.length ≤ 100)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < target.val.length),
      1 ≤ (target.val[i]'hi).val ∧ (target.val[i]'hi).val ≤ n.val)
    (hsorted : StrictlyIncreasing (targetVals target))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (hres : Aegis.BuildArray.build_array target n = ok r), (∀ k, k ≤ (opsOf r).length →
        ((((opsOf r).take k).filter (fun op => op = pushBytes)).length : Int)
          ≤ (target.val[target.val.length - 1]'(by omega)).val) ∧
      (∀ n' : Int, (target.val[target.val.length - 1]'(by omega)).val ≤ n' →
        (∃ m : Machine, run n' (opsOf r) = some m ∧ m.stack = targetVals target) ∧
        (∀ k, k < (opsOf r).length →
          stackAfter n' (opsOf r) k ≠ some (targetVals target)))) := by
  sorry

end AegisSpec.BuildArray
