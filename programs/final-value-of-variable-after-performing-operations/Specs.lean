import Aegis.FinalValueAfterOperations.Code.Funs

/-!
# Specifications of `Aegis.FinalValueAfterOperations.final_value_after_operations`

LeetCode problem `final-value-of-variable-after-performing-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FinalValueAfterOperations

def opIncX : List Std.U8 := [43#u8, 43#u8, 88#u8]

def opXInc : List Std.U8 := [88#u8, 43#u8, 43#u8]

def opDecX : List Std.U8 := [45#u8, 45#u8, 88#u8]

def opXDec : List Std.U8 := [88#u8, 45#u8, 45#u8]

def opBytes : List (List Std.U8) := [opIncX, opXInc, opDecX, opXDec]

def IsValidOp (op : alloc.vec.Vec Std.U8) : Prop :=
  op.val = opIncX ∨ op.val = opXInc ∨ op.val = opDecX ∨ op.val = opXDec

def IsIncOp (op : alloc.vec.Vec Std.U8) : Prop :=
  op.val = opIncX ∨ op.val = opXInc

def IsDecOp (op : alloc.vec.Vec Std.U8) : Prop :=
  op.val = opDecX ∨ op.val = opXDec

def isIncOp (op : alloc.vec.Vec Std.U8) : Bool :=
  decide (op.val = opIncX) || decide (op.val = opXInc)

def isDecOp (op : alloc.vec.Vec Std.U8) : Bool :=
  decide (op.val = opDecX) || decide (op.val = opXDec)

def AllValidOps (l : List (alloc.vec.Vec Std.U8)) : Prop :=
  ∀ (i : Nat) (hi : i < l.length), IsValidOp (l[i]'hi)

def delta (op : alloc.vec.Vec Std.U8) : Int :=
  if isIncOp op then 1 else -1

def countInc (l : List (alloc.vec.Vec Std.U8)) : Nat :=
  l.countP isIncOp

def countDec (l : List (alloc.vec.Vec Std.U8)) : Nat :=
  l.countP isDecOp

def countOf (l : List (alloc.vec.Vec Std.U8)) (s : List Std.U8) : Nat :=
  l.countP fun op => decide (op.val = s)

def flipBytes (b : List Std.U8) : List Std.U8 :=
  if b = opIncX then opDecX
  else if b = opXInc then opXDec
  else if b = opDecX then opIncX
  else if b = opXDec then opXInc
  else b

/-- The function returns a result r : I64 and r = sum_{i=0}^{n-1} d_i, where for each i, d_i = 1 if operations[i] is '++X' or 'X++', and d_i = -1 if operations[i] is '--X' or 'X--'.
  Preconditions: Let n = len(operations). The slice operations satisfies 1 <= n <= 100, and for every i with 0 <= i < n, operations[i] is exactly one of the four byte vectors: '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. -/
theorem spec_1 (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val) :
    ∃ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r ∧
      r.val = (operations.val.map delta).sum := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val), ∃ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r ∧
      r.val = (operations.val.map delta).sum) := by
  sorry

/-- The function returns a result r : I64 for every input satisfying the preconditions; it does not overflow, panic, or fail.
  Preconditions: Let n = len(operations). The slice operations satisfies 1 <= n <= 100, and for every i with 0 <= i < n, operations[i] is one of the byte vectors '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. -/
theorem spec_2 (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val) :
    ∃ r : Std.I64, Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val), ∃ r : Std.I64, Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r) := by
  sorry

/-- Whenever the function returns a result r : I64, -n <= r <= n, where n = len(operations). Equivalently, |r| <= len(operations).
  Preconditions: Let n = len(operations). The slice operations satisfies 1 <= n <= 100, and for every i with 0 <= i < n, operations[i] is one of the byte vectors '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. -/
theorem spec_3 (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val) :
    ∀ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      -((operations.val.length : Int)) ≤ r.val ∧ r.val ≤ ((operations.val.length : Int)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val), ∀ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      -((operations.val.length : Int)) ≤ r.val ∧ r.val ≤ ((operations.val.length : Int))) := by
  sorry

/-- Whenever the function returns a result r : I64, r and n have the same parity; that is, r mod 2 = n mod 2.
  Preconditions: Let n = len(operations). The slice operations satisfies 1 <= n <= 100, and for every i with 0 <= i < n, operations[i] is one of the byte vectors '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. -/
theorem spec_4 (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val) :
    ∀ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      r.val % 2 = ((operations.val.length : Int) % 2) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val), ∀ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      r.val % 2 = ((operations.val.length : Int) % 2)) := by
  sorry

/-- Let #inc be the number of indices i with 0 <= i < n such that operations[i] is '++X' or 'X++', and let #dec be the number of indices i with 0 <= i < n such that operations[i] is '--X' or 'X--'. Whenever the function returns a result r : I64, r = 0 if and only if #inc = #dec.
  Preconditions: Let n = len(operations). The slice operations satisfies 1 <= n <= 100, and for every i with 0 <= i < n, operations[i] is one of the byte vectors '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. -/
theorem spec_5 (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val) :
    ∀ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      (r.val = 0 ↔ countInc operations.val = countDec operations.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val), ∀ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      (r.val = 0 ↔ countInc operations.val = countDec operations.val)) := by
  sorry

/-- Let #inc be the number of indices i with 0 <= i < n such that operations[i] is '++X' or 'X++', and let #dec be the number of indices i with 0 <= i < n such that operations[i] is '--X' or 'X--'. Whenever the function returns a result r : I64, r > 0 if and only if #inc > #dec, and r < 0 if and only if #inc < #dec.
  Preconditions: Let n = len(operations). The slice operations satisfies 1 <= n <= 100, and for every i with 0 <= i < n, operations[i] is one of the byte vectors '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. -/
theorem spec_6 (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val) :
    ∀ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      (0 < r.val ↔ countInc operations.val > countDec operations.val) ∧
      (r.val < 0 ↔ countInc operations.val < countDec operations.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val), ∀ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      (0 < r.val ↔ countInc operations.val > countDec operations.val) ∧
      (r.val < 0 ↔ countInc operations.val < countDec operations.val)) := by
  sorry

/-- For every such k, whenever the function returns r on operations, r_p on p, and r_q on q, we have r = r_p + r_q.
  Preconditions: Let n = len(operations). The slice operations satisfies 1 <= n <= 100, and for every i with 0 <= i < n, operations[i] is one of the byte vectors '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. Also n >= 2. For every k with 0 < k < n, let p = operations[0..k] be the first k elements and q = operations[k..n] be the remaining n-k elements; p and q are nonempty valid operation lists. -/
theorem spec_7 (operations p q : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 2 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val)
    (k : Nat) (hk_low : 0 < k) (hk_high : k < operations.val.length)
    (hp : p.val = operations.val.take k) (hq : q.val = operations.val.drop k) :
    ∀ r rp rq : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      Aegis.FinalValueAfterOperations.final_value_after_operations p = ok rp →
      Aegis.FinalValueAfterOperations.final_value_after_operations q = ok rq →
      r.val = rp.val + rq.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (operations p q : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 2 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val)
    (k : Nat) (hk_low : 0 < k) (hk_high : k < operations.val.length)
    (hp : p.val = operations.val.take k) (hq : q.val = operations.val.drop k), ∀ r rp rq : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      Aegis.FinalValueAfterOperations.final_value_after_operations p = ok rp →
      Aegis.FinalValueAfterOperations.final_value_after_operations q = ok rq →
      r.val = rp.val + rq.val) := by
  sorry

/-- Whenever the function returns r on operations and r' on operations', we have r = r'.
  Preconditions: Let operations and operations' both be valid operation lists of the same length n with 1 <= n <= 100, so every element of either list is one of the byte vectors '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. For each s in {'++X','X++','--X','X--'}, the number of indices i with operations[i] = s equals the number of indices i with operations'[i] = s. -/
theorem spec_8 (operations operations' : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hlen_eq : operations'.val.length = operations.val.length)
    (hvalid : AllValidOps operations.val) (hvalid' : AllValidOps operations'.val)
    (hcounts : ∀ s : List Std.U8, s ∈ opBytes →
      countOf operations.val s = countOf operations'.val s) :
    ∀ r r' : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      Aegis.FinalValueAfterOperations.final_value_after_operations operations' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (operations operations' : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hlen_eq : operations'.val.length = operations.val.length)
    (hvalid : AllValidOps operations.val) (hvalid' : AllValidOps operations'.val)
    (hcounts : ∀ s : List Std.U8, s ∈ opBytes →
      countOf operations.val s = countOf operations'.val s), ∀ r r' : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      Aegis.FinalValueAfterOperations.final_value_after_operations operations' = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever the function returns r on operations and r' on operations', we have r' = -r.
  Preconditions: Let operations be a valid operation list: len(operations) is between 1 and 100, and every operations[i] is one of '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. Define operations' of the same length by replacing each operation by its opposite: '++X' -> '--X', 'X++' -> 'X--', '--X' -> '++X', and 'X--' -> 'X++'. Then operations' is also a valid operation list. -/
theorem spec_9 (operations operations' : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val)
    (hflip : operations'.val.map (fun op => op.val) =
      (operations.val.map (fun op => op.val)).map flipBytes) :
    ∀ r r' : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      Aegis.FinalValueAfterOperations.final_value_after_operations operations' = ok r' →
      r'.val = -r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (operations operations' : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val)
    (hflip : operations'.val.map (fun op => op.val) =
      (operations.val.map (fun op => op.val)).map flipBytes), ∀ r r' : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      Aegis.FinalValueAfterOperations.final_value_after_operations operations' = ok r' →
      r'.val = -r.val) := by
  sorry

/-- Whenever the function returns r on operations and r_i on ops_i, r = r_i + d_i, where d_i = 1 if operations[i] is '++X' or 'X++', and d_i = -1 if operations[i] is '--X' or 'X--'.
  Preconditions: Let operations be a valid operation list: n = len(operations) satisfies n >= 2 and n <= 100, and every operations[i] is one of '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. Fix an index i with 0 <= i < n. Let ops_i be the list of length n-1 obtained by deleting operations[i] and keeping the other elements in their original order; ops_i is a valid operation list. -/
theorem spec_10 (operations ops_i : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 2 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val)
    (i : Nat) (hi : i < operations.val.length)
    (hdel : ops_i.val = operations.val.eraseIdx i) :
    ∀ r ri : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      Aegis.FinalValueAfterOperations.final_value_after_operations ops_i = ok ri →
      r.val = ri.val + delta (operations.val[i]'hi) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (operations ops_i : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 2 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val)
    (i : Nat) (hi : i < operations.val.length)
    (hdel : ops_i.val = operations.val.eraseIdx i), ∀ r ri : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      Aegis.FinalValueAfterOperations.final_value_after_operations ops_i = ok ri →
      r.val = ri.val + delta (operations.val[i]'hi)) := by
  sorry

/-- Whenever the function returns r on operations and r' on operations', we have r' = r + 2.
  Preconditions: Let operations be a valid operation list: n = len(operations) satisfies n >= 1 and n <= 100, and every operations[i] is one of '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. Fix an index i with 0 <= i < n such that operations[i] is a decrement, i.e., '--X' or 'X--'. Let operations' be a valid operation list of the same length n such that operations'[i] is an increment ('++X' or 'X++') and operations'[j] = operations[j] for every j != i. -/
theorem spec_11 (operations operations' : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val)
    (i : Nat) (hi : i < operations.val.length)
    (hdec : IsDecOp (operations.val[i]'hi))
    (hi' : i < operations'.val.length)
    (hinc : IsIncOp (operations'.val[i]'hi'))
    (hlen_eq : operations'.val.length = operations.val.length)
    (hsame : ∀ (j : Nat) (hj : j < operations.val.length) (hj' : j < operations'.val.length),
      j ≠ i → operations'.val[j]'hj' = operations.val[j]'hj) :
    ∀ r r' : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      Aegis.FinalValueAfterOperations.final_value_after_operations operations' = ok r' →
      r'.val = r.val + 2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (operations operations' : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val)
    (i : Nat) (hi : i < operations.val.length)
    (hdec : IsDecOp (operations.val[i]'hi))
    (hi' : i < operations'.val.length)
    (hinc : IsIncOp (operations'.val[i]'hi'))
    (hlen_eq : operations'.val.length = operations.val.length)
    (hsame : ∀ (j : Nat) (hj : j < operations.val.length) (hj' : j < operations'.val.length),
      j ≠ i → operations'.val[j]'hj' = operations.val[j]'hj), ∀ r r' : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      Aegis.FinalValueAfterOperations.final_value_after_operations operations' = ok r' →
      r'.val = r.val + 2) := by
  sorry

/-- Whenever the function returns a result r : I64, if r > 0 then there exists an index i with 0 <= i < n such that operations[i] is '++X' or 'X++'; if r < 0 then there exists an index i with 0 <= i < n such that operations[i] is '--X' or 'X--'.
  Preconditions: Let n = len(operations). The slice operations satisfies 1 <= n <= 100, and for every i with 0 <= i < n, operations[i] is one of the byte vectors '++X' = [43,43,88], 'X++' = [88,43,43], '--X' = [45,45,88], 'X--' = [88,45,45]. -/
theorem spec_12 (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val) :
    ∀ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      (0 < r.val → ∃ (i : Nat) (hi : i < operations.val.length), IsIncOp (operations.val[i]'hi)) ∧
      (r.val < 0 → ∃ (i : Nat) (hi : i < operations.val.length), IsDecOp (operations.val[i]'hi)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8))
    (hlen_low : 1 ≤ operations.val.length) (hlen_high : operations.val.length ≤ 100)
    (hvalid : AllValidOps operations.val), ∀ r : Std.I64,
      Aegis.FinalValueAfterOperations.final_value_after_operations operations = ok r →
      (0 < r.val → ∃ (i : Nat) (hi : i < operations.val.length), IsIncOp (operations.val[i]'hi)) ∧
      (r.val < 0 → ∃ (i : Nat) (hi : i < operations.val.length), IsDecOp (operations.val[i]'hi))) := by
  sorry

end AegisSpec.FinalValueAfterOperations
