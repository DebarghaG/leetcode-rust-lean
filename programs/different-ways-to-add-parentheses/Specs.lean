import Aegis.DiffWaysToCompute.Code.Funs

/-!
# Specifications of `Aegis.DiffWaysToCompute.diff_ways_to_compute`

LeetCode problem `different-ways-to-add-parentheses`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DiffWaysToCompute

abbrev Byte := Std.U8

def isDigit (c : Byte) : Prop := 48 ≤ c.val ∧ c.val ≤ 57

instance instDecidableIsDigit (c : Byte) : Decidable (isDigit c) := by
  unfold isDigit; infer_instance

def isOp (c : Byte) : Prop := c.val = 43 ∨ c.val = 45 ∨ c.val = 42

instance instDecidableIsOp (c : Byte) : Decidable (isOp c) := by
  unfold isOp; infer_instance

def digitVal (run : List Byte) : Int :=
  run.foldl (fun acc c => acc * 10 + ((c.val : Int) - 48)) 0

def applyOp (op : Byte) (a b : Int) : Int :=
  if op.val = 43 then a + b else if op.val = 45 then a - b else a * b

def tokenizeAux (run : List Byte) (ns : List Int) (os : List Byte) :
    List Byte → Option (List Int × List Byte)
  | [] =>
    if run.isEmpty then none else some (ns ++ [digitVal run.reverse], os)
  | c :: cs =>
    if isDigit c then
      tokenizeAux (c :: run) ns os cs
    else if isOp c then
      if run.isEmpty then none
      else tokenizeAux [] (ns ++ [digitVal run.reverse]) (os ++ [c]) cs
    else none

def tokenize (s : List Byte) : Option (List Int × List Byte) := tokenizeAux [] [] [] s

def IsValid (s : List Byte) (ns : List Int) (os : List Byte) : Prop :=
  tokenize s = some (ns, os) ∧
  1 ≤ s.length ∧ s.length ≤ 20 ∧
  ns ≠ [] ∧ os.length + 1 = ns.length ∧
  ∀ v ∈ ns, 0 ≤ v ∧ v ≤ 99

def IsValidExpr (s : List Byte) : Prop := ∃ ns os, IsValid s ns os

def digitRunsAux (run : List Byte) (out : List (List Byte)) :
    List Byte → List (List Byte)
  | [] => if run.isEmpty then out.reverse else (run.reverse :: out).reverse
  | c :: cs =>
    if isDigit c then digitRunsAux (c :: run) out cs
    else if run.isEmpty then digitRunsAux [] out cs
    else digitRunsAux [] (run.reverse :: out) cs

def digitRuns (s : List Byte) : List (List Byte) := digitRunsAux [] [] s

def vecInts (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

def count (l : List Int) (v : Int) : Nat := (l.filter (fun x => x = v)).length

def SubMultiset (l₁ l₂ : List Int) : Prop := ∀ v : Int, count l₁ v ≤ count l₂ v

inductive FullParen where

  | leaf (v : Int)

  | node (l r : FullParen) (op : Byte)

inductive IsFullParen : FullParen → List Int → List Byte → Prop where
  | leaf (v : Int) : IsFullParen (.leaf v) [v] []
  | node {tl tr : FullParen} {nL nR : List Int} {oL oR : List Byte} (op : Byte) :
      IsFullParen tl nL oL → IsFullParen tr nR oR →
      IsFullParen (.node tl tr op) (nL ++ nR) (oL ++ op :: oR)

namespace FullParen

def value : FullParen → Int
  | leaf v => v
  | node l r op => applyOp op l.value r.value

end FullParen

def valuesOfAux : Nat → List Int → List Byte → List Int
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | _ + 1, [v], _ => [v]
  | fuel + 1, v₀ :: v₁ :: rest, ops =>
    (List.range (rest.length + 1)).flatMap (fun k =>
      let ns := v₀ :: v₁ :: rest
      (valuesOfAux fuel (ns.take (k + 1)) (ops.take k)).flatMap (fun lv =>
        (valuesOfAux fuel (ns.drop (k + 1)) (ops.drop (k + 1))).map (fun rv =>
          applyOp (ops.getD k default) lv rv)))

def valuesOf (ns : List Int) (os : List Byte) : List Int := valuesOfAux ns.length ns os

def splitValues (ns : List Int) (os : List Byte) (j : Nat) : List Int :=
  (valuesOf (ns.take j) (os.take (j - 1))).flatMap (fun lv =>
    (valuesOf (ns.drop j) (os.drop j)).map (fun rv =>
      applyOp (os.getD (j - 1) default) lv rv))

def leftAssoc (ns : List Int) (os : List Byte) : Int :=
  match ns with
  | [] => 0
  | v :: vs => (vs.zip os).foldl (fun acc q => applyOp q.2 acc q.1) v

def prodInts (ns : List Int) : Int := ns.foldr (fun a b => a * b) 1

def sumInts (ns : List Int) : Int := ns.foldr (fun a b => a + b) 0

def catalanList : Nat → List Nat
  | 0 => [1]
  | k + 1 =>
    catalanList k ++
      [ (List.range (k + 1)).foldl
          (fun acc j =>
            acc + (catalanList k).getD j 0 * (catalanList k).getD (k - j) 0) 0 ]

def catalan (n : Nat) : Nat := (catalanList n).getD n 0

/-- Let N_0,...,N_n be the number tokens (the maximal digit runs) in order and O_1,...,O_n the operator tokens in order, so n is the number of operators. A full parenthesization is any binary tree with leaves N_0,...,N_n in this left-to-right order and internal nodes O_1,...,O_n in this left-to-right order; equivalently, any insertion of n pairs of parentheses that fully parenthesizes the original expression without changing the order of numbers or operators. Let V be the multiset of values of all full parenthesizations, where value(T) is computed recursively by applying the operator at each internal node to the values of its left and right subtrees using ordinary integer +, -, *; V has one entry per full parenthesization, so equal values from different parenthesizations are separate entries. The function returns a result r and the multiset of entries of r is exactly V: for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of full parenthesizations T with value(T) = v. The order of the entries of r is arbitrary.
  Preconditions: Let expression be a byte slice satisfying the problem constraints: 1 <= len(expression) <= 20; every byte is an ASCII digit ('0'..'9') or one of '+', '-', '*'; reading left to right, expression is a nonempty alternating sequence of maximal nonempty digit runs and single operator bytes, beginning and ending with a digit run; each digit run's decimal value (leading zeros allowed) is in [0,99]. -/
theorem spec_1 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      ∀ v : Int, count (vecInts r) v = count (valuesOf ns os) v := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      ∀ v : Int, count (vecInts r) v = count (valuesOf ns os) v) := by
  sorry

/-- Let n be the number of operator tokens. The function returns r and len(r) = C_n, where C_0 = 1 and C_n = sum_{j=0}^{n-1} C_j * C_{n-1-j} for n >= 1. Equivalently, len(r) equals the number of full parenthesizations of expression.
  Preconditions: Let expression be a valid expression under the problem constraints (length 1..20, alternating maximal digit runs of value 0..99 and single '+','-','*' bytes, starting and ending with a digit run). -/
theorem spec_2 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length = catalan os.length ∧
      r.val.length = (valuesOf ns os).length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length = catalan os.length ∧
      r.val.length = (valuesOf ns os).length) := by
  sorry

/-- The function returns a result r; it does not fail with overflow, out-of-bounds access, or panic.
  Preconditions: Let expression be a valid expression under the problem constraints (length 1..20, alternating maximal digit runs of value 0..99 and single '+','-','*' bytes, starting and ending with a digit run). -/
theorem spec_3 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r) := by
  sorry

/-- The function returns r and len(r) = 1 and r[0] equals the decimal value of that single digit run (which is in [0,99]).
  Preconditions: Let expression be a valid expression under the problem constraints and suppose it has no operator token, so expression is a single nonempty digit run. -/
theorem spec_4 (expression : Slice Std.U8) (v : Int)
    (h : IsValid expression.val [v] []) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length = 1 ∧ vecInts r = [v] := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (expression : Slice Std.U8) (v : Int)
    (h : IsValid expression.val [v] []), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length = 1 ∧ vecInts r = [v]) := by
  sorry

/-- The function returns r and len(r) = 1 and r[0] = a + b if op is '+', r[0] = a - b if op is '-', and r[0] = a * b if op is '*'.
  Preconditions: Let expression be a valid expression under the problem constraints with exactly one operator token. Let a be the decimal value of the digit run before it, op be the operator byte ('+', '-', or '*'), and b be the decimal value of the digit run after it. -/
theorem spec_5 (expression : Slice Std.U8) (a b : Int) (op : Byte)
    (h : IsValid expression.val [a, b] [op]) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length = 1 ∧ vecInts r = [applyOp op a b] := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (expression : Slice Std.U8) (a b : Int) (op : Byte)
    (h : IsValid expression.val [a, b] [op]), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length = 1 ∧ vecInts r = [applyOp op a b]) := by
  sorry

/-- The function returns r and len(r) = 2; the multiset of the two entries of r is exactly { (a op1 b) op2 c, a op1 (b op2 c) }, where each op is ordinary integer +, -, or *. If the two values are equal, both occurrences are present.
  Preconditions: Let expression be a valid expression under the problem constraints with exactly two operator tokens. Let the three digit-run values be a, b, c and the two operator bytes be op1 then op2. -/
theorem spec_6 (expression : Slice Std.U8) (a b c : Int) (op₁ op₂ : Byte)
    (h : IsValid expression.val [a, b, c] [op₁, op₂]) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length = 2 ∧
      ∀ v : Int,
        count (vecInts r) v =
          count [applyOp op₂ (applyOp op₁ a b) c, applyOp op₁ a (applyOp op₂ b c)] v := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (expression : Slice Std.U8) (a b c : Int) (op₁ op₂ : Byte)
    (h : IsValid expression.val [a, b, c] [op₁, op₂]), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length = 2 ∧
      ∀ v : Int,
        count (vecInts r) v =
          count [applyOp op₂ (applyOp op₁ a b) c, applyOp op₁ a (applyOp op₂ b c)] v) := by
  sorry

/-- The function returns r and for every i with 0 <= i < len(r), r[i] >= 0.
  Preconditions: Let expression be a valid expression under the problem constraints and suppose no operator token is '-'. -/
theorem spec_7 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) (hno : ∀ op ∈ os, op.val ≠ 45) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      ∀ i (hi : i < (vecInts r).length), 0 ≤ (vecInts r)[i]'hi := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) (hno : ∀ op ∈ os, op.val ≠ 45), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      ∀ i (hi : i < (vecInts r).length), 0 ≤ (vecInts r)[i]'hi) := by
  sorry

/-- The function returns r and for every i with 0 <= i < len(r), r[i] = v_0 * v_1 * ... * v_n. Also len(r) = C_n, the n-th Catalan number with C_0 = 1.
  Preconditions: Let expression be a valid expression under the problem constraints and suppose every operator token is '*'. Let the digit-run values be v_0,...,v_n. -/
theorem spec_8 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) (hmul : ∀ op ∈ os, op.val = 42) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      (∀ i (hi : i < (vecInts r).length), (vecInts r)[i]'hi = prodInts ns) ∧
      r.val.length = catalan os.length := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) (hmul : ∀ op ∈ os, op.val = 42), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      (∀ i (hi : i < (vecInts r).length), (vecInts r)[i]'hi = prodInts ns) ∧
      r.val.length = catalan os.length) := by
  sorry

/-- The function returns r and for every i with 0 <= i < len(r), r[i] = v_0 + v_1 + ... + v_n. Also len(r) = C_n, the n-th Catalan number with C_0 = 1.
  Preconditions: Let expression be a valid expression under the problem constraints and suppose every operator token is '+'. Let the digit-run values be v_0,...,v_n. -/
theorem spec_9 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) (hadd : ∀ op ∈ os, op.val = 43) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      (∀ i (hi : i < (vecInts r).length), (vecInts r)[i]'hi = sumInts ns) ∧
      r.val.length = catalan os.length := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) (hadd : ∀ op ∈ os, op.val = 43), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      (∀ i (hi : i < (vecInts r).length), (vecInts r)[i]'hi = sumInts ns) ∧
      r.val.length = catalan os.length) := by
  sorry

/-- The function returns r and there exists an index i with 0 <= i < len(r) such that r[i] equals the value of the fully left-associative parenthesization (((...((v_0 op_1 v_1) op_2 v_2) ... ) op_n v_n), computed by applying op_1 first, then op_2, and so on; for n = 0 this value is v_0.
  Preconditions: Let expression be a valid expression under the problem constraints with digit-run values v_0,...,v_n and operator bytes op_1,...,op_n in order, where n >= 0. -/
theorem spec_10 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      leftAssoc ns os ∈ vecInts r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      leftAssoc ns os ∈ vecInts r) := by
  sorry

/-- The function returns r and for every j with 1 <= j <= n, the multiset { value(T_L) op_j value(T_R) | T_L in Full(L_j), T_R in Full(R_j) } is a sub-multiset of the multiset of entries of r. Equivalently, for every such pair of subexpression parenthesizations, the combined value occurs in r at least as many times as the number of pairs producing that value.
  Preconditions: Let expression be a valid expression under the problem constraints with digit-run values v_0,...,v_n and operator bytes op_1,...,op_n in order. For each j from 1 to n, let L_j be the prefix expression consisting of v_0,...,v_{j-1} and op_1,...,op_{j-1} (L_1 is just v_0), and let R_j be the suffix expression consisting of v_j,...,v_n and op_{j+1},...,op_n (R_n is just v_n). Let Full(L_j) and Full(R_j) be the sets of all full parenthesizations of these subexpressions. -/
theorem spec_11 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      ∀ j : Nat, 1 ≤ j → j ≤ os.length → SubMultiset (splitValues ns os j) (vecInts r) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      ∀ j : Nat, 1 ≤ j → j ≤ os.length → SubMultiset (splitValues ns os j) (vecInts r)) := by
  sorry

/-- The function returns r and len(r) = 0.
  Preconditions: Let expression be a byte slice with 1 <= len(expression) <= 20. Suppose every maximal nonempty run of ASCII digit bytes in expression has decimal value in [0,99], and suppose there exists an index i with 0 <= i < len(expression) such that expression[i] is not an ASCII digit and is not equal to '+', '-', or '*'. -/
theorem spec_12 (expression : Slice Std.U8)
    (hlen : 1 ≤ expression.val.length ∧ expression.val.length ≤ 20)
    (hruns : ∀ run ∈ digitRuns expression.val, 0 ≤ digitVal run ∧ digitVal run ≤ 99)
    (hinvalid : ∃ i : Nat, ∃ hi : i < expression.val.length,
      ¬ isDigit (expression.val[i]'hi) ∧ ¬ isOp (expression.val[i]'hi)) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (expression : Slice Std.U8)
    (hlen : 1 ≤ expression.val.length ∧ expression.val.length ≤ 20)
    (hruns : ∀ run ∈ digitRuns expression.val, 0 ≤ digitVal run ∧ digitVal run ≤ 99)
    (hinvalid : ∃ i : Nat, ∃ hi : i < expression.val.length,
      ¬ isDigit (expression.val[i]'hi) ∧ ¬ isOp (expression.val[i]'hi)), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length = 0) := by
  sorry

/-- The function returns r and for every i with 0 <= i < len(r), -2^31 <= r[i] <= 2^31-1.
  Preconditions: Let expression be a valid expression under the problem constraints. Assume the problem's test-generation guarantee that every value produced by any full parenthesization of expression lies in [-2^31, 2^31-1]. -/
theorem spec_13 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os)
    (hbounds : ∀ v ∈ valuesOf ns os, -(2 ^ 31 : Int) ≤ v ∧ v ≤ (2 ^ 31 : Int) - 1) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      ∀ i (hi : i < (vecInts r).length),
        -(2 ^ 31 : Int) ≤ (vecInts r)[i]'hi ∧ (vecInts r)[i]'hi ≤ (2 ^ 31 : Int) - 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os)
    (hbounds : ∀ v ∈ valuesOf ns os, -(2 ^ 31 : Int) ≤ v ∧ v ≤ (2 ^ 31 : Int) - 1), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      ∀ i (hi : i < (vecInts r).length),
        -(2 ^ 31 : Int) ≤ (vecInts r)[i]'hi ∧ (vecInts r)[i]'hi ≤ (2 ^ 31 : Int) - 1) := by
  sorry

/-- The function returns r and len(r) <= 4862.
  Preconditions: Let expression be a valid expression under the problem constraints with len(expression) <= 20. -/
theorem spec_14 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length ≤ 4862 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      r.val.length ≤ 4862) := by
  sorry

/-- The function returns r and for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v is at least the number of full parenthesizations T of expression with value(T) = v.
  Preconditions: Let expression be a valid expression under the problem constraints. -/
theorem spec_15 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      SubMultiset (valuesOf ns os) (vecInts r) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      SubMultiset (valuesOf ns os) (vecInts r)) := by
  sorry

/-- The function returns r and for every index i with 0 <= i < len(r), there exists a full parenthesization T of expression such that value(T) = r[i].
  Preconditions: Let expression be a valid expression under the problem constraints. -/
theorem spec_16 (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      ∀ i (hi : i < (vecInts r).length), (vecInts r)[i]'hi ∈ valuesOf ns os := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (expression : Slice Std.U8) (ns : List Int) (os : List Byte)
    (h : IsValid expression.val ns os), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DiffWaysToCompute.diff_ways_to_compute expression = ok r ∧
      ∀ i (hi : i < (vecInts r).length), (vecInts r)[i]'hi ∈ valuesOf ns os) := by
  sorry

end AegisSpec.DiffWaysToCompute
