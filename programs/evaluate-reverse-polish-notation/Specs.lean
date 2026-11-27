import Aegis.EvalRpn.Code.Funs

/-!
# Specifications of `Aegis.EvalRpn.eval_rpn`

LeetCode problem `evaluate-reverse-polish-notation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.EvalRpn

namespace AegisSpec.EvalRpn

abbrev Token : Type := Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8

abbrev Tokens : Type := Aeneas.Std.Slice Token

def InI32 (x : Int) : Prop := -2147483648 ≤ x ∧ x ≤ 2147483647

def divTrunc (x y : Int) : Int := Int.tdiv x y

def isAdd (t : Token) : Prop := t.val = [43#u8]

def isSub (t : Token) : Prop := t.val = [45#u8]

def isMul (t : Token) : Prop := t.val = [42#u8]

def isDiv (t : Token) : Prop := t.val = [47#u8]

def isOpTok (t : Token) : Prop := isAdd t ∨ isSub t ∨ isMul t ∨ isDiv t

inductive Op : Type where

  | add

  | sub

  | mul

  | div

def opDecode (t : Token) : Option Op :=
  match t.val with
  | [c] =>
      if c.val = 43 then some Op.add
      else if c.val = 45 then some Op.sub
      else if c.val = 42 then some Op.mul
      else if c.val = 47 then some Op.div
      else none
  | _ => none

def digitsVal (l : List U8) : Nat :=
  l.foldl (fun acc c => acc * 10 + (c.val - 48)) 0

def allDigits (l : List U8) : Prop := ∀ c, c ∈ l → 48 ≤ c.val ∧ c.val ≤ 57

def numeral (t : Token) (n : Int) : Prop :=
  ∃ ds : List U8, ds ≠ [] ∧ allDigits ds ∧ -200 ≤ n ∧ n ≤ 200 ∧
    ((t.val = ds ∧ n = (digitsVal ds : Int)) ∨
     (t.val = 45#u8 :: ds ∧ n = -((digitsVal ds : Int))))

inductive Expr : Type where

  | leaf (t : Token) (n : Int) : Expr

  | node (o : Token) (l r : Expr) : Expr

namespace Expr

def postorder : Expr → List Token
  | leaf t _ => [t]
  | node o l r => l.postorder ++ r.postorder ++ [o]

def value : Expr → Int
  | leaf _ n => n
  | node o l r =>
      match opDecode o with
      | some Op.add => l.value + r.value
      | some Op.sub => l.value - r.value
      | some Op.mul => l.value * r.value
      | some Op.div => divTrunc l.value r.value
      | none => 0

def WellFormed : Expr → Prop
  | leaf t n => numeral t n
  | node o l r => isOpTok o ∧ l.WellFormed ∧ r.WellFormed

def NoDivZero : Expr → Prop
  | leaf _ _ => True
  | node o l r => l.NoDivZero ∧ r.NoDivZero ∧ (isDiv o → r.value ≠ 0)

def AllValuesInI32 : Expr → Prop
  | leaf _ n => InI32 n
  | node o l r => InI32 (value (node o l r)) ∧ l.AllValuesInI32 ∧ r.AllValuesInI32

end Expr

def Valid (v : List Token) : Prop := ∃ E : Expr, E.WellFormed ∧ E.postorder = v

def RpnValue (v : List Token) (x : Int) : Prop :=
  ∃ E : Expr, E.WellFormed ∧ E.postorder = v ∧ E.value = x

def ValidNoDivZero (v : List Token) : Prop :=
  ∃ E : Expr, E.WellFormed ∧ E.postorder = v ∧ E.NoDivZero

def InputOK (tokens : Tokens) : Prop :=
  ∃ E : Expr, E.WellFormed ∧ E.postorder = tokens.val ∧ E.NoDivZero ∧ E.AllValuesInI32

/-- Let E be the unique binary expression tree whose postorder traversal is exactly tokens. Define V on such trees by: V(leaf with numeric token representing n) = n; V(node with operator '+' and left/right values x,y) = x + y; V(node with operator '-' and left/right values x,y) = x - y; V(node with operator '*' and left/right values x,y) = x * y; V(node with operator '/' and left/right values x,y) = trunc(x/y), where trunc(x/y) is the integer obtained from the rational number x/y by truncating toward zero (so trunc(13/5)=2 and trunc(-13/5)=-2), and y != 0. Then eval_rpn tokens returns a result r and r = V(E).
  Preconditions: tokens is a nonempty finite slice of byte vectors. Each element is either (i) one of the four one-byte ASCII operator strings "+", "-", "*", "/", or (ii) the ASCII decimal representation of an integer n with -200 <= n <= 200 (an optional leading '-' followed by one or more decimal digits; the one-byte string "-" is the operator, not a numeral). The sequence tokens is a valid reverse Polish expression: it is the postorder traversal of a binary expression tree whose leaves are the numeric tokens and whose internal nodes are the operator tokens, with the left subtree's tokens appearing before the right subtree's tokens and the operator token after both. No division by zero occurs when this tree is evaluated. The final value and every intermediate value fit in the signed 32-bit integer range [-2147483648, 2147483647]. -/
theorem spec_1 (tokens : Tokens) (E : Expr)
    (hE : E.WellFormed) (hpost : E.postorder = tokens.val)
    (hdiv : E.NoDivZero) (hrange : E.AllValuesInI32) :
    ∃ r : I64, eval_rpn tokens = ok r ∧ r.val = E.value := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (tokens : Tokens) (E : Expr)
    (hE : E.WellFormed) (hpost : E.postorder = tokens.val)
    (hdiv : E.NoDivZero) (hrange : E.AllValuesInI32), ∃ r : I64, eval_rpn tokens = ok r ∧ r.val = E.value) := by
  sorry

/-- eval_rpn tokens returns a result r; equivalently, the evaluation does not fail. In particular, no signed 64-bit integer overflow, array index out of bounds, division by zero, or panic occurs.
  Preconditions: tokens is a nonempty finite slice of byte vectors. Each element is either (i) one of the four one-byte ASCII operator strings "+", "-", "*", "/", or (ii) the ASCII decimal representation of an integer n with -200 <= n <= 200 (an optional leading '-' followed by one or more decimal digits; the one-byte string "-" is the operator, not a numeral). The sequence tokens is a valid reverse Polish expression: it is the postorder traversal of a binary expression tree whose leaves are the numeric tokens and whose internal nodes are the operator tokens, with the left subtree's tokens appearing before the right subtree's tokens and the operator token after both. No division by zero occurs when this tree is evaluated. The final value and every intermediate value fit in the signed 32-bit integer range [-2147483648, 2147483647]. -/
theorem spec_2 (tokens : Tokens) (h : InputOK tokens) :
    ∃ r : I64, eval_rpn tokens = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (tokens : Tokens) (h : InputOK tokens), ∃ r : I64, eval_rpn tokens = ok r) := by
  sorry

/-- Whenever eval_rpn tokens returns a result r, -2147483648 <= r <= 2147483647.
  Preconditions: tokens is a nonempty finite slice of byte vectors. Each element is either (i) one of the four one-byte ASCII operator strings "+", "-", "*", "/", or (ii) the ASCII decimal representation of an integer n with -200 <= n <= 200 (an optional leading '-' followed by one or more decimal digits; the one-byte string "-" is the operator, not a numeral). The sequence tokens is a valid reverse Polish expression: it is the postorder traversal of a binary expression tree whose leaves are the numeric tokens and whose internal nodes are the operator tokens, with the left subtree's tokens appearing before the right subtree's tokens and the operator token after both. No division by zero occurs when this tree is evaluated. The final value and every intermediate value fit in the signed 32-bit integer range [-2147483648, 2147483647]. -/
theorem spec_3 (tokens : Tokens) (r : I64)
    (h : InputOK tokens) (hr : eval_rpn tokens = ok r) :
    InI32 r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (tokens : Tokens) (r : I64)
    (h : InputOK tokens) (hr : eval_rpn tokens = ok r), InI32 r.val) := by
  sorry

/-- Let x be the RPN value of A and y be the RPN value of B, where the RPN value of a valid token sequence is the value of its unique expression tree using the operator meanings +, -, *, and / with division truncated toward zero. Then eval_rpn tokens returns a result r and r = x + y.
  Preconditions: tokens is a nonempty finite slice of byte vectors. Each element is either (i) one of the four one-byte ASCII operator strings "+", "-", "*", "/", or (ii) the ASCII decimal representation of an integer n with -200 <= n <= 200 (an optional leading '-' followed by one or more decimal digits; the one-byte string "-" is the operator, not a numeral). The sequence tokens is a valid reverse Polish expression: it is the postorder traversal of a binary expression tree whose leaves are the numeric tokens and whose internal nodes are the operator tokens, with the left subtree's tokens appearing before the right subtree's tokens and the operator token after both. No division by zero occurs when this tree is evaluated. The final value and every intermediate value fit in the signed 32-bit integer range [-2147483648, 2147483647]. In addition, tokens is the concatenation A ++ B ++ ["+"], where A and B are nonempty valid reverse Polish token sequences. -/
theorem spec_4 (tokens : Tokens) (A B : List Token) (op : Token) (x y : Int)
    (h : InputOK tokens)
    (hA : Valid A) (hAne : A ≠ []) (hB : Valid B) (hBne : B ≠ [])
    (hx : RpnValue A x) (hy : RpnValue B y)
    (hplus : isAdd op) (hsplit : tokens.val = A ++ B ++ [op]) :
    ∃ r : I64, eval_rpn tokens = ok r ∧ r.val = x + y := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (tokens : Tokens) (A B : List Token) (op : Token) (x y : Int)
    (h : InputOK tokens)
    (hA : Valid A) (hAne : A ≠ []) (hB : Valid B) (hBne : B ≠ [])
    (hx : RpnValue A x) (hy : RpnValue B y)
    (hplus : isAdd op) (hsplit : tokens.val = A ++ B ++ [op]), ∃ r : I64, eval_rpn tokens = ok r ∧ r.val = x + y) := by
  sorry

/-- Let x be the RPN value of A and y be the RPN value of B, where the RPN value of a valid token sequence is the value of its unique expression tree using the operator meanings +, -, *, and / with division truncated toward zero. Then eval_rpn tokens returns a result r and r = x - y.
  Preconditions: tokens is a nonempty finite slice of byte vectors. Each element is either (i) one of the four one-byte ASCII operator strings "+", "-", "*", "/", or (ii) the ASCII decimal representation of an integer n with -200 <= n <= 200 (an optional leading '-' followed by one or more decimal digits; the one-byte string "-" is the operator, not a numeral). The sequence tokens is a valid reverse Polish expression: it is the postorder traversal of a binary expression tree whose leaves are the numeric tokens and whose internal nodes are the operator tokens, with the left subtree's tokens appearing before the right subtree's tokens and the operator token after both. No division by zero occurs when this tree is evaluated. The final value and every intermediate value fit in the signed 32-bit integer range [-2147483648, 2147483647]. In addition, tokens is the concatenation A ++ B ++ ["-"], where A and B are nonempty valid reverse Polish token sequences. -/
theorem spec_5 (tokens : Tokens) (A B : List Token) (op : Token) (x y : Int)
    (h : InputOK tokens)
    (hA : Valid A) (hAne : A ≠ []) (hB : Valid B) (hBne : B ≠ [])
    (hx : RpnValue A x) (hy : RpnValue B y)
    (hminus : isSub op) (hsplit : tokens.val = A ++ B ++ [op]) :
    ∃ r : I64, eval_rpn tokens = ok r ∧ r.val = x - y := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (tokens : Tokens) (A B : List Token) (op : Token) (x y : Int)
    (h : InputOK tokens)
    (hA : Valid A) (hAne : A ≠ []) (hB : Valid B) (hBne : B ≠ [])
    (hx : RpnValue A x) (hy : RpnValue B y)
    (hminus : isSub op) (hsplit : tokens.val = A ++ B ++ [op]), ∃ r : I64, eval_rpn tokens = ok r ∧ r.val = x - y) := by
  sorry

/-- Let x be the RPN value of A and y be the RPN value of B, where the RPN value of a valid token sequence is the value of its unique expression tree using the operator meanings +, -, *, and / with division truncated toward zero. Then eval_rpn tokens returns a result r and r = x * y.
  Preconditions: tokens is a nonempty finite slice of byte vectors. Each element is either (i) one of the four one-byte ASCII operator strings "+", "-", "*", "/", or (ii) the ASCII decimal representation of an integer n with -200 <= n <= 200 (an optional leading '-' followed by one or more decimal digits; the one-byte string "-" is the operator, not a numeral). The sequence tokens is a valid reverse Polish expression: it is the postorder traversal of a binary expression tree whose leaves are the numeric tokens and whose internal nodes are the operator tokens, with the left subtree's tokens appearing before the right subtree's tokens and the operator token after both. No division by zero occurs when this tree is evaluated. The final value and every intermediate value fit in the signed 32-bit integer range [-2147483648, 2147483647]. In addition, tokens is the concatenation A ++ B ++ ["*"], where A and B are nonempty valid reverse Polish token sequences. -/
theorem spec_6 (tokens : Tokens) (A B : List Token) (op : Token) (x y : Int)
    (h : InputOK tokens)
    (hA : Valid A) (hAne : A ≠ []) (hB : Valid B) (hBne : B ≠ [])
    (hx : RpnValue A x) (hy : RpnValue B y)
    (hmul : isMul op) (hsplit : tokens.val = A ++ B ++ [op]) :
    ∃ r : I64, eval_rpn tokens = ok r ∧ r.val = x * y := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (tokens : Tokens) (A B : List Token) (op : Token) (x y : Int)
    (h : InputOK tokens)
    (hA : Valid A) (hAne : A ≠ []) (hB : Valid B) (hBne : B ≠ [])
    (hx : RpnValue A x) (hy : RpnValue B y)
    (hmul : isMul op) (hsplit : tokens.val = A ++ B ++ [op]), ∃ r : I64, eval_rpn tokens = ok r ∧ r.val = x * y) := by
  sorry

/-- Let x be the RPN value of A and y be the RPN value of B, where the RPN value of a valid token sequence is the value of its unique expression tree using the operator meanings +, -, *, and / with division truncated toward zero. Then eval_rpn tokens returns a result r and r = trunc(x/y), the integer obtained from the rational number x/y by truncating toward zero.
  Preconditions: tokens is a nonempty finite slice of byte vectors. Each element is either (i) one of the four one-byte ASCII operator strings "+", "-", "*", "/", or (ii) the ASCII decimal representation of an integer n with -200 <= n <= 200 (an optional leading '-' followed by one or more decimal digits; the one-byte string "-" is the operator, not a numeral). The sequence tokens is a valid reverse Polish expression: it is the postorder traversal of a binary expression tree whose leaves are the numeric tokens and whose internal nodes are the operator tokens, with the left subtree's tokens appearing before the right subtree's tokens and the operator token after both. No division by zero occurs when this tree is evaluated. The final value and every intermediate value fit in the signed 32-bit integer range [-2147483648, 2147483647]. In addition, tokens is the concatenation A ++ B ++ ["/"], where A and B are nonempty valid reverse Polish token sequences, and the RPN value y of B is nonzero. -/
theorem spec_7 (tokens : Tokens) (A B : List Token) (op : Token) (x y : Int)
    (h : InputOK tokens)
    (hA : Valid A) (hAne : A ≠ []) (hB : Valid B) (hBne : B ≠ [])
    (hx : RpnValue A x) (hy : RpnValue B y) (hy0 : y ≠ 0)
    (hslash : isDiv op) (hsplit : tokens.val = A ++ B ++ [op]) :
    ∃ r : I64, eval_rpn tokens = ok r ∧ r.val = divTrunc x y := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (tokens : Tokens) (A B : List Token) (op : Token) (x y : Int)
    (h : InputOK tokens)
    (hA : Valid A) (hAne : A ≠ []) (hB : Valid B) (hBne : B ≠ [])
    (hx : RpnValue A x) (hy : RpnValue B y) (hy0 : y ≠ 0)
    (hslash : isDiv op) (hsplit : tokens.val = A ++ B ++ [op]), ∃ r : I64, eval_rpn tokens = ok r ∧ r.val = divTrunc x y) := by
  sorry

/-- Let x be the RPN value of A and y be the RPN value of B. Whenever eval_rpn tokens returns a result r, there exists an integer m such that x = r*y + m, |m| < |y|, and either m = 0 or m has the same sign as x.
  Preconditions: tokens is a nonempty finite slice of byte vectors. Each element is either (i) one of the four one-byte ASCII operator strings "+", "-", "*", "/", or (ii) the ASCII decimal representation of an integer n with -200 <= n <= 200 (an optional leading '-' followed by one or more decimal digits; the one-byte string "-" is the operator, not a numeral). The sequence tokens is a valid reverse Polish expression: it is the postorder traversal of a binary expression tree whose leaves are the numeric tokens and whose internal nodes are the operator tokens, with the left subtree's tokens appearing before the right subtree's tokens and the operator token after both. No division by zero occurs when this tree is evaluated. The final value and every intermediate value fit in the signed 32-bit integer range [-2147483648, 2147483647]. In addition, tokens is the concatenation A ++ B ++ ["/"], where A and B are nonempty valid reverse Polish token sequences, and the RPN value y of B is nonzero. -/
theorem spec_8 (tokens : Tokens) (A B : List Token) (op : Token) (x y : Int) (r : I64)
    (h : InputOK tokens)
    (hA : Valid A) (hAne : A ≠ []) (hB : Valid B) (hBne : B ≠ [])
    (hx : RpnValue A x) (hy : RpnValue B y) (hy0 : y ≠ 0)
    (hslash : isDiv op) (hsplit : tokens.val = A ++ B ++ [op])
    (hr : eval_rpn tokens = ok r) :
    ∃ m : Int, x = r.val * y + m ∧ |m| < |y| ∧ (m = 0 ∨ (0 < m ∧ 0 < x) ∨ (m < 0 ∧ x < 0)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (tokens : Tokens) (A B : List Token) (op : Token) (x y : Int) (r : I64)
    (h : InputOK tokens)
    (hA : Valid A) (hAne : A ≠ []) (hB : Valid B) (hBne : B ≠ [])
    (hx : RpnValue A x) (hy : RpnValue B y) (hy0 : y ≠ 0)
    (hslash : isDiv op) (hsplit : tokens.val = A ++ B ++ [op])
    (hr : eval_rpn tokens = ok r), ∃ m : Int, x = r.val * y + m ∧ |m| < |y| ∧ (m = 0 ∨ (0 < m ∧ 0 < x) ∨ (m < 0 ∧ x < 0))) := by
  sorry

/-- eval_rpn tokens returns a result r and r >= 0.
  Preconditions: tokens is a nonempty finite slice of byte vectors. Each element is either (i) one of the four one-byte ASCII operator strings "+", "-", "*", "/", or (ii) the ASCII decimal representation of an integer n with -200 <= n <= 200 (an optional leading '-' followed by one or more decimal digits; the one-byte string "-" is the operator, not a numeral). The sequence tokens is a valid reverse Polish expression: it is the postorder traversal of a binary expression tree whose leaves are the numeric tokens and whose internal nodes are the operator tokens, with the left subtree's tokens appearing before the right subtree's tokens and the operator token after both. No division by zero occurs when this tree is evaluated. The final value and every intermediate value fit in the signed 32-bit integer range [-2147483648, 2147483647]. In addition, every numeric token represents a nonnegative integer, and no token is the one-byte operator string "-". -/
theorem spec_9 (tokens : Tokens)
    (h : InputOK tokens)
    (hnonneg : ∀ (t : Token) (n : Int), t ∈ tokens.val → numeral t n → 0 ≤ n)
    (hnosub : ∀ t : Token, t ∈ tokens.val → ¬ isSub t) :
    ∃ r : I64, eval_rpn tokens = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (tokens : Tokens)
    (h : InputOK tokens)
    (hnonneg : ∀ (t : Token) (n : Int), t ∈ tokens.val → numeral t n → 0 ≤ n)
    (hnosub : ∀ t : Token, t ∈ tokens.val → ¬ isSub t), ∃ r : I64, eval_rpn tokens = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- Whenever eval_rpn tokens returns a result r, there exists a binary expression tree E such that: (i) the postorder traversal of E is exactly tokens; (ii) each leaf of E is labeled by the integer represented by the corresponding numeric token in tokens; (iii) each internal node of E is labeled by the corresponding operator token in tokens; and (iv) the value of E, computed using +, -, *, and / with division truncated toward zero, is r.
  Preconditions: tokens is a nonempty finite slice of byte vectors. Each element is either (i) one of the four one-byte ASCII operator strings "+", "-", "*", "/", or (ii) the ASCII decimal representation of an integer n with -200 <= n <= 200 (an optional leading '-' followed by one or more decimal digits; the one-byte string "-" is the operator, not a numeral). The sequence tokens is a valid reverse Polish expression: it is the postorder traversal of a binary expression tree whose leaves are the numeric tokens and whose internal nodes are the operator tokens, with the left subtree's tokens appearing before the right subtree's tokens and the operator token after both. No division by zero occurs when this tree is evaluated. The final value and every intermediate value fit in the signed 32-bit integer range [-2147483648, 2147483647]. -/
theorem spec_10 (tokens : Tokens) (r : I64)
    (h : InputOK tokens) (hr : eval_rpn tokens = ok r) :
    ∃ E : Expr, E.WellFormed ∧ E.postorder = tokens.val ∧ E.value = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (tokens : Tokens) (r : I64)
    (h : InputOK tokens) (hr : eval_rpn tokens = ok r), ∃ E : Expr, E.WellFormed ∧ E.postorder = tokens.val ∧ E.value = r.val) := by
  sorry

/-- If eval_rpn tokens1 returns r1 and eval_rpn tokens2 returns r2, then r1 = r2.
  Preconditions: A and B are nonempty valid reverse Polish token sequences whose tokens are either the one-byte operators "+", "-", "*", "/" or ASCII decimal integers in [-200,200], with no division by zero in their evaluations. op is either "+" or "*". Let tokens1 = A ++ B ++ [op] and tokens2 = B ++ A ++ [op]. Both tokens1 and tokens2 satisfy the standing input constraints, including that all final and intermediate values fit in signed 32-bit integers. -/
theorem spec_11 (tokens1 tokens2 : Tokens) (A B : List Token) (op : Token)
    (hA : ValidNoDivZero A) (hAne : A ≠ []) (hB : ValidNoDivZero B) (hBne : B ≠ [])
    (hop : isAdd op ∨ isMul op)
    (hsplit1 : tokens1.val = A ++ B ++ [op]) (hsplit2 : tokens2.val = B ++ A ++ [op])
    (h1 : InputOK tokens1) (h2 : InputOK tokens2)
    (r1 r2 : I64) (hr1 : eval_rpn tokens1 = ok r1) (hr2 : eval_rpn tokens2 = ok r2) :
    r1 = r2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (tokens1 tokens2 : Tokens) (A B : List Token) (op : Token)
    (hA : ValidNoDivZero A) (hAne : A ≠ []) (hB : ValidNoDivZero B) (hBne : B ≠ [])
    (hop : isAdd op ∨ isMul op)
    (hsplit1 : tokens1.val = A ++ B ++ [op]) (hsplit2 : tokens2.val = B ++ A ++ [op])
    (h1 : InputOK tokens1) (h2 : InputOK tokens2)
    (r1 r2 : I64) (hr1 : eval_rpn tokens1 = ok r1) (hr2 : eval_rpn tokens2 = ok r2), r1 = r2) := by
  sorry

end AegisSpec.EvalRpn
