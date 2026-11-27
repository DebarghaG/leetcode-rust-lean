import Aegis.Calculate.Code.Funs

/-!
# Specifications of `Aegis.Calculate.calculate`

LeetCode problem `basic-calculator-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.Calculate

def IsDigit (c : U8) : Prop := 48 ≤ c.val ∧ c.val ≤ 57

def IsAdd (c : U8) : Prop := c.val = 43

def IsSub (c : U8) : Prop := c.val = 45

def IsMul (c : U8) : Prop := c.val = 42

def IsDiv (c : U8) : Prop := c.val = 47

def IsOp (c : U8) : Prop := IsAdd c ∨ IsSub c ∨ IsMul c ∨ IsDiv c

def IsSpace (c : U8) : Prop := c.val = 32

def IsLParen (c : U8) : Prop := c.val = 40

def IsRParen (c : U8) : Prop := c.val = 41

def IsParen (c : U8) : Prop := IsLParen c ∨ IsRParen c

def IsSep (c : U8) : Prop := IsSpace c ∨ IsParen c

def isDigitB (c : U8) : Bool := decide (48 ≤ c.val ∧ c.val ≤ 57)

def isSepB (c : U8) : Bool := decide (c.val = 32 ∨ c.val = 40 ∨ c.val = 41)

def isSpaceB (c : U8) : Bool := decide (c.val = 32)

def isMulDivB (c : U8) : Bool := decide (c.val = 42 ∨ c.val = 47)

def isAddSubB (c : U8) : Bool := decide (c.val = 43 ∨ c.val = 45)

def IsBasicByte (c : U8) : Prop := IsDigit c ∨ IsOp c ∨ IsSpace c

def IsParenByte (c : U8) : Prop := IsBasicByte c ∨ IsParen c

def BasicAlphabet (l : List U8) : Prop := ∀ c ∈ l, IsBasicByte c

def ParenAlphabet (l : List U8) : Prop := ∀ c ∈ l, IsParenByte c

inductive Tok where

  | num (v : Int)

  | op (c : U8) : Tok

def flushNum (cur : Option Int) (toks : List Tok) : List Tok :=
  match cur with
  | none => toks
  | some v => Tok.num v :: toks

def tokenizeAux : List U8 → List Tok → Option Int → List Tok
  | [], toks, cur => (flushNum cur toks).reverse
  | c :: cs, toks, cur =>
    if isDigitB c then
      tokenizeAux cs toks (some (cur.getD 0 * 10 + ((c.val : Int) - 48)))
    else if isSepB c then
      tokenizeAux cs (flushNum cur toks) none
    else
      tokenizeAux cs (Tok.op c :: flushNum cur toks) none

def tokenize (l : List U8) : List Tok := tokenizeAux l [] none

def ExprForm : List Tok → Prop
  | [] => False
  | Tok.num _ :: [] => True
  | Tok.num _ :: Tok.op c :: rest => IsOp c ∧ ExprForm rest
  | _ => False

def i32Min : Int := -((2 : Int) ^ 31)

def i32Max : Int := (2 : Int) ^ 31 - 1

def inI32 (v : Int) : Bool := decide (i32Min ≤ v ∧ v ≤ i32Max)

def litOK (v : Int) : Bool := decide (0 ≤ v ∧ v ≤ i32Max)

def mathMul (a : Int) (c : U8) (b : Int) : Option Int :=
  if c.val == 42 then some (a * b)
  else if c.val == 47 then (if b == 0 then none else some (a.tdiv b))
  else none

def checkedMul (a : Int) (c : U8) (b : Int) : Option Int :=
  match mathMul a c b with
  | none => none
  | some v => if inI32 v then some v else none

def mathAdd (a b : Int) : Option Int := some (a + b)

def checkedAdd (a b : Int) : Option Int := if inI32 (a + b) then some (a + b) else none

def mathLit (n : Int) : Option Int := some n

def checkedLit (n : Int) : Option Int := if litOK n then some n else none

def evalAux (ofLit : Int → Option Int) (mulOp : Int → U8 → Int → Option Int)
    (addOp : Int → Int → Option Int) (total : Int) (acc : Int) :
    List Tok → Option Int
  | [] => addOp total acc
  | Tok.op c :: Tok.num n :: rest =>
    match ofLit n with
    | none => none
    | some v =>
      if isAddSubB c then
        match addOp total acc with
        | none => none
        | some total' =>
          evalAux ofLit mulOp addOp total' (if c.val == 43 then v else -v) rest
      else if isMulDivB c then
        match mulOp acc c v with
        | none => none
        | some acc' => evalAux ofLit mulOp addOp total acc' rest
      else none
  | _ => none

def evalGen (ofLit : Int → Option Int) (mulOp : Int → U8 → Int → Option Int)
    (addOp : Int → Int → Option Int) : List Tok → Option Int
  | [] => none
  | Tok.num n :: rest =>
    match ofLit n with
    | none => none
    | some v => evalAux ofLit mulOp addOp 0 v rest
  | Tok.op _ :: _ => none

def evalMath : List Tok → Option Int := evalGen mathLit mathMul mathAdd

def evalChecked : List Tok → Option Int := evalGen checkedLit checkedMul checkedAdd

def ValidExpr (ts : List Tok) : Prop := ExprForm ts ∧ ∃ v, evalChecked ts = some v

def deleteSpaces (l : List U8) : List U8 := l.filter (fun c => !isSpaceB c)

/-- Let `eval(s)` be the integer value of the token sequence of `s` under the usual precedence: `*` and `/` bind tighter than `+` and `-`; operators of equal precedence associate left to right; each `/` truncates toward zero; there is no unary operator. The function returns a result `r` and `r = eval(s)`.
  Preconditions: `s` is a byte slice with 1 <= len(s) <= 300000. Tokenize `s` as follows: each maximal nonempty contiguous run of ASCII digits '0'..'9' is an integer literal; each byte '+', '-', '*', '/' is an operator; each space byte (ASCII 32) is a separator producing no token; no other byte occurs. The resulting token sequence has the form `n0 op1 n1 ... opk nk` for some k >= 0, alternating literals and operators, beginning and ending with a literal. Each literal's decimal value is in [0, 2^31-1]. The expression is valid: every division in its standard operator-precedence evaluation has a nonzero divisor, and every intermediate value (including the final value) lies in [-2^31, 2^31-1]. -/
theorem spec_1 (s : Slice U8)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 300000)
    (halb : BasicAlphabet s.val)
    (hvalid : ValidExpr (tokenize s.val)) :
    ∃ r : I64, Aegis.Calculate.calculate s = ok r ∧ evalMath (tokenize s.val) = some r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 300000)
    (halb : BasicAlphabet s.val)
    (hvalid : ValidExpr (tokenize s.val)), ∃ r : I64, Aegis.Calculate.calculate s = ok r ∧ evalMath (tokenize s.val) = some r.val) := by
  sorry

/-- Let `T(s)` be the token sequence obtained from `s` by the tokenization in the precondition. Let `value(T(s))` be the integer value of that operator sequence under the same standard precedence and truncating division as in spec_1. The function returns a result `r` and `r = value(T(s))`. Thus parentheses are treated as ignorable whitespace, not as grouping constructs.
  Preconditions: `s` is a byte slice with 1 <= len(s) <= 300000. Tokenize `s` as follows: each maximal nonempty contiguous run of ASCII digits '0'..'9' is an integer literal; each byte '+', '-', '*', '/' is an operator; each space byte (ASCII 32), '(' byte, or ')' byte is a separator producing no token; no other byte occurs. The resulting token sequence has the form `n0 op1 n1 ... opk nk` for some k >= 0, alternating literals and operators, beginning and ending with a literal. Each literal's decimal value is in [0, 2^31-1]. The expression is valid: every division in its standard operator-precedence evaluation has a nonzero divisor, and every intermediate value (including the final value) lies in [-2^31, 2^31-1]. -/
theorem spec_2 (s : Slice U8)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 300000)
    (halb : ParenAlphabet s.val)
    (hvalid : ValidExpr (tokenize s.val)) :
    ∃ r : I64, Aegis.Calculate.calculate s = ok r ∧ evalMath (tokenize s.val) = some r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 300000)
    (halb : ParenAlphabet s.val)
    (hvalid : ValidExpr (tokenize s.val)), ∃ r : I64, Aegis.Calculate.calculate s = ok r ∧ evalMath (tokenize s.val) = some r.val) := by
  sorry

/-- The function returns some result `r`; it does not fail (no overflow, out-of-bounds access, division by zero, or panic).
  Preconditions: Same as spec_2: `s` is a byte slice of length 1..300000 containing only ASCII digits, spaces, '+', '-', '*', '/', '(' and ')'; after tokenization with spaces and parentheses as separators, the token sequence is a valid alternating expression with all literals in [0, 2^31-1], all divisors nonzero, and all intermediate values in [-2^31, 2^31-1]. -/
theorem spec_3 (s : Slice U8)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 300000)
    (halb : ParenAlphabet s.val)
    (hvalid : ValidExpr (tokenize s.val)) :
    ∃ r : I64, Aegis.Calculate.calculate s = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 300000)
    (halb : ParenAlphabet s.val)
    (hvalid : ValidExpr (tokenize s.val)), ∃ r : I64, Aegis.Calculate.calculate s = ok r) := by
  sorry

/-- The function returns a result `r` and `-2^31 <= r <= 2^31-1`.
  Preconditions: Same as spec_1: `s` satisfies the original Basic Calculator II constraints, with no parentheses allowed. -/
theorem spec_4 (s : Slice U8)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 300000)
    (halb : BasicAlphabet s.val)
    (hvalid : ValidExpr (tokenize s.val)) :
    ∃ r : I64, Aegis.Calculate.calculate s = ok r ∧ i32Min ≤ r.val ∧ r.val ≤ i32Max := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 300000)
    (halb : BasicAlphabet s.val)
    (hvalid : ValidExpr (tokenize s.val)), ∃ r : I64, Aegis.Calculate.calculate s = ok r ∧ i32Min ≤ r.val ∧ r.val ≤ i32Max) := by
  sorry

/-- The function returns `r` on `s` and `r'` on `t`, and `r = r'`.
  Preconditions: `s` and `t` are byte slices that both satisfy the precondition of spec_2. Deleting all space bytes (ASCII 32) from `s` and from `t` yields the same byte string, so the two expressions differ only in their spaces; any parentheses present are in the same positions and will be ignored. -/
theorem spec_5 (s t : Slice U8)
    (hlen_s : 1 ≤ s.val.length ∧ s.val.length ≤ 300000)
    (hlen_t : 1 ≤ t.val.length ∧ t.val.length ≤ 300000)
    (halb_s : ParenAlphabet s.val)
    (halb_t : ParenAlphabet t.val)
    (hvalid_s : ValidExpr (tokenize s.val))
    (hvalid_t : ValidExpr (tokenize t.val))
    (hspaces : deleteSpaces s.val = deleteSpaces t.val) :
    ∃ r r' : I64,
      Aegis.Calculate.calculate s = ok r ∧ Aegis.Calculate.calculate t = ok r' ∧
        r.val = r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s t : Slice U8)
    (hlen_s : 1 ≤ s.val.length ∧ s.val.length ≤ 300000)
    (hlen_t : 1 ≤ t.val.length ∧ t.val.length ≤ 300000)
    (halb_s : ParenAlphabet s.val)
    (halb_t : ParenAlphabet t.val)
    (hvalid_s : ValidExpr (tokenize s.val))
    (hvalid_t : ValidExpr (tokenize t.val))
    (hspaces : deleteSpaces s.val = deleteSpaces t.val), ∃ r r' : I64,
      Aegis.Calculate.calculate s = ok r ∧ Aegis.Calculate.calculate t = ok r' ∧
        r.val = r'.val) := by
  sorry

end AegisSpec.Calculate
