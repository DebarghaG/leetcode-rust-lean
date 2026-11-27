import Aegis.IsValidSerialization.Code.Funs

/-!
# Specifications of `Aegis.IsValidSerialization.is_valid_serialization`

LeetCode problem `verify-preorder-serialization-of-a-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsValidSerialization

  def commaByte : Std.U8 := 44#u8

  def hashByte : Std.U8 := 35#u8

  def splitCommaAux (cur : List Std.U8) (acc : List (List Std.U8)) :
      List Std.U8 → List (List Std.U8)
    | [] => acc ++ [cur.reverse]
    | b :: bs =>
        if b = commaByte then splitCommaAux [] (acc ++ [cur.reverse]) bs
        else splitCommaAux (b :: cur) acc bs

  def splitComma (bs : List Std.U8) : List (List Std.U8) := splitCommaAux [] [] bs

  def tokens (preorder : Slice Std.U8) : List (List Std.U8) := splitComma preorder.val

  def IsDigit (b : Std.U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

  def digitValue (b : Std.U8) : ℕ := b.val - 48

  def numeralValue : List Std.U8 → ℕ
    | [] => 0
    | b :: bs => digitValue b * 10 ^ bs.length + numeralValue bs

  def IsNullToken (t : List Std.U8) : Prop := t = [hashByte]

  def IsNumeralToken (t : List Std.U8) : Prop :=
    t ≠ [] ∧ (∀ b, b ∈ t → IsDigit b) ∧ numeralValue t ≤ 100

  def IsToken (t : List Std.U8) : Prop := IsNullToken t ∨ IsNumeralToken t

  def IsTokenSeq (ts : List (List Std.U8)) : Prop :=
    ts ≠ [] ∧ ∀ t, t ∈ ts → t ≠ [] ∧ IsToken t

  def IsAsciiBytes (bs : List Std.U8) : Prop := ∀ b, b ∈ bs → b.val < 128

  def Formatted (preorder : Slice Std.U8) : Prop :=
    IsAsciiBytes preorder.val ∧ 1 ≤ preorder.val.length ∧ preorder.val.length ≤ 10 ^ 4 ∧
      IsTokenSeq (tokens preorder)

  def FromFormattedBytes (T : List (List Std.U8)) : Prop :=
    ∃ bs : Slice Std.U8, Formatted bs ∧ tokens bs = T

  def countNull : List (List Std.U8) → ℕ
    | [] => 0
    | t :: ts => (if t = [hashByte] then 1 else 0) + countNull ts

  def countInt : List (List Std.U8) → ℕ
    | [] => 0
    | t :: ts => (if t = [hashByte] then 0 else 1) + countInt ts

  def nonNullTokens : List (List Std.U8) → List (List Std.U8)
    | [] => []
    | t :: ts => if t = [hashByte] then nonNullTokens ts else t :: nonNullTokens ts

  def IsPrefixOf (P ts : List (List Std.U8)) : Prop := ∃ s, ts = P ++ s

  def IsProperPrefixOf (P ts : List (List Std.U8)) : Prop := ∃ s, s ≠ [] ∧ ts = P ++ s

  inductive TokTree where

    | leaf : TokTree

    | node : List Std.U8 → TokTree → TokTree → TokTree

  namespace TokTree

  def serialize : TokTree → List (List Std.U8)
    | leaf => [[hashByte]]
    | node v l r => [v] ++ serialize l ++ serialize r

  def nodeTokens : TokTree → List (List Std.U8)
    | leaf => []
    | node v l r => [v] ++ nodeTokens l ++ nodeTokens r

  def numNodes : TokTree → ℕ
    | leaf => 0
    | node _ l r => 1 + numNodes l + numNodes r

  def numNulls : TokTree → ℕ
    | leaf => 1
    | node _ l r => numNulls l + numNulls r

  def WellFormed : TokTree → Prop
    | leaf => True
    | node v l r => IsNumeralToken v ∧ WellFormed l ∧ WellFormed r

  end TokTree

  def IsTreePreorder (ts : List (List Std.U8)) : Prop :=
    ∃ T : TokTree, T.WellFormed ∧ T.serialize = ts

  inductive Valid : List (List Std.U8) → Prop

    | leaf : Valid [[hashByte]]

    | node : ∀ (v : List Std.U8) (L R : List (List Std.U8)),
        IsNumeralToken v → Valid L → Valid R → Valid ([v] ++ L ++ R)

  /-- Whenever is_valid_serialization returns a Boolean result r, r = true if and only if tokens(preorder) belongs to the least set V of token lists satisfying: (i) the one-element list ['#'] is in V; (ii) if v is an integer token, L is in V, and R is in V, then the concatenation [v] ++ L ++ R is in V. Equivalently, r = true iff tokens(preorder) is exactly the preorder serialization of some finite binary tree, where each null child is written '#', each non-null node is written as its integer token, and the children of a non-null node are serialized in preorder order left then right. If no such tree exists, r = false.
    Preconditions: preorder is an ASCII byte slice with 1 <= len(preorder) <= 10^4; splitting its bytes at commas gives a nonempty token list tokens(preorder) with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_1 (preorder : Slice Std.U8) (hpre : Formatted preorder) :
      (∀ r : Bool,
          Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
            (r = true ↔ Valid (tokens preorder))) ∧
        (∀ r : Bool,
          Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
            (r = true ↔ IsTreePreorder (tokens preorder))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (preorder : Slice Std.U8) (hpre : Formatted preorder), (∀ r : Bool,
            Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
              (r = true ↔ Valid (tokens preorder))) ∧
          (∀ r : Bool,
            Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
              (r = true ↔ IsTreePreorder (tokens preorder)))) := by
    sorry

  /-- For every preorder satisfying the precondition, is_valid_serialization returns a Boolean result r; it does not fail, panic, overflow, or access out of bounds.
    Preconditions: preorder is an ASCII byte slice with 1 <= len(preorder) <= 10^4; splitting its bytes at commas gives a nonempty token list tokens(preorder) with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_2 (preorder : Slice Std.U8) (hpre : Formatted preorder) :
      ∃ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (preorder : Slice Std.U8) (hpre : Formatted preorder), ∃ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r) := by
    sorry

  /-- Let m = len(tokens(preorder)). If m is even, then whenever is_valid_serialization returns a Boolean result r, r = false. Hence a true result can occur only when the number of tokens is odd.
    Preconditions: preorder is an ASCII byte slice with 1 <= len(preorder) <= 10^4; splitting its bytes at commas gives a nonempty token list tokens(preorder) with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_3 (preorder : Slice Std.U8) (hpre : Formatted preorder)
      (hm : (tokens preorder).length % 2 = 0) :
      (∀ r : Bool,
          Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = false) ∧
        (∀ r : Bool,
          Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = true →
            (tokens preorder).length % 2 = 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (preorder : Slice Std.U8) (hpre : Formatted preorder)
        (hm : (tokens preorder).length % 2 = 0), (∀ r : Bool,
            Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = false) ∧
          (∀ r : Bool,
            Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = true →
              (tokens preorder).length % 2 = 1)) := by
    sorry

  /-- Let h be the number of tokens equal to '#' in tokens(preorder), and let z be the number of tokens that are not '#' (integer tokens). If h != z + 1, then whenever is_valid_serialization returns a Boolean result r, r = false. Equivalently, if r = true then h = z + 1.
    Preconditions: preorder is an ASCII byte slice with 1 <= len(preorder) <= 10^4; splitting its bytes at commas gives a nonempty token list tokens(preorder) with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_4 (preorder : Slice Std.U8) (hpre : Formatted preorder)
      (hbad : countNull (tokens preorder) ≠ countInt (tokens preorder) + 1) :
      (∀ r : Bool,
          Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = false) ∧
        (∀ r : Bool,
          Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = true →
            countNull (tokens preorder) = countInt (tokens preorder) + 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (preorder : Slice Std.U8) (hpre : Formatted preorder)
        (hbad : countNull (tokens preorder) ≠ countInt (tokens preorder) + 1), (∀ r : Bool,
            Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = false) ∧
          (∀ r : Bool,
            Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = true →
              countNull (tokens preorder) = countInt (tokens preorder) + 1)) := by
    sorry

  /-- For any prefix P of the token list tokens(preorder), let int(P) be the number of non-'#' tokens in P and let len(P) be the number of tokens in P. If there exists such a prefix P with len(P) > 1 + 2*int(P), then whenever is_valid_serialization returns a Boolean result r, r = false.
    Preconditions: preorder is an ASCII byte slice with 1 <= len(preorder) <= 10^4; splitting its bytes at commas gives a nonempty token list tokens(preorder) with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_5 (preorder : Slice Std.U8) (hpre : Formatted preorder)
      (P : List (List Std.U8)) (hP : IsPrefixOf P (tokens preorder))
      (hbad : P.length > 1 + 2 * countInt P) :
      ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
        r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (preorder : Slice Std.U8) (hpre : Formatted preorder)
        (P : List (List Std.U8)) (hP : IsPrefixOf P (tokens preorder))
        (hbad : P.length > 1 + 2 * countInt P), ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
          r = false) := by
    sorry

  /-- For any proper prefix P of tokens(preorder), meaning 0 <= len(P) < len(tokens(preorder)), let int(P) be the number of non-'#' tokens in P and let len(P) be the number of tokens in P. If len(P) = 1 + 2*int(P) for some proper prefix P, then whenever is_valid_serialization returns a Boolean result r, r = false.
    Preconditions: preorder is an ASCII byte slice with 1 <= len(preorder) <= 10^4; splitting its bytes at commas gives a nonempty token list tokens(preorder) with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_6 (preorder : Slice Std.U8) (hpre : Formatted preorder)
      (P : List (List Std.U8)) (hP : IsProperPrefixOf P (tokens preorder))
      (hbad : P.length = 1 + 2 * countInt P) :
      ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
        r = false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (preorder : Slice Std.U8) (hpre : Formatted preorder)
        (P : List (List Std.U8)) (hP : IsProperPrefixOf P (tokens preorder))
        (hbad : P.length = 1 + 2 * countInt P), ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
          r = false) := by
    sorry

  /-- If len(tokens(preorder)) = 1, then whenever is_valid_serialization returns a Boolean result r, r = true if and only if the unique token is '#'. In particular, the input containing only '#' returns true, and a one-token integer input returns false.
    Preconditions: preorder is an ASCII byte slice with 1 <= len(preorder) <= 10^4; splitting its bytes at commas gives a nonempty token list tokens(preorder) with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_7 (preorder : Slice Std.U8) (hpre : Formatted preorder)
      (hone : (tokens preorder).length = 1) :
      ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
        (r = true ↔ tokens preorder = [[hashByte]]) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (preorder : Slice Std.U8) (hpre : Formatted preorder)
        (hone : (tokens preorder).length = 1), ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
          (r = true ↔ tokens preorder = [[hashByte]])) := by
    sorry

  /-- If the first token of tokens(preorder) is '#' and len(tokens(preorder)) > 1, then whenever is_valid_serialization returns a Boolean result r, r = false.
    Preconditions: preorder is an ASCII byte slice with 1 <= len(preorder) <= 10^4; splitting its bytes at commas gives a nonempty token list tokens(preorder) with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_8 (preorder : Slice Std.U8) (hpre : Formatted preorder)
      (hmore : 1 < (tokens preorder).length)
      (hfirst : ∃ T : List (List Std.U8), tokens preorder = [hashByte] :: T) :
      ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
        r = false := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (preorder : Slice Std.U8) (hpre : Formatted preorder)
        (hmore : 1 < (tokens preorder).length)
        (hfirst : ∃ T : List (List Std.U8), tokens preorder = [hashByte] :: T), ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
          r = false) := by
    sorry

  /-- If the last token of tokens(preorder) is not '#', then whenever is_valid_serialization returns a Boolean result r, r = false. Equivalently, if r = true then the last token is '#'.
    Preconditions: preorder is an ASCII byte slice with 1 <= len(preorder) <= 10^4; splitting its bytes at commas gives a nonempty token list tokens(preorder) with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_9 (preorder : Slice Std.U8) (hpre : Formatted preorder)
      (t : List Std.U8) (hlast : (tokens preorder).getLast? = some t)
      (hne : t ≠ [hashByte]) :
      (∀ r : Bool,
          Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = false) ∧
        (∀ r : Bool,
          Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = true →
            (tokens preorder).getLast? = some [hashByte]) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (preorder : Slice Std.U8) (hpre : Formatted preorder)
        (t : List Std.U8) (hlast : (tokens preorder).getLast? = some t)
        (hne : t ≠ [hashByte]), (∀ r : Bool,
            Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = false) ∧
          (∀ r : Bool,
            Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = true →
              (tokens preorder).getLast? = some [hashByte])) := by
    sorry

  /-- Suppose tokens(preorder1) and tokens(preorder2) have the same length m, and for every i with 0 <= i < m, the i-th token of preorder1 is '#' if and only if the i-th token of preorder2 is '#'. Then whenever is_valid_serialization returns Boolean results r1 on preorder1 and r2 on preorder2, r1 = r2. Thus validity depends only on the pattern of null versus non-null tokens, not on the integer values.
    Preconditions: preorder1 and preorder2 each satisfy the format precondition: each is an ASCII byte slice with 1 <= length <= 10^4; splitting its bytes at commas gives a nonempty token list with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_10 (preorder₁ preorder₂ : Slice Std.U8) (hpre₁ : Formatted preorder₁)
      (hpre₂ : Formatted preorder₂)
      (hlen : (tokens preorder₁).length = (tokens preorder₂).length)
      (hsame : ∀ i : ℕ, i < (tokens preorder₁).length →
        ((tokens preorder₁)[i]? = some [hashByte] ↔
          (tokens preorder₂)[i]? = some [hashByte])) :
      ∀ r₁ r₂ : Bool,
        Aegis.IsValidSerialization.is_valid_serialization preorder₁ = ok r₁ →
          Aegis.IsValidSerialization.is_valid_serialization preorder₂ = ok r₂ → r₁ = r₂ := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (preorder₁ preorder₂ : Slice Std.U8) (hpre₁ : Formatted preorder₁)
        (hpre₂ : Formatted preorder₂)
        (hlen : (tokens preorder₁).length = (tokens preorder₂).length)
        (hsame : ∀ i : ℕ, i < (tokens preorder₁).length →
          ((tokens preorder₁)[i]? = some [hashByte] ↔
            (tokens preorder₂)[i]? = some [hashByte])), ∀ r₁ r₂ : Bool,
          Aegis.IsValidSerialization.is_valid_serialization preorder₁ = ok r₁ →
            Aegis.IsValidSerialization.is_valid_serialization preorder₂ = ok r₂ → r₁ = r₂) := by
    sorry

  /-- The token list [v, '#'] ++ T is the preorder token list of some finite binary tree if and only if T is the preorder token list of some finite binary tree. Consequently, whenever is_valid_serialization returns Boolean results r on preorder and r2 on preorder2, r2 = r.
    Preconditions: v is an integer token, meaning a nonempty decimal numeral denoting an integer in [0,100]; T is a nonempty token list obtainable from some byte string satisfying the format precondition; preorder and preorder2 are ASCII byte slices satisfying the format precondition with tokens(preorder) = T and tokens(preorder2) = [v, '#'] ++ T. -/
  theorem spec_11 (v : List Std.U8) (T : List (List Std.U8)) (hv : IsNumeralToken v)
      (hT : FromFormattedBytes T) (preorder preorder₂ : Slice Std.U8)
      (hpre : Formatted preorder) (hpre₂ : Formatted preorder₂)
      (htok : tokens preorder = T) (htok₂ : tokens preorder₂ = [v] ++ [[hashByte]] ++ T) :
      (IsTreePreorder ([v] ++ [[hashByte]] ++ T) ↔ IsTreePreorder T) ∧
        (∀ r r₂ : Bool,
          Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
            Aegis.IsValidSerialization.is_valid_serialization preorder₂ = ok r₂ →
              r₂ = r) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (v : List Std.U8) (T : List (List Std.U8)) (hv : IsNumeralToken v)
        (hT : FromFormattedBytes T) (preorder preorder₂ : Slice Std.U8)
        (hpre : Formatted preorder) (hpre₂ : Formatted preorder₂)
        (htok : tokens preorder = T) (htok₂ : tokens preorder₂ = [v] ++ [[hashByte]] ++ T), (IsTreePreorder ([v] ++ [[hashByte]] ++ T) ↔ IsTreePreorder T) ∧
          (∀ r r₂ : Bool,
            Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
              Aegis.IsValidSerialization.is_valid_serialization preorder₂ = ok r₂ →
                r₂ = r)) := by
    sorry

  /-- If is_valid_serialization returns true on preorder, then is_valid_serialization returns true on preorder2. Equivalently, if T is the preorder token list of some finite binary tree, then [v] ++ T ++ ['#'] is also the preorder token list of some finite binary tree.
    Preconditions: v is an integer token, meaning a nonempty decimal numeral denoting an integer in [0,100]; T is a nonempty token list obtainable from some byte string satisfying the format precondition; preorder and preorder2 are ASCII byte slices satisfying the format precondition with tokens(preorder) = T and tokens(preorder2) = [v] ++ T ++ ['#']. -/
  theorem spec_12 (v : List Std.U8) (T : List (List Std.U8)) (hv : IsNumeralToken v)
      (hT : FromFormattedBytes T) (preorder preorder₂ : Slice Std.U8)
      (hpre : Formatted preorder) (hpre₂ : Formatted preorder₂)
      (htok : tokens preorder = T) (htok₂ : tokens preorder₂ = [v] ++ T ++ [[hashByte]]) :
      (IsTreePreorder T → IsTreePreorder ([v] ++ T ++ [[hashByte]])) ∧
        (∀ r : Bool,
          Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = true →
            Aegis.IsValidSerialization.is_valid_serialization preorder₂ = ok true) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (v : List Std.U8) (T : List (List Std.U8)) (hv : IsNumeralToken v)
        (hT : FromFormattedBytes T) (preorder preorder₂ : Slice Std.U8)
        (hpre : Formatted preorder) (hpre₂ : Formatted preorder₂)
        (htok : tokens preorder = T) (htok₂ : tokens preorder₂ = [v] ++ T ++ [[hashByte]]), (IsTreePreorder T → IsTreePreorder ([v] ++ T ++ [[hashByte]])) ∧
          (∀ r : Bool,
            Aegis.IsValidSerialization.is_valid_serialization preorder = ok r → r = true →
              Aegis.IsValidSerialization.is_valid_serialization preorder₂ = ok true)) := by
    sorry

  /-- Whenever is_valid_serialization returns a Boolean result r, if r = true then there exists a finite binary tree T such that tokens(preorder) is exactly the preorder token list of T. Moreover, for any such T, if z is the number of non-'#' tokens in tokens(preorder), then T has exactly z non-null nodes and z+1 null child entries, and the non-'#' tokens of tokens(preorder), read in order, are exactly the values of those non-null nodes in preorder.
    Preconditions: preorder is an ASCII byte slice with 1 <= len(preorder) <= 10^4; splitting its bytes at commas gives a nonempty token list tokens(preorder) with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_13 (preorder : Slice Std.U8) (hpre : Formatted preorder) :
      ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
        r = true →
          ∃ T : TokTree,
            T.WellFormed ∧ T.serialize = tokens preorder ∧
              T.numNodes = countInt (tokens preorder) ∧
                T.numNulls = countInt (tokens preorder) + 1 ∧
                  T.nodeTokens = nonNullTokens (tokens preorder) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (preorder : Slice Std.U8) (hpre : Formatted preorder), ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
          r = true →
            ∃ T : TokTree,
              T.WellFormed ∧ T.serialize = tokens preorder ∧
                T.numNodes = countInt (tokens preorder) ∧
                  T.numNulls = countInt (tokens preorder) + 1 ∧
                    T.nodeTokens = nonNullTokens (tokens preorder)) := by
    sorry

  /-- Let h(P) be the number of '#' tokens in a prefix P of tokens(preorder), and let z(P) be the number of non-'#' tokens in P. Then whenever is_valid_serialization returns a Boolean result r, r = true if and only if h(tokens(preorder)) = z(tokens(preorder)) + 1 and for every proper prefix P of tokens(preorder), h(P) <= z(P). Equivalently, the slot count starting at 1, decremented by 1 for every token and then incremented by 2 for every non-'#' token, is positive before each token and is 0 after the last token.
    Preconditions: preorder is an ASCII byte slice with 1 <= len(preorder) <= 10^4; splitting its bytes at commas gives a nonempty token list tokens(preorder) with no empty tokens, and every token is either exactly '#' or a nonempty decimal numeral denoting an integer in [0,100]. -/
  theorem spec_14 (preorder : Slice Std.U8) (hpre : Formatted preorder) :
      ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
        (r = true ↔
          (countNull (tokens preorder) = countInt (tokens preorder) + 1 ∧
            ∀ P : List (List Std.U8),
              IsProperPrefixOf P (tokens preorder) → countNull P ≤ countInt P)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (preorder : Slice Std.U8) (hpre : Formatted preorder), ∀ r : Bool, Aegis.IsValidSerialization.is_valid_serialization preorder = ok r →
          (r = true ↔
            (countNull (tokens preorder) = countInt (tokens preorder) + 1 ∧
              ∀ P : List (List Std.U8),
                IsProperPrefixOf P (tokens preorder) → countNull P ≤ countInt P))) := by
    sorry

  end AegisSpec.IsValidSerialization
