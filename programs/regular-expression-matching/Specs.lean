import Aegis.IsMatch.Code.Funs

/-!
# Specifications of `Aegis.IsMatch.is_match`

LeetCode problem `regular-expression-matching`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsMatch

  open Aegis.IsMatch

  def isLowerByte (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def isDotByte (b : U8) : Prop := b.val = 46

  def isStarByte (b : U8) : Prop := b.val = 42

  def isPatByte (b : U8) : Prop := isLowerByte b ∨ isDotByte b ∨ isStarByte b

  def isLowerOrDot (b : U8) : Prop := isLowerByte b ∨ isDotByte b

  def byteMatch (a c : U8) : Prop := isDotByte a ∨ c = a

  def byteAt (l : List U8) (i : Nat) (c : U8) : Prop := l[i]? = some c

  def byteMatchAt (a : U8) (l : List U8) (i : Nat) : Prop :=
    ∃ c, byteAt l i c ∧ byteMatch a c

  def patMatches : List U8 → List U8 → Prop
    | [], s => s = []
    | _a :: rest, [] =>
        match rest with
        | b :: q => if b.val = 42 then patMatches q [] else False
        | [] => False
    | a :: rest, c :: t =>
        match rest with
        | b :: q =>
            if b.val = 42 then
              (patMatches q (c :: t) ∨ (byteMatch a c ∧ patMatches (a :: b :: q) t))
            else
              (byteMatch a c ∧ patMatches (b :: q) t)
        | [] => byteMatch a c ∧ patMatches [] t
  termination_by p s => p.length + s.length

  inductive Token where
    | single (a : U8)
    | star (a : U8)

  def tokenize : List U8 → List Token
    | [] => []
    | [a] => [Token.single a]
    | a :: b :: q =>
        if b.val = 42 then Token.star a :: tokenize q else Token.single a :: tokenize (b :: q)

  def tokenBoundaries : List U8 → List Nat
    | [] => [0]
    | [_] => [0, 1]
    | _a :: b :: q =>
        if b.val = 42 then
          0 :: (tokenBoundaries q).map (fun n => n + 2)
        else
          0 :: (tokenBoundaries (b :: q)).map (fun n => n + 1)

  def IsTokenPrefix (p : List U8) (k : Nat) : Prop := k ∈ tokenBoundaries p

  def TokenMatches : Token → List U8 → Nat → Nat → Prop
    | Token.single a, s, lo, hi =>
        hi = lo + 1 ∧ ∃ c, byteAt s lo c ∧ byteMatch a c
    | Token.star a, s, lo, hi =>
        lo ≤ hi ∧ hi ≤ s.length ∧
          ∀ k, lo ≤ k → k < hi → ∃ c, byteAt s k c ∧ byteMatch a c

  def minTokens : List U8 → Nat
    | [] => 0
    | [a] => if a.val = 42 then 0 else 1
    | a :: b :: q =>
        if b.val = 42 then minTokens q else (if a.val = 42 then 0 else 1) + minTokens (b :: q)

  /-- Whenever the function returns a result r, r is true exactly when the whole string s is matched by the pattern p. Formally, let matches be the predicate on byte slices defined by: (a) matches(p,s) holds if len(p)=0 and len(s)=0, and for len(p)=0 and len(s)>0 it does not hold; (b) if len(p) >= 2 and p[1]='*', then with a=p[0] and q=p[2..], matches(p,s) holds iff either matches(q,s) holds, or (len(s)>0 and (a='.' or s[0]=a) and matches(p,s[1..]) holds); (c) if len(p)>0 and (len(p)=1 or p[1]!='*'), then with a=p[0], matches(p,s) holds iff len(s)>0 and (a='.' or s[0]=a) and matches(p[1..],s[1..]) holds. Then r=true iff matches(p,s) holds, and r=false iff matches(p,s) does not hold.
    Preconditions: len(s) >= 1 and len(s) <= 20; len(p) >= 1 and len(p) <= 20; for every i with 0 <= i < len(s), s[i] is a lowercase English letter; for every i with 0 <= i < len(p), p[i] is a lowercase English letter, '.' or '*'; and for every i with 0 <= i < len(p), if p[i] = '*' then i > 0 and p[i-1] is a lowercase English letter or '.'. In particular p[0] != '*' and no two '*' are adjacent. -/
  theorem spec_1 (s p : Slice U8)
      (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
      (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
      (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
      (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
      (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
        0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b) :
      ∀ r : Bool, is_match s p = ok r → (r = true ↔ patMatches p.val s.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s p : Slice U8)
        (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
        (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
        (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
        (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
        (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
          0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b), ∀ r : Bool, is_match s p = ok r → (r = true ↔ patMatches p.val s.val)) := by
    sorry

  /-- For every s and p satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access an index outside s or p.
    Preconditions: len(s) >= 1 and len(s) <= 20; len(p) >= 1 and len(p) <= 20; for every i with 0 <= i < len(s), s[i] is a lowercase English letter; for every i with 0 <= i < len(p), p[i] is a lowercase English letter, '.' or '*'; and for every i with 0 <= i < len(p), if p[i] = '*' then i > 0 and p[i-1] is a lowercase English letter or '.'. In particular p[0] != '*' and no two '*' are adjacent. -/
  theorem spec_2 (s p : Slice U8)
      (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
      (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
      (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
      (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
      (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
        0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b) :
      ∃ r : Bool, is_match s p = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s p : Slice U8)
        (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
        (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
        (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
        (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
        (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
          0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b), ∃ r : Bool, is_match s p = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r=true iff len(s)=len(p) and for every i with 0 <= i < len(p), p[i]='.' or p[i]=s[i]; otherwise r=false.
    Preconditions: len(s) >= 1 and len(s) <= 20; len(p) >= 1 and len(p) <= 20; for every i with 0 <= i < len(s), s[i] is a lowercase English letter; for every i with 0 <= i < len(p), p[i] is a lowercase English letter, '.' or '*'; for every i with 0 <= i < len(p), if p[i] = '*' then i > 0 and p[i-1] is a lowercase English letter or '.'; and p contains no byte '*'. -/
  theorem spec_3 (s p : Slice U8)
      (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
      (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
      (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
      (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
      (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
        0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
      (hp_nostar : ∀ b, b ∈ p.val → b.val ≠ 42) :
      ∀ r : Bool, is_match s p = ok r →
        (r = true ↔
          s.val.length = p.val.length ∧
            ∀ i (hi : i < p.val.length), byteMatchAt (p.val[i]'hi) s.val i) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s p : Slice U8)
        (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
        (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
        (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
        (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
        (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
          0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
        (hp_nostar : ∀ b, b ∈ p.val → b.val ≠ 42), ∀ r : Bool, is_match s p = ok r →
          (r = true ↔
            s.val.length = p.val.length ∧
              ∀ i (hi : i < p.val.length), byteMatchAt (p.val[i]'hi) s.val i)) := by
    sorry

  /-- Whenever the function returns a result r, r=true iff for every i with 0 <= i < len(s), p[0]='.' or s[i]=p[0]; otherwise r=false.
    Preconditions: len(s) >= 1 and len(s) <= 20; len(p) >= 1 and len(p) <= 20; for every i with 0 <= i < len(s), s[i] is a lowercase English letter; for every i with 0 <= i < len(p), p[i] is a lowercase English letter, '.' or '*'; for every i with 0 <= i < len(p), if p[i] = '*' then i > 0 and p[i-1] is a lowercase English letter or '.'; len(p)=2; and p[1]='*'. -/
  theorem spec_4 (s p : Slice U8)
      (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
      (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
      (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
      (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
      (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
        0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
      (hp_len2 : p.val.length = 2)
      (hp_second : p.val[1]'(by omega) = 42#u8) :
      ∀ r : Bool, is_match s p = ok r →
        (r = true ↔
          ∀ i (hi : i < s.val.length), byteMatchAt (p.val[0]'(by omega)) s.val i) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s p : Slice U8)
        (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
        (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
        (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
        (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
        (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
          0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
        (hp_len2 : p.val.length = 2)
        (hp_second : p.val[1]'(by omega) = 42#u8), ∀ r : Bool, is_match s p = ok r →
          (r = true ↔
            ∀ i (hi : i < s.val.length), byteMatchAt (p.val[0]'(by omega)) s.val i)) := by
    sorry

  /-- Let min_tokens(p) be the number of indices i with 0 <= i < len(p) such that p[i]!='*' and (i+1=len(p) or p[i+1]!='*'). Whenever the function returns a result r, r=true iff len(s) >= min_tokens(p); otherwise r=false.
    Preconditions: len(s) >= 1 and len(s) <= 20; len(p) >= 1 and len(p) <= 20; for every i with 0 <= i < len(s), s[i] is a lowercase English letter; for every i with 0 <= i < len(p), p[i] is '.' or '*'; for every i with 0 <= i < len(p), if p[i] = '*' then i > 0 and p[i-1] is '.'; and p contains at least one '*'. -/
  theorem spec_5 (s p : Slice U8)
      (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
      (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
      (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
      (hp_dotstar : ∀ i (hi : i < p.val.length),
        isDotByte (p.val[i]'hi) ∨ isStarByte (p.val[i]'hi))
      (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
        0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isDotByte b)
      (hp_has_star : ∃ (i : Nat) (hi : i < p.val.length), p.val[i]'hi = 42#u8) :
      ∀ r : Bool, is_match s p = ok r → (r = true ↔ minTokens p.val ≤ s.val.length) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s p : Slice U8)
        (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
        (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
        (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
        (hp_dotstar : ∀ i (hi : i < p.val.length),
          isDotByte (p.val[i]'hi) ∨ isStarByte (p.val[i]'hi))
        (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
          0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isDotByte b)
        (hp_has_star : ∃ (i : Nat) (hi : i < p.val.length), p.val[i]'hi = 42#u8), ∀ r : Bool, is_match s p = ok r → (r = true ↔ minTokens p.val ≤ s.val.length)) := by
    sorry

  /-- Let min_tokens(p) be the number of indices i with 0 <= i < len(p) such that p[i]!='*' and (i+1=len(p) or p[i+1]!='*'). Whenever the function returns true for (s,p), len(s) >= min_tokens(p).
    Preconditions: len(s) >= 1 and len(s) <= 20; len(p) >= 1 and len(p) <= 20; for every i with 0 <= i < len(s), s[i] is a lowercase English letter; for every i with 0 <= i < len(p), p[i] is a lowercase English letter, '.' or '*'; and for every i with 0 <= i < len(p), if p[i] = '*' then i > 0 and p[i-1] is a lowercase English letter or '.'. In particular p[0] != '*' and no two '*' are adjacent. -/
  theorem spec_6 (s p : Slice U8)
      (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
      (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
      (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
      (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
      (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
        0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b) :
      is_match s p = ok true → minTokens p.val ≤ s.val.length := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s p : Slice U8)
        (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
        (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
        (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
        (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
        (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
          0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b), is_match s p = ok true → minTokens p.val ≤ s.val.length) := by
    sorry

  /-- Whenever the function returns r for (s,p) and r' for (s,p'), if r=true then r'=true.
    Preconditions: len(s) >= 1 and len(s) <= 20; len(p) >= 1 and len(p) <= 20; for every i with 0 <= i < len(s), s[i] is a lowercase English letter; for every i with 0 <= i < len(p), p[i] is a lowercase English letter, '.' or '*'; for every i with 0 <= i < len(p), if p[i] = '*' then i > 0 and p[i-1] is a lowercase English letter or '.'; i is an index with 0 <= i < len(p) and p[i]!='*'; and p' is the slice with p'[i]='.' and p'[j]=p[j] for all j != i. -/
  theorem spec_7 (s p p' : Slice U8)
      (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
      (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
      (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
      (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
      (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
        0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
      (i : Nat) (hi : i < p.val.length) (hp_i_nostar : p.val[i]'hi ≠ 42#u8)
      (hp'_len : p'.val.length = p.val.length)
      (hp'_at : p'.val[i]'(by omega) = 46#u8)
      (hp'_other : ∀ j (hj : j < p.val.length), j ≠ i → p'.val[j]'(by omega) = p.val[j]'hj) :
      ∀ r r' : Bool, is_match s p = ok r → is_match s p' = ok r' →
        r = true → r' = true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s p p' : Slice U8)
        (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
        (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
        (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
        (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
        (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
          0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
        (i : Nat) (hi : i < p.val.length) (hp_i_nostar : p.val[i]'hi ≠ 42#u8)
        (hp'_len : p'.val.length = p.val.length)
        (hp'_at : p'.val[i]'(by omega) = 46#u8)
        (hp'_other : ∀ j (hj : j < p.val.length), j ≠ i → p'.val[j]'(by omega) = p.val[j]'hj), ∀ r r' : Bool, is_match s p = ok r → is_match s p' = ok r' →
          r = true → r' = true) := by
    sorry

  /-- Whenever the function returns r for (s,p) and rq for (s,q), if r=true then rq=true.
    Preconditions: len(s) >= 1 and len(s) <= 20; len(p) >= 1 and len(p) <= 20; for every i with 0 <= i < len(s), s[i] is a lowercase English letter; for every i with 0 <= i < len(p), p[i] is a lowercase English letter, '.' or '*'; for every i with 0 <= i < len(p), if p[i] = '*' then i > 0 and p[i-1] is a lowercase English letter or '.'; k is an integer with 0 <= k <= len(p) such that the prefix p[0..k) is a concatenation of whole tokens of p, where a token is either a single lowercase letter or '.', or a two-byte block a* with a a lowercase letter or '.'; c is a lowercase letter or '.'; q = p[0..k) ++ [c,'*'] ++ p[k..]; and len(q) <= 20 (equivalently len(p) <= 18). -/
  theorem spec_8 (s p q : Slice U8)
      (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
      (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
      (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
      (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
      (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
        0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
      (k : Nat) (hk : k ≤ p.val.length) (hk_prefix : IsTokenPrefix p.val k)
      (c : U8) (hc : isLowerOrDot c)
      (hq : q.val = p.val.take k ++ [c, 42#u8] ++ p.val.drop k)
      (hq_len : q.val.length ≤ 20) :
      ∀ r rq : Bool, is_match s p = ok r → is_match s q = ok rq →
        r = true → rq = true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s p q : Slice U8)
        (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
        (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
        (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
        (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
        (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
          0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
        (k : Nat) (hk : k ≤ p.val.length) (hk_prefix : IsTokenPrefix p.val k)
        (c : U8) (hc : isLowerOrDot c)
        (hq : q.val = p.val.take k ++ [c, 42#u8] ++ p.val.drop k)
        (hq_len : q.val.length ≤ 20), ∀ r rq : Bool, is_match s p = ok r → is_match s q = ok rq →
          r = true → rq = true) := by
    sorry

  /-- For every two strings s and s' satisfying the string constraints with len(s)=len(s') and s[j]=s'[j] for every j with 0 <= j < len(s) and j != i, the boolean returned for (s,p) equals the boolean returned for (s',p).
    Preconditions: len(s) >= 1 and len(s) <= 20; len(p) >= 1 and len(p) <= 20; for every i with 0 <= i < len(s), s[i] is a lowercase English letter; for every i with 0 <= i < len(p), p[i] is a lowercase English letter, '.' or '*'; for every i with 0 <= i < len(p), if p[i] = '*' then i > 0 and p[i-1] is a lowercase English letter or '.'; p contains no '*'; and i is an index with 0 <= i < len(p) and p[i]='.'. -/
  theorem spec_9 (s s' p : Slice U8)
      (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
      (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
      (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
      (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
      (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
        0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
      (hp_nostar : ∀ b, b ∈ p.val → b.val ≠ 42)
      (i : Nat) (hi : i < p.val.length) (hp_i_dot : p.val[i]'hi = 46#u8)
      (hs'_len1 : 1 ≤ s'.val.length) (hs'_len20 : s'.val.length ≤ 20)
      (hs'_lower : ∀ j (hj : j < s'.val.length), isLowerByte (s'.val[j]'hj))
      (hlen : s.val.length = s'.val.length)
      (hagree : ∀ j (hj : j < s.val.length), j ≠ i → s.val[j]'hj = s'.val[j]'(by omega)) :
      ∀ r r' : Bool, is_match s p = ok r → is_match s' p = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s s' p : Slice U8)
        (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
        (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
        (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
        (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
        (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
          0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
        (hp_nostar : ∀ b, b ∈ p.val → b.val ≠ 42)
        (i : Nat) (hi : i < p.val.length) (hp_i_dot : p.val[i]'hi = 46#u8)
        (hs'_len1 : 1 ≤ s'.val.length) (hs'_len20 : s'.val.length ≤ 20)
        (hs'_lower : ∀ j (hj : j < s'.val.length), isLowerByte (s'.val[j]'hj))
        (hlen : s.val.length = s'.val.length)
        (hagree : ∀ j (hj : j < s.val.length), j ≠ i → s.val[j]'hj = s'.val[j]'(by omega)), ∀ r r' : Bool, is_match s p = ok r → is_match s' p = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns true for (s,p), there exist an integer m >= 0, the unique left-to-right tokenization t_0,...,t_{m-1} of p (each t_j is either a single lowercase letter or '.', or a pair a* with a a lowercase letter or '.'), and indices 0 = i_0 <= i_1 <= ... <= i_m = len(s) such that for each j with 0 <= j < m: if t_j=a is a single token, then i_{j+1}=i_j+1 and (a='.' or s[i_j]=a); if t_j=a* is a star token, then for every k with i_j <= k < i_{j+1}, (a='.' or s[k]=a).
    Preconditions: len(s) >= 1 and len(s) <= 20; len(p) >= 1 and len(p) <= 20; for every i with 0 <= i < len(s), s[i] is a lowercase English letter; for every i with 0 <= i < len(p), p[i] is a lowercase English letter, '.' or '*'; and for every i with 0 <= i < len(p), if p[i] = '*' then i > 0 and p[i-1] is a lowercase English letter or '.'. In particular p[0] != '*' and no two '*' are adjacent. -/
  theorem spec_10 (s p : Slice U8)
      (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
      (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
      (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
      (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
      (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
        0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
      (h : is_match s p = ok true) :
      ∃ (m : Nat) (toks : List Token) (idx : Nat → Nat),
        tokenize p.val = toks ∧ toks.length = m ∧ idx 0 = 0 ∧ idx m = s.val.length ∧
          (∀ j, j < m → idx j ≤ idx (j + 1)) ∧
          (∀ (j : Nat) (hj : j < toks.length),
            TokenMatches (toks[j]'hj) s.val (idx j) (idx (j + 1))) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s p : Slice U8)
        (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
        (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
        (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
        (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
        (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
          0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
        (h : is_match s p = ok true), ∃ (m : Nat) (toks : List Token) (idx : Nat → Nat),
          tokenize p.val = toks ∧ toks.length = m ∧ idx 0 = 0 ∧ idx m = s.val.length ∧
            (∀ j, j < m → idx j ≤ idx (j + 1)) ∧
            (∀ (j : Nat) (hj : j < toks.length),
              TokenMatches (toks[j]'hj) s.val (idx j) (idx (j + 1)))) := by
    sorry

  /-- Whenever the function returns true for (s,p), for every i with 0 <= i < len(s) there exists j with 0 <= j < len(p) such that p[j]=s[i].
    Preconditions: len(s) >= 1 and len(s) <= 20; len(p) >= 1 and len(p) <= 20; for every i with 0 <= i < len(s), s[i] is a lowercase English letter; for every i with 0 <= i < len(p), p[i] is a lowercase English letter, '.' or '*'; for every i with 0 <= i < len(p), if p[i] = '*' then i > 0 and p[i-1] is a lowercase English letter or '.'; and p contains no '.'. -/
  theorem spec_11 (s p : Slice U8)
      (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
      (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
      (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
      (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
      (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
        0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
      (hp_nodot : ∀ b, b ∈ p.val → b.val ≠ 46)
      (h : is_match s p = ok true) :
      ∀ i (hi : i < s.val.length),
        ∃ (j : Nat) (hj : j < p.val.length), p.val[j]'hj = s.val[i]'hi := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s p : Slice U8)
        (hs_len1 : 1 ≤ s.val.length) (hs_len20 : s.val.length ≤ 20)
        (hp_len1 : 1 ≤ p.val.length) (hp_len20 : p.val.length ≤ 20)
        (hs_lower : ∀ i (hi : i < s.val.length), isLowerByte (s.val[i]'hi))
        (hp_pat : ∀ i (hi : i < p.val.length), isPatByte (p.val[i]'hi))
        (hp_star : ∀ i (hi : i < p.val.length), p.val[i]'hi = 42#u8 →
          0 < i ∧ ∃ b, p.val[i - 1]? = some b ∧ isLowerOrDot b)
        (hp_nodot : ∀ b, b ∈ p.val → b.val ≠ 46)
        (h : is_match s p = ok true), ∀ i (hi : i < s.val.length),
          ∃ (j : Nat) (hj : j < p.val.length), p.val[j]'hj = s.val[i]'hi) := by
    sorry

  end AegisSpec.IsMatch
