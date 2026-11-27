import Aegis.IsEscapePossible.Code.Funs

/-!
# Specifications of `Aegis.IsEscapePossible.is_escape_possible`

LeetCode problem `escape-a-large-maze`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.IsEscapePossible

  namespace AegisSpec.IsEscapePossible

  def InBounds (p : Int × Int) : Prop :=
    0 ≤ p.1 ∧ p.1 < 1000000 ∧ 0 ≤ p.2 ∧ p.2 < 1000000

  def coord (s : Slice I64) (i : Nat) : Int :=
    match s.val[i]? with
    | some v => v.val
    | none => 0

  def pointOf (s : Slice I64) : Int × Int := (coord s 0, coord s 1)

  def rowCoord (v : alloc.vec.Vec I64) (i : Nat) : Int :=
    match v.val[i]? with
    | some x => x.val
    | none => 0

  def rowPair (v : alloc.vec.Vec I64) : Int × Int := (rowCoord v 0, rowCoord v 1)

  def Blocked (blocked : Slice (alloc.vec.Vec I64)) : Set (Int × Int) :=
    {p | ∃ v ∈ blocked.val, rowPair v = p}

  def Adjacent (p q : Int × Int) : Prop :=
    (q.1 - p.1).natAbs + (q.2 - p.2).natAbs = 1

  def GridPath (blocked : Slice (alloc.vec.Vec I64)) (s t : Int × Int) : Prop :=
    ∃ (k : Nat) (p : Nat → Int × Int),
      p 0 = s ∧ p k = t ∧
      (∀ j, j ≤ k → InBounds (p j) ∧ p j ∉ Blocked blocked) ∧
      (∀ j, j < k → Adjacent (p j) (p (j + 1)))

  def swapPair (p : Int × Int) : Int × Int := (p.2, p.1)

  /-- The function returns a result r and r = true if and only if there exists an integer k >= 0 and a finite sequence of squares p_0,...,p_k, with p_j=(x_j,y_j) for each j, such that p_0=S, p_k=T, for every j with 0 <= j <= k, 0 <= x_j < 1000000 and 0 <= y_j < 1000000 and p_j is not in B, and for every j with 0 <= j < k, |x_{j+1}-x_j| + |y_{j+1}-y_j| = 1.
    Preconditions: Let S=(source[0],source[1]), T=(target[0],target[1]), and B be the set of pairs (blocked[i][0],blocked[i][1]) for 0 <= i < len(blocked). Assume len(blocked) <= 200; for every i with 0 <= i < len(blocked), len(blocked[i]) = 2 and 0 <= blocked[i][0] < 1000000 and 0 <= blocked[i][1] < 1000000; len(source)=len(target)=2; 0 <= source[0],source[1],target[0],target[1] < 1000000; S != T; S not in B; T not in B. -/
  theorem spec_1
      (blocked : Slice (alloc.vec.Vec I64)) (source : Slice I64) (target : Slice I64)
      (hblen : blocked.val.length ≤ 200)
      (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
      (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
      (hslen : source.val.length = 2)
      (htlen : target.val.length = 2)
      (hsbounds : InBounds (pointOf source))
      (htbounds : InBounds (pointOf target))
      (hne : pointOf source ≠ pointOf target)
      (hsnb : pointOf source ∉ Blocked blocked)
      (htnb : pointOf target ∉ Blocked blocked) :
      ∃ r, is_escape_possible blocked source target = ok r ∧
        (r = true ↔ GridPath blocked (pointOf source) (pointOf target)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (blocked : Slice (alloc.vec.Vec I64)) (source : Slice I64) (target : Slice I64)
        (hblen : blocked.val.length ≤ 200)
        (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
        (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
        (hslen : source.val.length = 2)
        (htlen : target.val.length = 2)
        (hsbounds : InBounds (pointOf source))
        (htbounds : InBounds (pointOf target))
        (hne : pointOf source ≠ pointOf target)
        (hsnb : pointOf source ∉ Blocked blocked)
        (htnb : pointOf target ∉ Blocked blocked), ∃ r, is_escape_possible blocked source target = ok r ∧
          (r = true ↔ GridPath blocked (pointOf source) (pointOf target))) := by
    sorry

  /-- The function returns a result (it does not fail, panic, or overflow) for every blocked, source, and target satisfying these preconditions.
    Preconditions: Let S=(source[0],source[1]), T=(target[0],target[1]), and B be the set of pairs (blocked[i][0],blocked[i][1]) for 0 <= i < len(blocked). Assume len(blocked) <= 200; for every i with 0 <= i < len(blocked), len(blocked[i]) = 2 and 0 <= blocked[i][0] < 1000000 and 0 <= blocked[i][1] < 1000000; len(source)=len(target)=2; 0 <= source[0],source[1],target[0],target[1] < 1000000; S != T; S not in B; T not in B. -/
  theorem spec_2
      (blocked : Slice (alloc.vec.Vec I64)) (source : Slice I64) (target : Slice I64)
      (hblen : blocked.val.length ≤ 200)
      (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
      (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
      (hslen : source.val.length = 2)
      (htlen : target.val.length = 2)
      (hsbounds : InBounds (pointOf source))
      (htbounds : InBounds (pointOf target))
      (hne : pointOf source ≠ pointOf target)
      (hsnb : pointOf source ∉ Blocked blocked)
      (htnb : pointOf target ∉ Blocked blocked) :
      ∃ r, is_escape_possible blocked source target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (blocked : Slice (alloc.vec.Vec I64)) (source : Slice I64) (target : Slice I64)
        (hblen : blocked.val.length ≤ 200)
        (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
        (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
        (hslen : source.val.length = 2)
        (htlen : target.val.length = 2)
        (hsbounds : InBounds (pointOf source))
        (htbounds : InBounds (pointOf target))
        (hne : pointOf source ≠ pointOf target)
        (hsnb : pointOf source ∉ Blocked blocked)
        (htnb : pointOf target ∉ Blocked blocked), ∃ r, is_escape_possible blocked source target = ok r) := by
    sorry

  /-- Let r be the result of is_escape_possible(blocked, source, target), and let r' be the result of is_escape_possible(blocked, target, source). Whenever both calls return results, r = r'.
    Preconditions: Let S=(source[0],source[1]), T=(target[0],target[1]), and B be the set of pairs (blocked[i][0],blocked[i][1]) for 0 <= i < len(blocked). Assume len(blocked) <= 200; for every i with 0 <= i < len(blocked), len(blocked[i]) = 2 and 0 <= blocked[i][0] < 1000000 and 0 <= blocked[i][1] < 1000000; len(source)=len(target)=2; 0 <= source[0],source[1],target[0],target[1] < 1000000; S != T; S not in B; T not in B. -/
  theorem spec_3
      (blocked : Slice (alloc.vec.Vec I64)) (source : Slice I64) (target : Slice I64)
      (hblen : blocked.val.length ≤ 200)
      (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
      (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
      (hslen : source.val.length = 2)
      (htlen : target.val.length = 2)
      (hsbounds : InBounds (pointOf source))
      (htbounds : InBounds (pointOf target))
      (hne : pointOf source ≠ pointOf target)
      (hsnb : pointOf source ∉ Blocked blocked)
      (htnb : pointOf target ∉ Blocked blocked) :
      ∀ r r', is_escape_possible blocked source target = ok r →
        is_escape_possible blocked target source = ok r' → r = r' := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (blocked : Slice (alloc.vec.Vec I64)) (source : Slice I64) (target : Slice I64)
        (hblen : blocked.val.length ≤ 200)
        (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
        (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
        (hslen : source.val.length = 2)
        (htlen : target.val.length = 2)
        (hsbounds : InBounds (pointOf source))
        (htbounds : InBounds (pointOf target))
        (hne : pointOf source ≠ pointOf target)
        (hsnb : pointOf source ∉ Blocked blocked)
        (htnb : pointOf target ∉ Blocked blocked), ∀ r r', is_escape_possible blocked source target = ok r →
          is_escape_possible blocked target source = ok r' → r = r') := by
    sorry

  /-- Let r1 be the result of is_escape_possible(blocked1, source, target), and let r2 be the result of is_escape_possible(blocked2, source, target). Whenever both calls return results, if r2 = true then r1 = true.
    Preconditions: Let S=(source[0],source[1]) and T=(target[0],target[1]). Let B1 and B2 be the sets of coordinate pairs occurring in blocked1 and blocked2, respectively. Assume len(blocked1), len(blocked2) <= 200; every entry in both blocked arrays has length 2 and coordinates in [0,1000000); len(source)=len(target)=2; all source and target coordinates are in [0,1000000); S != T; S and T are not in B1 and not in B2; and B1 is a subset of B2. -/
  theorem spec_4
      (blocked1 : Slice (alloc.vec.Vec I64)) (blocked2 : Slice (alloc.vec.Vec I64))
      (source : Slice I64) (target : Slice I64)
      (hb1len : blocked1.val.length ≤ 200)
      (hb2len : blocked2.val.length ≤ 200)
      (hb1width : ∀ v ∈ blocked1.val, v.val.length = 2)
      (hb2width : ∀ v ∈ blocked2.val, v.val.length = 2)
      (hb1bounds : ∀ v ∈ blocked1.val, InBounds (rowPair v))
      (hb2bounds : ∀ v ∈ blocked2.val, InBounds (rowPair v))
      (hslen : source.val.length = 2)
      (htlen : target.val.length = 2)
      (hsbounds : InBounds (pointOf source))
      (htbounds : InBounds (pointOf target))
      (hne : pointOf source ≠ pointOf target)
      (hsnb1 : pointOf source ∉ Blocked blocked1)
      (htnb1 : pointOf target ∉ Blocked blocked1)
      (hsnb2 : pointOf source ∉ Blocked blocked2)
      (htnb2 : pointOf target ∉ Blocked blocked2)
      (hsub : Blocked blocked1 ⊆ Blocked blocked2) :
      ∀ r1 r2, is_escape_possible blocked1 source target = ok r1 →
        is_escape_possible blocked2 source target = ok r2 → r2 = true → r1 = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (blocked1 : Slice (alloc.vec.Vec I64)) (blocked2 : Slice (alloc.vec.Vec I64))
        (source : Slice I64) (target : Slice I64)
        (hb1len : blocked1.val.length ≤ 200)
        (hb2len : blocked2.val.length ≤ 200)
        (hb1width : ∀ v ∈ blocked1.val, v.val.length = 2)
        (hb2width : ∀ v ∈ blocked2.val, v.val.length = 2)
        (hb1bounds : ∀ v ∈ blocked1.val, InBounds (rowPair v))
        (hb2bounds : ∀ v ∈ blocked2.val, InBounds (rowPair v))
        (hslen : source.val.length = 2)
        (htlen : target.val.length = 2)
        (hsbounds : InBounds (pointOf source))
        (htbounds : InBounds (pointOf target))
        (hne : pointOf source ≠ pointOf target)
        (hsnb1 : pointOf source ∉ Blocked blocked1)
        (htnb1 : pointOf target ∉ Blocked blocked1)
        (hsnb2 : pointOf source ∉ Blocked blocked2)
        (htnb2 : pointOf target ∉ Blocked blocked2)
        (hsub : Blocked blocked1 ⊆ Blocked blocked2), ∀ r1 r2, is_escape_possible blocked1 source target = ok r1 →
          is_escape_possible blocked2 source target = ok r2 → r2 = true → r1 = true) := by
    sorry

  /-- Let r be the result of is_escape_possible(blocked, source, target), and let r' be the result of is_escape_possible(blocked', source, target). Whenever both calls return results, r = r'.
    Preconditions: Let B and B' be the sets of coordinate pairs occurring in blocked and blocked', respectively. Let S=(source[0],source[1]) and T=(target[0],target[1]). Assume len(blocked), len(blocked') <= 200; every entry in both arrays has length 2 and coordinates in [0,1000000); len(source)=len(target)=2; all source and target coordinates are in [0,1000000); S != T; S and T are not in B; and B = B'. -/
  theorem spec_5
      (blocked : Slice (alloc.vec.Vec I64)) (blocked' : Slice (alloc.vec.Vec I64))
      (source : Slice I64) (target : Slice I64)
      (hblen : blocked.val.length ≤ 200)
      (hb'len : blocked'.val.length ≤ 200)
      (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
      (hb'width : ∀ v ∈ blocked'.val, v.val.length = 2)
      (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
      (hb'bounds : ∀ v ∈ blocked'.val, InBounds (rowPair v))
      (hslen : source.val.length = 2)
      (htlen : target.val.length = 2)
      (hsbounds : InBounds (pointOf source))
      (htbounds : InBounds (pointOf target))
      (hne : pointOf source ≠ pointOf target)
      (hsnb : pointOf source ∉ Blocked blocked)
      (htnb : pointOf target ∉ Blocked blocked)
      (hB : Blocked blocked = Blocked blocked') :
      ∀ r r', is_escape_possible blocked source target = ok r →
        is_escape_possible blocked' source target = ok r' → r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (blocked : Slice (alloc.vec.Vec I64)) (blocked' : Slice (alloc.vec.Vec I64))
        (source : Slice I64) (target : Slice I64)
        (hblen : blocked.val.length ≤ 200)
        (hb'len : blocked'.val.length ≤ 200)
        (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
        (hb'width : ∀ v ∈ blocked'.val, v.val.length = 2)
        (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
        (hb'bounds : ∀ v ∈ blocked'.val, InBounds (rowPair v))
        (hslen : source.val.length = 2)
        (htlen : target.val.length = 2)
        (hsbounds : InBounds (pointOf source))
        (htbounds : InBounds (pointOf target))
        (hne : pointOf source ≠ pointOf target)
        (hsnb : pointOf source ∉ Blocked blocked)
        (htnb : pointOf target ∉ Blocked blocked)
        (hB : Blocked blocked = Blocked blocked'), ∀ r r', is_escape_possible blocked source target = ok r →
          is_escape_possible blocked' source target = ok r' → r = r') := by
    sorry

  /-- The function returns a result r and r = true.
    Preconditions: Let B be the set of pairs (blocked[i][0],blocked[i][1]) for 0 <= i < len(blocked), S=(source[0],source[1]), and T=(target[0],target[1]). Assume len(blocked) <= 1; every blocked entry has length 2 and coordinates in [0,1000000); len(source)=len(target)=2; all source and target coordinates are in [0,1000000); S != T; S and T are not in B. -/
  theorem spec_6
      (blocked : Slice (alloc.vec.Vec I64)) (source : Slice I64) (target : Slice I64)
      (hblen : blocked.val.length ≤ 1)
      (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
      (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
      (hslen : source.val.length = 2)
      (htlen : target.val.length = 2)
      (hsbounds : InBounds (pointOf source))
      (htbounds : InBounds (pointOf target))
      (hne : pointOf source ≠ pointOf target)
      (hsnb : pointOf source ∉ Blocked blocked)
      (htnb : pointOf target ∉ Blocked blocked) :
      ∃ r, is_escape_possible blocked source target = ok r ∧ r = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (blocked : Slice (alloc.vec.Vec I64)) (source : Slice I64) (target : Slice I64)
        (hblen : blocked.val.length ≤ 1)
        (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
        (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
        (hslen : source.val.length = 2)
        (htlen : target.val.length = 2)
        (hsbounds : InBounds (pointOf source))
        (htbounds : InBounds (pointOf target))
        (hne : pointOf source ≠ pointOf target)
        (hsnb : pointOf source ∉ Blocked blocked)
        (htnb : pointOf target ∉ Blocked blocked), ∃ r, is_escape_possible blocked source target = ok r ∧ r = true) := by
    sorry

  /-- The function returns a result r and r = false.
    Preconditions: Let B be the set of pairs (blocked[i][0],blocked[i][1]) for 0 <= i < len(blocked), S=(source[0],source[1]), and T=(target[0],target[1]). Assume len(blocked) <= 200; every blocked entry has length 2 and coordinates in [0,1000000); len(source)=len(target)=2; all source and target coordinates are in [0,1000000); S != T; S and T are not in B. Additionally, for every integer pair (x,y) with 0 <= x < 1000000, 0 <= y < 1000000, and |x-source[0]| + |y-source[1]| = 1, the pair (x,y) is in B. -/
  theorem spec_7
      (blocked : Slice (alloc.vec.Vec I64)) (source : Slice I64) (target : Slice I64)
      (hblen : blocked.val.length ≤ 200)
      (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
      (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
      (hslen : source.val.length = 2)
      (htlen : target.val.length = 2)
      (hsbounds : InBounds (pointOf source))
      (htbounds : InBounds (pointOf target))
      (hne : pointOf source ≠ pointOf target)
      (hsnb : pointOf source ∉ Blocked blocked)
      (htnb : pointOf target ∉ Blocked blocked)
      (hneigh : ∀ x y : Int, InBounds (x, y) → Adjacent (pointOf source) (x, y) →
        (x, y) ∈ Blocked blocked) :
      ∃ r, is_escape_possible blocked source target = ok r ∧ r = false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (blocked : Slice (alloc.vec.Vec I64)) (source : Slice I64) (target : Slice I64)
        (hblen : blocked.val.length ≤ 200)
        (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
        (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
        (hslen : source.val.length = 2)
        (htlen : target.val.length = 2)
        (hsbounds : InBounds (pointOf source))
        (htbounds : InBounds (pointOf target))
        (hne : pointOf source ≠ pointOf target)
        (hsnb : pointOf source ∉ Blocked blocked)
        (htnb : pointOf target ∉ Blocked blocked)
        (hneigh : ∀ x y : Int, InBounds (x, y) → Adjacent (pointOf source) (x, y) →
          (x, y) ∈ Blocked blocked), ∃ r, is_escape_possible blocked source target = ok r ∧ r = false) := by
    sorry

  /-- Let r be the result of is_escape_possible(blocked, source, target), and let r' be the result of is_escape_possible(blocked', source', target'). Whenever both calls return results, r = r'.
    Preconditions: Let B be the set of pairs (blocked[i][0],blocked[i][1]) for 0 <= i < len(blocked), S=(source[0],source[1]), and T=(target[0],target[1]). Assume the usual valid-input conditions: len(blocked) <= 200; every blocked entry has length 2 and coordinates in [0,1000000); len(source)=len(target)=2; all source and target coordinates are in [0,1000000); S != T; S and T are not in B. Let blocked' be the array obtained from blocked by replacing each entry [x,y] with [y,x], let source'=(source[1],source[0]), and let target'=(target[1],target[0]). Assume blocked', source', target' also have the required lengths and coordinate ranges. -/
  theorem spec_8
      (blocked : Slice (alloc.vec.Vec I64)) (blocked' : Slice (alloc.vec.Vec I64))
      (source : Slice I64) (source' : Slice I64)
      (target : Slice I64) (target' : Slice I64)
      (hblen : blocked.val.length ≤ 200)
      (hb'len : blocked'.val.length ≤ 200)
      (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
      (hb'width : ∀ v ∈ blocked'.val, v.val.length = 2)
      (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
      (hb'bounds : ∀ v ∈ blocked'.val, InBounds (rowPair v))
      (hslen : source.val.length = 2)
      (hs'len : source'.val.length = 2)
      (htlen : target.val.length = 2)
      (ht'len : target'.val.length = 2)
      (hsbounds : InBounds (pointOf source))
      (hs'bounds : InBounds (pointOf source'))
      (htbounds : InBounds (pointOf target))
      (ht'bounds : InBounds (pointOf target'))
      (hne : pointOf source ≠ pointOf target)
      (hsnb : pointOf source ∉ Blocked blocked)
      (htnb : pointOf target ∉ Blocked blocked)
      (hblen' : blocked'.val.length = blocked.val.length)
      (hrow' : ∀ (i : Nat) (v : alloc.vec.Vec I64), i < blocked.val.length →
        blocked.val[i]? = some v → ∃ v', blocked'.val[i]? = some v' ∧
          rowPair v' = swapPair (rowPair v))
      (hsrc' : pointOf source' = swapPair (pointOf source))
      (htgt' : pointOf target' = swapPair (pointOf target)) :
      ∀ r r', is_escape_possible blocked source target = ok r →
        is_escape_possible blocked' source' target' = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (blocked : Slice (alloc.vec.Vec I64)) (blocked' : Slice (alloc.vec.Vec I64))
        (source : Slice I64) (source' : Slice I64)
        (target : Slice I64) (target' : Slice I64)
        (hblen : blocked.val.length ≤ 200)
        (hb'len : blocked'.val.length ≤ 200)
        (hbwidth : ∀ v ∈ blocked.val, v.val.length = 2)
        (hb'width : ∀ v ∈ blocked'.val, v.val.length = 2)
        (hbounds : ∀ v ∈ blocked.val, InBounds (rowPair v))
        (hb'bounds : ∀ v ∈ blocked'.val, InBounds (rowPair v))
        (hslen : source.val.length = 2)
        (hs'len : source'.val.length = 2)
        (htlen : target.val.length = 2)
        (ht'len : target'.val.length = 2)
        (hsbounds : InBounds (pointOf source))
        (hs'bounds : InBounds (pointOf source'))
        (htbounds : InBounds (pointOf target))
        (ht'bounds : InBounds (pointOf target'))
        (hne : pointOf source ≠ pointOf target)
        (hsnb : pointOf source ∉ Blocked blocked)
        (htnb : pointOf target ∉ Blocked blocked)
        (hblen' : blocked'.val.length = blocked.val.length)
        (hrow' : ∀ (i : Nat) (v : alloc.vec.Vec I64), i < blocked.val.length →
          blocked.val[i]? = some v → ∃ v', blocked'.val[i]? = some v' ∧
            rowPair v' = swapPair (rowPair v))
        (hsrc' : pointOf source' = swapPair (pointOf source))
        (htgt' : pointOf target' = swapPair (pointOf target)), ∀ r r', is_escape_possible blocked source target = ok r →
          is_escape_possible blocked' source' target' = ok r' → r = r') := by
    sorry

  end AegisSpec.IsEscapePossible
