import Aegis.NumSteps.Code.Funs

/-!
# Specifications of `Aegis.NumSteps.num_steps`

LeetCode problem `number-of-steps-to-reduce-a-number-in-binary-representation-to-one`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.NumSteps

namespace AegisSpec.NumSteps

open Classical in

def T (x : Int) : Int :=
  if x = 1 then 1 else if x % 2 = 0 then x / 2 else x + 1

def listValue (l : List Std.U8) : Int :=
  l.foldl (fun acc b => acc * 2 + ((b.val : Int) - 48)) 0

def N (s : Slice Std.U8) : Int :=
  listValue s.val

open Classical in

noncomputable def steps (x : Int) : Nat :=
  if h : ∃ t : Nat, T^[t] x = 1 then Nat.find h else 0

/-- Let N(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 2^{len(s)-1-i}. Let T(1)=1, T(x)=x/2 for even x>1, and T(x)=x+1 for odd x>1. Let steps(s) be the least t >= 0 such that T^t(N(s)) = 1. Whenever the function returns a result r, r = steps(s).
  Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), s[i] is 48 or 49 (ASCII '0' or '1'); and s[0] = 49 (ASCII '1'). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r) :
    r.val = (steps (N s) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r), r.val = (steps (N s) : Int)) := by
  sorry

/-- The function returns a result r for every valid s; equivalently, the Result is Ok, not Err, and no overflow, out-of-bounds access, or panic occurs.
  Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), s[i] is 48 or 49 (ASCII '0' or '1'); and s[0] = 49 (ASCII '1'). -/
theorem spec_2 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8) :
    ∃ r : Std.I64, num_steps s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8), ∃ r : Std.I64, num_steps s = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= 2*len(s).
  Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), s[i] is 48 or 49 (ASCII '0' or '1'); and s[0] = 49 (ASCII '1'). -/
theorem spec_3 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r) :
    r.val ≤ 2 * (s.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r), r.val ≤ 2 * (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, len(s)-1 <= r.
  Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), s[i] is 48 or 49 (ASCII '0' or '1'); and s[0] = 49 (ASCII '1'). -/
theorem spec_4 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r) :
    (s.val.length : Int) - 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r), (s.val.length : Int) - 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if len(s) >= 2 and s[0]=49 and s[i]=48 for every i with 1 <= i < len(s), then r = len(s)-1.
  Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), s[i] is 48 or 49 (ASCII '0' or '1'); and s[0] = 49 (ASCII '1'). -/
theorem spec_5 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r)
    (hge2 : 2 ≤ s.val.length)
    (hzero : s.val[0]? = some 49#u8)
    (hrest : ∀ (i : Nat) (_h1 : 1 ≤ i) (_h2 : i < s.val.length), s.val[i].val = 48) :
    r.val = (s.val.length : Int) - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r)
    (hge2 : 2 ≤ s.val.length)
    (hzero : s.val[0]? = some 49#u8)
    (hrest : ∀ (i : Nat) (_h1 : 1 ≤ i) (_h2 : i < s.val.length), s.val[i].val = 48), r.val = (s.val.length : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, if len(s) >= 2 and s[i]=49 for every i with 0 <= i < len(s), then r = len(s)+1.
  Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), s[i] is 48 or 49 (ASCII '0' or '1'); and s[0] = 49 (ASCII '1'). -/
theorem spec_6 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r)
    (hge2 : 2 ≤ s.val.length)
    (hall : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 49) :
    r.val = (s.val.length : Int) + 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r)
    (hge2 : 2 ≤ s.val.length)
    (hall : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 49), r.val = (s.val.length : Int) + 1) := by
  sorry

/-- Whenever the function returns a result r, if len(s) > 1 and s[len(s)-1] = 48, then r = 1 + steps(u), where u is the prefix consisting of s[0],...,s[len(s)-2], N(u)=sum_{i=0}^{len(u)-1}(u[i]-48)*2^{len(u)-1-i}, and steps(u) is the least t >= 0 such that T^t(N(u))=1 with T(1)=1, T(x)=x/2 for even x>1, and T(x)=x+1 for odd x>1.
  Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), s[i] is 48 or 49 (ASCII '0' or '1'); and s[0] = 49 (ASCII '1'). -/
theorem spec_7 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r)
    (hgt1 : 1 < s.val.length)
    (hlast : s.val[s.val.length - 1]? = some 48#u8) :
    r.val = 1 + (steps (listValue s.val.dropLast) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r)
    (hgt1 : 1 < s.val.length)
    (hlast : s.val[s.val.length - 1]? = some 48#u8), r.val = 1 + (steps (listValue s.val.dropLast) : Int)) := by
  sorry

/-- Whenever the function returns a result r, if len(s) > 1 and s[len(s)-1] = 49, then r = 1 + stepsInt(N(s)+1), where N(s)=sum_{i=0}^{len(s)-1}(s[i]-48)*2^{len(s)-1-i} and stepsInt(x) for an integer x >= 1 is the least t >= 0 such that T^t(x)=1, with T(1)=1, T(x)=x/2 for even x>1, and T(x)=x+1 for odd x>1.
  Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), s[i] is 48 or 49 (ASCII '0' or '1'); and s[0] = 49 (ASCII '1'). -/
theorem spec_8 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r)
    (hgt1 : 1 < s.val.length)
    (hlast : s.val[s.val.length - 1]? = some 49#u8) :
    r.val = 1 + (steps (N s + 1) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r)
    (hgt1 : 1 < s.val.length)
    (hlast : s.val[s.val.length - 1]? = some 49#u8), r.val = 1 + (steps (N s + 1) : Int)) := by
  sorry

/-- Whenever the function returns a result r and r > 0, if N(s)=sum_{i=0}^{len(s)-1}(s[i]-48)*2^{len(s)-1-i}, x_0=N(s), and x_{k+1}=T(x_k) for k=0,...,r-1 with T(1)=1, T(x)=x/2 for even x>1, and T(x)=x+1 for odd x>1, then x_{r-1}=2.
  Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), s[i] is 48 or 49 (ASCII '0' or '1'); and s[0] = 49 (ASCII '1'). -/
theorem spec_9 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (x : Nat → Int)
    (hres : num_steps s = ok r)
    (hpos : 0 < r.val)
    (hx0 : x 0 = N s)
    (hx : ∀ (k : Nat), k < r.val.toNat → x (k + 1) = T (x k)) :
    x (r.val.toNat - 1) = 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (x : Nat → Int)
    (hres : num_steps s = ok r)
    (hpos : 0 < r.val)
    (hx0 : x 0 = N s)
    (hx : ∀ (k : Nat), k < r.val.toNat → x (k + 1) = T (x k)), x (r.val.toNat - 1) = 2) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if len(s) = 1.
  Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), s[i] is 48 or 49 (ASCII '0' or '1'); and s[0] = 49 (ASCII '1'). -/
theorem spec_10 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r) :
    r.val = 0 ↔ s.val.length = 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (hres : num_steps s = ok r), r.val = 0 ↔ s.val.length = 1) := by
  sorry

/-- Whenever the function returns a result r, if N(s)=sum_{i=0}^{len(s)-1}(s[i]-48)*2^{len(s)-1-i}, x_0=N(s), and x_{k+1}=T(x_k) with T(1)=1, T(x)=x/2 for even x>1, and T(x)=x+1 for odd x>1, then for every integer k with 0 <= k <= r-2 and x_k > 1, we have x_{k+2} < x_k.
  Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), s[i] is 48 or 49 (ASCII '0' or '1'); and s[0] = 49 (ASCII '1'). -/
theorem spec_11 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (x : Nat → Int)
    (hres : num_steps s = ok r)
    (hx0 : x 0 = N s)
    (hx : ∀ (k : Nat), x (k + 1) = T (x k)) :
    ∀ (k : Nat), k + 2 ≤ r.val.toNat → 1 < x k → x (k + 2) < x k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500)
    (hdigits : ∀ (i : Nat) (_hi : i < s.val.length), s.val[i].val = 48 ∨ s.val[i].val = 49)
    (hfirst : s.val[0]? = some 49#u8)
    (r : Std.I64) (x : Nat → Int)
    (hres : num_steps s = ok r)
    (hx0 : x 0 = N s)
    (hx : ∀ (k : Nat), x (k + 1) = T (x k)), ∀ (k : Nat), k + 2 ≤ r.val.toNat → 1 < x k → x (k + 2) < x k) := by
  sorry

end AegisSpec.NumSteps
