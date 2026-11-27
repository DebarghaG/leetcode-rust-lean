import Aegis.MaxActiveSectionsAfterTrade.Code.Funs

/-!
# Specifications of `Aegis.MaxActiveSectionsAfterTrade.max_active_sections_after_trade`

LeetCode problem `maximize-active-section-with-trade-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxActiveSectionsAfterTrade

  open Aegis.MaxActiveSectionsAfterTrade (max_active_sections_after_trade)

  def byte_zero : Std.U8 := 48#u8

  def byte_one : Std.U8 := 49#u8

  def IsBit (b : Std.U8) : Prop := b.val = 48 ∨ b.val = 49

  def IsBitString (l : List Std.U8) : Prop := ∀ b ∈ l, IsBit b

  def oneCount (l : List Std.U8) : Nat := l.countP (fun b => b.val == 49)

  def BlockIs (l : List Std.U8) (a b : Nat) (v : Std.U8) : Prop :=
    ∀ i, a ≤ i → i ≤ b → l[i]? = some v

  def overwrite (l : List Std.U8) (a k : Nat) (v : Std.U8) : List Std.U8 :=
    l.take a ++ List.replicate k v ++ l.drop (a + k)

  def augment (s : List Std.U8) : List Std.U8 := byte_one :: (s ++ [byte_one])

  def Move1 (t t1 : List Std.U8) : Prop :=
    ∃ a b : Nat,
      0 < a ∧ a ≤ b ∧ b + 1 < t.length ∧ BlockIs t a b byte_one ∧
        t[a - 1]? = some byte_zero ∧ t[b + 1]? = some byte_zero ∧
        t1 = overwrite t a (b + 1 - a) byte_zero

  def Move2 (t1 t2 : List Std.U8) : Prop :=
    ∃ c d : Nat,
      0 < c ∧ c ≤ d ∧ d + 1 < t1.length ∧ BlockIs t1 c d byte_zero ∧
        t1[c - 1]? = some byte_one ∧ t1[d + 1]? = some byte_one ∧
        t2 = overwrite t1 c (d + 1 - c) byte_one

  def Trade (s u : List Std.U8) : Prop :=
    ∃ t1 t2 : List Std.U8, Move1 (augment s) t1 ∧ Move2 t1 t2 ∧ u = (t2.drop 1).dropLast

  def TradeCandidate (s u : List Std.U8) : Prop :=
    u.length = s.length ∧ IsBitString u ∧ (u = s ∨ Trade s u)

  def IsMaxOneRun (l : List Std.U8) (p q : Nat) : Prop :=
    p ≤ q ∧ q < l.length ∧ BlockIs l p q byte_one ∧
      (p = 0 ∨ l[p - 1]? ≠ some byte_one) ∧
      (q + 1 = l.length ∨ l[q + 1]? ≠ some byte_one)

  def SurroundedOneRun (l : List Std.U8) (p q : Nat) : Prop :=
    IsMaxOneRun l p q ∧ 0 < p ∧ q + 1 < l.length ∧
      l[p - 1]? = some byte_zero ∧ l[q + 1]? = some byte_zero

  def ZeroRunBefore (l : List Std.U8) (p L : Nat) : Prop :=
    0 < L ∧ BlockIs l (p - L) (p - 1) byte_zero ∧
      (p - L = 0 ∨ l[p - L - 1]? = some byte_one)

  def ZeroRunAfter (l : List Std.U8) (q R : Nat) : Prop :=
    0 < R ∧ BlockIs l (q + 1) (q + R) byte_zero ∧
      (q + R = l.length - 1 ∨ l[q + R + 1]? = some byte_one)

  /-- The function returns a result r. Let c be the integer value of r, and for any string x let c1(x) = #{i | 0 <= i < len(x) and x[i] = '1'}. Then c is the maximum of c1(u) over all strings u of length len(s) over {'0','1'} that are obtained from s by at most one valid trade, defined as follows. Put t = '1' ++ s ++ '1'. A valid trade either does nothing (u = s), or: choose a nonempty contiguous index block [a,b] of t such that t[a..b] are all '1', a > 0, b+1 < len(t), t[a-1] = '0', and t[b+1] = '0'; replace t[a..b] by '0', obtaining t1; then choose a nonempty contiguous index block [c,d] of t1 such that t1[c..d] are all '0', c > 0, d+1 < len(t1), t1[c-1] = '1', and t1[d+1] = '1'; replace t1[c..d] by '1', obtaining t2; and set u to be the string obtained from t2 by deleting its first and last bytes.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) :
      ∃ r : Std.I64,
        max_active_sections_after_trade s = ok r ∧
          (∀ u : List Std.U8, TradeCandidate s.val u → (oneCount u : Int) ≤ r.val) ∧
          (∃ u : List Std.U8, TradeCandidate s.val u ∧ (oneCount u : Int) = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val), ∃ r : Std.I64,
          max_active_sections_after_trade s = ok r ∧
            (∀ u : List Std.U8, TradeCandidate s.val u → (oneCount u : Int) ≤ r.val) ∧
            (∃ u : List Std.U8, TradeCandidate s.val u ∧ (oneCount u : Int) = r.val)) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access out of bounds.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) :
      ∃ r : Std.I64, max_active_sections_after_trade s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val), ∃ r : Std.I64, max_active_sections_after_trade s = ok r) := by
    sorry

  /-- Whenever the function returns a result r with integer value c, 0 <= c <= len(s).
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) (r : Std.I64)
      (hr : max_active_sections_after_trade s = ok r) :
      0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val) (r : Std.I64)
        (hr : max_active_sections_after_trade s = ok r), 0 ≤ r.val ∧ r.val ≤ (s.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r with integer value c, c >= c1(s), where c1(s) = #{i | 0 <= i < len(s) and s[i] = '1'}.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) (r : Std.I64)
      (hr : max_active_sections_after_trade s = ok r) :
      (oneCount s.val : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val) (r : Std.I64)
        (hr : max_active_sections_after_trade s = ok r), (oneCount s.val : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r with integer value c, if there exists a maximal contiguous run of '1's in s with a byte immediately before it in s equal to '0' and a byte immediately after it in s equal to '0', then c >= c1(s) + 2, where c1(s) = #{i | 0 <= i < len(s) and s[i] = '1'}.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) (r : Std.I64)
      (hr : max_active_sections_after_trade s = ok r)
      (hsurrounded : ∃ p q : Nat, SurroundedOneRun s.val p q) :
      (oneCount s.val : Int) + 2 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val) (r : Std.I64)
        (hr : max_active_sections_after_trade s = ok r)
        (hsurrounded : ∃ p q : Nat, SurroundedOneRun s.val p q), (oneCount s.val : Int) + 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r with integer value c, if s[i] = '0' for every 0 <= i < len(s), then c = 0.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) (r : Std.I64)
      (hr : max_active_sections_after_trade s = ok r)
      (hzero : ∀ b ∈ s.val, b.val = 48) :
      r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val) (r : Std.I64)
        (hr : max_active_sections_after_trade s = ok r)
        (hzero : ∀ b ∈ s.val, b.val = 48), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r with integer value c, if s[i] = '1' for every 0 <= i < len(s), then c = len(s).
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) (r : Std.I64)
      (hr : max_active_sections_after_trade s = ok r)
      (hone : ∀ b ∈ s.val, b.val = 49) :
      r.val = (s.val.length : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val) (r : Std.I64)
        (hr : max_active_sections_after_trade s = ok r)
        (hone : ∀ b ∈ s.val, b.val = 49), r.val = (s.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r with integer value c, if len(s) = 1 then c = 1 when s[0] = '1', and c = 0 when s[0] = '0'.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) (r : Std.I64)
      (hr : max_active_sections_after_trade s = ok r)
      (hsole : s.val.length = 1) :
      (s.val[0]? = some byte_one → r.val = 1) ∧
        (s.val[0]? = some byte_zero → r.val = 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val) (r : Std.I64)
        (hr : max_active_sections_after_trade s = ok r)
        (hsole : s.val.length = 1), (s.val[0]? = some byte_one → r.val = 1) ∧
          (s.val[0]? = some byte_zero → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r with integer value c, if no maximal contiguous run of '1's in s has both a byte immediately before the run in s and a byte immediately after the run in s equal to '0', then c = c1(s), where c1(s) = #{i | 0 <= i < len(s) and s[i] = '1'}.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_9 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) (r : Std.I64)
      (hr : max_active_sections_after_trade s = ok r)
      (hnone : ¬ ∃ p q : Nat, SurroundedOneRun s.val p q) :
      r.val = (oneCount s.val : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val) (r : Std.I64)
        (hr : max_active_sections_after_trade s = ok r)
        (hnone : ¬ ∃ p q : Nat, SurroundedOneRun s.val p q), r.val = (oneCount s.val : Int)) := by
    sorry

  /-- Whenever the function returns a result r with integer value c, suppose exactly one maximal contiguous run of '1's in s is surrounded by '0's. Let p and q be the first and last indices of that run, so s[p..q] are '1', p > 0, q+1 < len(s), s[p-1] = '0', and s[q+1] = '0'. Let L be the unique positive integer such that s[p-L..p-1] are all '0' and (p-L = 0 or s[p-L-1] = '1'), and let R be the unique positive integer such that s[q+1..q+R] are all '0' and (q+R = len(s)-1 or s[q+R+1] = '1'). Then c = c1(s) + L + R, where c1(s) = #{i | 0 <= i < len(s) and s[i] = '1'}.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_10 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) (r : Std.I64)
      (hr : max_active_sections_after_trade s = ok r)
      (p q : Nat) (hrun : SurroundedOneRun s.val p q)
      (hunique : ∀ p' q', SurroundedOneRun s.val p' q' → p' = p ∧ q' = q)
      (L R : Nat) (hL : ZeroRunBefore s.val p L) (hR : ZeroRunAfter s.val q R) :
      r.val = (oneCount s.val : Int) + (L : Int) + (R : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val) (r : Std.I64)
        (hr : max_active_sections_after_trade s = ok r)
        (p q : Nat) (hrun : SurroundedOneRun s.val p q)
        (hunique : ∀ p' q', SurroundedOneRun s.val p' q' → p' = p ∧ q' = q)
        (L R : Nat) (hL : ZeroRunBefore s.val p L) (hR : ZeroRunAfter s.val q R), r.val = (oneCount s.val : Int) + (L : Int) + (R : Int)) := by
    sorry

  /-- Whenever the function returns a result r with integer value c, there exists a string u of length len(s) over {'0','1'} such that c1(u) = c, where c1(u) = #{i | 0 <= i < len(u) and u[i] = '1'}, and u is obtained from s by at most one valid trade as follows: put t = '1' ++ s ++ '1'; either u = s, or replace a nonempty contiguous block of '1's in t having immediate neighbors '0' by '0's, then replace a nonempty contiguous block of '0's in the resulting string having immediate neighbors '1' by '1's, and delete the first and last augmented bytes.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_11 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) (r : Std.I64)
      (hr : max_active_sections_after_trade s = ok r) :
      ∃ u : List Std.U8, TradeCandidate s.val u ∧ (oneCount u : Int) = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val) (r : Std.I64)
        (hr : max_active_sections_after_trade s = ok r), ∃ u : List Std.U8, TradeCandidate s.val u ∧ (oneCount u : Int) = r.val) := by
    sorry

  /-- For any two slices s and s' of the same length satisfying the preconditions, if s'[i] = s[len(s)-1-i] for every 0 <= i < len(s) so that s' is the left-to-right reversal of s, and if r and r' are the results returned on s and s' respectively, then the integer values of r and r' are equal.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_12 (s s' : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val)
      (hlen_ge' : 1 ≤ s'.val.length) (hlen_le' : s'.val.length ≤ 100000)
      (hbits' : IsBitString s'.val)
      (hlen_eq : s'.val.length = s.val.length)
      (hrev : ∀ i, i < s.val.length → s'.val[i]? = s.val[s.val.length - 1 - i]?)
      (r r' : Std.I64)
      (hr : max_active_sections_after_trade s = ok r)
      (hr' : max_active_sections_after_trade s' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s s' : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val)
        (hlen_ge' : 1 ≤ s'.val.length) (hlen_le' : s'.val.length ≤ 100000)
        (hbits' : IsBitString s'.val)
        (hlen_eq : s'.val.length = s.val.length)
        (hrev : ∀ i, i < s.val.length → s'.val[i]? = s.val[s.val.length - 1 - i]?)
        (r r' : Std.I64)
        (hr : max_active_sections_after_trade s = ok r)
        (hr' : max_active_sections_after_trade s' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r with integer value c, for every string u of length len(s) over {'0','1'} that is obtained from s by at most one valid trade as follows: put t = '1' ++ s ++ '1'; either u = s, or replace a nonempty contiguous block of '1's in t having immediate neighbors '0' by '0's, then replace a nonempty contiguous block of '0's in the resulting string having immediate neighbors '1' by '1's, and delete the first and last augmented bytes, we have c1(u) <= c, where c1(u) = #{i | 0 <= i < len(u) and u[i] = '1'}.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '0' or '1'. -/
  theorem spec_13 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbits : IsBitString s.val) (r : Std.I64)
      (hr : max_active_sections_after_trade s = ok r) :
      ∀ u : List Std.U8, TradeCandidate s.val u → (oneCount u : Int) ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbits : IsBitString s.val) (r : Std.I64)
        (hr : max_active_sections_after_trade s = ok r), ∀ u : List Std.U8, TradeCandidate s.val u → (oneCount u : Int) ≤ r.val) := by
    sorry

  end AegisSpec.MaxActiveSectionsAfterTrade
