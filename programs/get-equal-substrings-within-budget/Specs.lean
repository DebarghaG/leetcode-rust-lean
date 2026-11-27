import Aegis.EqualSubstring.Code.Funs

/-!
# Specifications of `Aegis.EqualSubstring.equal_substring`

LeetCode problem `get-equal-substrings-within-budget`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.EqualSubstring

  open Aegis.EqualSubstring (equal_substring)

  def byteCost (a b : Aeneas.Std.U8) : Int :=
    if a.val ≥ b.val then (a.val : Int) - (b.val : Int) else (b.val : Int) - (a.val : Int)

  def window (s : Aeneas.Std.Slice Aeneas.Std.U8) (a k : Nat) : List Aeneas.Std.U8 :=
    (s.val.drop a).take k

  def agreeAt (s t : Aeneas.Std.Slice Aeneas.Std.U8) (i : Nat) : Prop :=
    window s i 1 = window t i 1

  def gapAt (s t : Aeneas.Std.Slice Aeneas.Std.U8) (i : Nat) : Int :=
    ((window s i 1).zip (window t i 1)).map (fun p => byteCost p.1 p.2) |>.sum

  def cost (s t : Aeneas.Std.Slice Aeneas.Std.U8) (a b : Nat) : Int :=
    ((List.range (b - a)).map (fun k => gapAt s t (a + k))).sum

  def affordable (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (k : Nat) : Prop :=
    k ≤ s.val.length ∧
      ∃ a : Nat, a + k ≤ s.val.length ∧ cost s t a (a + k) ≤ maxCost.val

  def equalWindow (s t : Aeneas.Std.Slice Aeneas.Std.U8) (k : Nat) : Prop :=
    k ≤ s.val.length ∧
      ∃ a : Nat, a + k ≤ s.val.length ∧ ∀ i : Nat, a ≤ i → i < a + k → agreeAt s t i

  /-- Let n=len(s). For 0<=i<n define c(i)=|ascii(s[i])-ascii(t[i])|, and for 0<=a<=b<=n define C(a,b)=sum_{i=a}^{b-1} c(i), with C(a,a)=0. The function returns a result r such that r is the greatest integer k with 0<=k<=n for which there exists an integer a with 0<=a<=n-k and C(a,a+k)<=maxCost. Equivalently, r is the maximum length of a contiguous substring of s whose total cost to become the corresponding substring of t is at most maxCost; if no positive length is affordable, r=0 (the empty substring has cost 0).
    Preconditions: len(t)=len(s); 1<=len(s)<=10^5; 0<=maxCost<=10^6; every byte of s and t is an ASCII lowercase letter (code in 97..122). -/
  theorem spec_1 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
      (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        equal_substring s t maxCost = ok r ∧
        0 ≤ r.val ∧
        r.val ≤ (s.val.length : Int) ∧
        affordable s t maxCost r.val.toNat ∧
        (∀ k : Nat, affordable s t maxCost k → k ≤ r.val.toNat) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
        (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122), ∃ r : Aeneas.Std.I64,
          equal_substring s t maxCost = ok r ∧
          0 ≤ r.val ∧
          r.val ≤ (s.val.length : Int) ∧
          affordable s t maxCost r.val.toNat ∧
          (∀ k : Nat, affordable s t maxCost k → k ≤ r.val.toNat)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: len(t)=len(s); 1<=len(s)<=10^5; 0<=maxCost<=10^6; every byte of s and t is an ASCII lowercase letter (code in 97..122). -/
  theorem spec_2 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
      (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122) :
      ∃ r : Aeneas.Std.I64, equal_substring s t maxCost = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
        (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122), ∃ r : Aeneas.Std.I64, equal_substring s t maxCost = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(s).
    Preconditions: len(t)=len(s); 1<=len(s)<=10^5; 0<=maxCost<=10^6; every byte of s and t is an ASCII lowercase letter (code in 97..122). -/
  theorem spec_3 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
      (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122) :
      ∀ r : Aeneas.Std.I64, equal_substring s t maxCost = ok r →
        0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
        (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122), ∀ r : Aeneas.Std.I64, equal_substring s t maxCost = ok r →
          0 ≤ r.val ∧ r.val ≤ (s.val.length : Int)) := by
    sorry

  /-- Let n=len(s). The returned value r equals the length of the longest contiguous block of indices i for which s[i]=t[i]; explicitly, r is the greatest integer k with 0<=k<=n such that there exists an integer a with 0<=a<=n-k and s[i]=t[i] for every i satisfying a<=i<a+k.
    Preconditions: len(t)=len(s); 1<=len(s)<=10^5; maxCost=0; every byte of s and t is an ASCII lowercase letter (code in 97..122). -/
  theorem spec_4 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
      (hcost : maxCost.val = 0)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        equal_substring s t maxCost = ok r ∧
        0 ≤ r.val ∧
        r.val ≤ (s.val.length : Int) ∧
        equalWindow s t r.val.toNat ∧
        (∀ k : Nat, equalWindow s t k → k ≤ r.val.toNat) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
        (hcost : maxCost.val = 0)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122), ∃ r : Aeneas.Std.I64,
          equal_substring s t maxCost = ok r ∧
          0 ≤ r.val ∧
          r.val ≤ (s.val.length : Int) ∧
          equalWindow s t r.val.toNat ∧
          (∀ k : Nat, equalWindow s t k → k ≤ r.val.toNat)) := by
    sorry

  /-- The function returns r = len(s).
    Preconditions: len(t)=len(s); 1<=len(s)<=10^5; 0<=maxCost<=10^6; every byte of s and t is an ASCII lowercase letter (code in 97..122); for every i with 0<=i<len(s), s[i]=t[i]. -/
  theorem spec_5 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
      (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hagree : ∀ i : Nat, i < s.val.length → agreeAt s t i) :
      ∃ r : Aeneas.Std.I64,
        equal_substring s t maxCost = ok r ∧ r.val = (s.val.length : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
        (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hagree : ∀ i : Nat, i < s.val.length → agreeAt s t i), ∃ r : Aeneas.Std.I64,
          equal_substring s t maxCost = ok r ∧ r.val = (s.val.length : Int)) := by
    sorry

  /-- The function returns a result r, and r=0 if and only if for every i with 0<=i<len(s), |ascii(s[i])-ascii(t[i])| > maxCost.
    Preconditions: len(t)=len(s); 1<=len(s)<=10^5; 0<=maxCost<=10^6; every byte of s and t is an ASCII lowercase letter (code in 97..122). -/
  theorem spec_6 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
      (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        equal_substring s t maxCost = ok r ∧
        (r.val = 0 ↔ ∀ i : Nat, i < s.val.length → maxCost.val < gapAt s t i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
        (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122), ∃ r : Aeneas.Std.I64,
          equal_substring s t maxCost = ok r ∧
          (r.val = 0 ↔ ∀ i : Nat, i < s.val.length → maxCost.val < gapAt s t i)) := by
    sorry

  /-- Let n=len(s) and let C = sum_{i=0}^{n-1} |ascii(s[i])-ascii(t[i])|. The function returns a result r, and r=n if and only if C <= maxCost.
    Preconditions: len(t)=len(s); 1<=len(s)<=10^5; 0<=maxCost<=10^6; every byte of s and t is an ASCII lowercase letter (code in 97..122). -/
  theorem spec_7 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
      (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        equal_substring s t maxCost = ok r ∧
        (r.val = (s.val.length : Int) ↔ cost s t 0 s.val.length ≤ maxCost.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
        (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122), ∃ r : Aeneas.Std.I64,
          equal_substring s t maxCost = ok r ∧
          (r.val = (s.val.length : Int) ↔ cost s t 0 s.val.length ≤ maxCost.val)) := by
    sorry

  /-- Let c = |ascii(s[0])-ascii(t[0])|. The function returns r=1 if c<=maxCost, and returns r=0 otherwise.
    Preconditions: len(t)=len(s); len(s)=1; 0<=maxCost<=10^6; every byte of s and t is an ASCII lowercase letter (code in 97..122). -/
  theorem spec_8 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hlen1 : s.val.length = 1)
      (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        equal_substring s t maxCost = ok r ∧
        ((gapAt s t 0 ≤ maxCost.val ∧ r.val = 1) ∨
         (maxCost.val < gapAt s t 0 ∧ r.val = 0)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hlen1 : s.val.length = 1)
        (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122), ∃ r : Aeneas.Std.I64,
          equal_substring s t maxCost = ok r ∧
          ((gapAt s t 0 ≤ maxCost.val ∧ r.val = 1) ∨
           (maxCost.val < gapAt s t 0 ∧ r.val = 0))) := by
    sorry

  /-- Whenever the function returns a result r with r>0, there exists an integer a such that 0<=a<=len(s)-r and sum_{i=a}^{a+r-1} |ascii(s[i])-ascii(t[i])| <= maxCost.
    Preconditions: len(t)=len(s); 1<=len(s)<=10^5; 0<=maxCost<=10^6; every byte of s and t is an ASCII lowercase letter (code in 97..122). -/
  theorem spec_9 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
      (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122) :
      ∀ r : Aeneas.Std.I64, equal_substring s t maxCost = ok r → 0 < r.val →
        ∃ a : Nat,
          a + r.val.toNat ≤ s.val.length ∧ cost s t a (a + r.val.toNat) ≤ maxCost.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
        (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122), ∀ r : Aeneas.Std.I64, equal_substring s t maxCost = ok r → 0 < r.val →
          ∃ a : Nat,
            a + r.val.toNat ≤ s.val.length ∧ cost s t a (a + r.val.toNat) ≤ maxCost.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with r<k<=len(s) and every integer a with 0<=a<=len(s)-k, we have sum_{i=a}^{a+k-1} |ascii(s[i])-ascii(t[i])| > maxCost.
    Preconditions: len(t)=len(s); 1<=len(s)<=10^5; 0<=maxCost<=10^6; every byte of s and t is an ASCII lowercase letter (code in 97..122). -/
  theorem spec_10 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
      (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122) :
      ∀ r : Aeneas.Std.I64, equal_substring s t maxCost = ok r →
        ∀ k : Nat, r.val < (k : Int) → k ≤ s.val.length →
          ∀ a : Nat, a + k ≤ s.val.length → maxCost.val < cost s t a (a + k) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
        (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122), ∀ r : Aeneas.Std.I64, equal_substring s t maxCost = ok r →
          ∀ k : Nat, r.val < (k : Int) → k ≤ s.val.length →
            ∀ a : Nat, a + k ≤ s.val.length → maxCost.val < cost s t a (a + k)) := by
    sorry

  /-- For any valid inputs s,t,maxCost, let r be the result returned by equal_substring(s,t,maxCost) and let r' be the result returned by equal_substring(t,s,maxCost). Both calls return results and r=r'.
    Preconditions: len(t)=len(s); 1<=len(s)<=10^5; 0<=maxCost<=10^6; every byte of s and t is an ASCII lowercase letter (code in 97..122). -/
  theorem spec_11 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
      (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122) :
      ∃ r r' : Aeneas.Std.I64,
        equal_substring s t maxCost = ok r ∧
        equal_substring t s maxCost = ok r' ∧
        r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (maxCost : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
        (hcost_lo : 0 ≤ maxCost.val) (hcost_hi : maxCost.val ≤ 1000000)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122), ∃ r r' : Aeneas.Std.I64,
          equal_substring s t maxCost = ok r ∧
          equal_substring t s maxCost = ok r' ∧
          r.val = r'.val) := by
    sorry

  /-- Let r1 be the result returned by equal_substring(s,t,m1) and let r2 be the result returned by equal_substring(s,t,m2). Both calls return results and r1<=r2.
    Preconditions: len(t)=len(s); 1<=len(s)<=10^5; every byte of s and t is an ASCII lowercase letter (code in 97..122); 0<=m1<=m2<=10^6. -/
  theorem spec_12 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (m1 m2 : Aeneas.Std.I64)
      (hlen : t.val.length = s.val.length)
      (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
      (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hm1 : 0 ≤ m1.val) (hm12 : m1.val ≤ m2.val) (hm2 : m2.val ≤ 1000000) :
      ∃ r1 r2 : Aeneas.Std.I64,
        equal_substring s t m1 = ok r1 ∧
        equal_substring s t m2 = ok r2 ∧
        r1.val ≤ r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (m1 m2 : Aeneas.Std.I64)
        (hlen : t.val.length = s.val.length)
        (hpos : 1 ≤ s.val.length) (hn : s.val.length ≤ 100000)
        (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hm1 : 0 ≤ m1.val) (hm12 : m1.val ≤ m2.val) (hm2 : m2.val ≤ 1000000), ∃ r1 r2 : Aeneas.Std.I64,
          equal_substring s t m1 = ok r1 ∧
          equal_substring s t m2 = ok r2 ∧
          r1.val ≤ r2.val) := by
    sorry

  end AegisSpec.EqualSubstring
