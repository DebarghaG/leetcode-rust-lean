import Aegis.DistributeCookies.Code.Funs

/-!
# Specifications of `Aegis.DistributeCookies.distribute_cookies`

LeetCode problem `fair-distribution-of-cookies`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DistributeCookies

  def vals (cookies : Slice Std.I64) : List Int := cookies.val.map (fun x => x.val)

  def AllBounded (cs : List Int) : Prop := ∀ x ∈ cs, 1 ≤ x ∧ x ≤ 100000

  def listMax (cs : List Int) : Int := cs.foldr max 0

  def listSum (cs : List Int) : Int := cs.sum

  def childLoad {n : Nat} (cs : List Int) (assign : Fin n → Nat) (c : Nat) : Int :=
    (((List.finRange n).filter (fun i => assign i = c)).map (fun i => cs.getD i.val 0)).sum

  def maxLoad {n : Nat} (cs : List Int) (k : Nat) (assign : Fin n → Nat) : Int :=
    ((List.range k).map (fun c => childLoad cs assign c)).foldr max 0

  def subsetSum {n : Nat} (cs : List Int) (sel : Fin n → Bool) : Int :=
    (((List.finRange n).filter (fun i => sel i)).map (fun i => cs.getD i.val 0)).sum

  def loadFun {n k : Nat} (assign : Fin n → Fin k) : Fin n → Nat := fun i => (assign i).val

  def IsBestLoad (cs : List Int) (k : Nat) (r : Int) : Prop :=
    (∃ assign : Fin cs.length → Fin k, r = maxLoad cs k (loadFun assign)) ∧
      (∀ assign : Fin cs.length → Fin k, r ≤ maxLoad cs k (loadFun assign))

  def IsCeilDiv (a b m : Int) : Prop := a ≤ m * b ∧ (∀ m', a ≤ m' * b → m ≤ m')

  def TwoSmallest (cs : List Int) (a b : Int) : Prop :=
    ∃ s : List Int, s.length = cs.length ∧ List.Pairwise (· ≤ ·) s ∧ List.Perm s cs ∧
      a = s.getD 0 0 ∧ b = s.getD 1 0

  def permute (cs : List Int) (pi : Fin cs.length → Fin cs.length) : List Int :=
    (List.finRange cs.length).map (fun i => cs.get (pi i))

  /-- The function returns a result r and r equals the minimum, over all functions f from {0, 1, ..., len(cookies)-1} to {0, 1, ..., k-1}, of max_{c=0}^{k-1} (sum of cookies[i] over all i in {0, ..., len(cookies)-1} with f(i) = c). A function f is a distribution: it assigns each bag i to child f(i); a child c with no assigned bags has total 0.
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k <= len(cookies). -/
  theorem spec_1 (cookies : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)) :
      ∃ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r ∧
        IsBestLoad (vals cookies) k.val.toNat r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)), ∃ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r ∧
          IsBestLoad (vals cookies) k.val.toNat r.val) := by
    sorry

  /-- Whenever the preconditions hold, the function returns a result (it does not fail, panic, or overflow).
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k <= len(cookies). -/
  theorem spec_2 (cookies : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)) :
      ∃ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)), ∃ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= max_{0 <= i < len(cookies)} cookies[i].
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k <= len(cookies). -/
  theorem spec_3 (cookies : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)) :
      ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        listMax (vals cookies) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)), ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          listMax (vals cookies) ≤ r.val) := by
    sorry

  /-- Let total = sum_{i=0}^{len(cookies)-1} cookies[i] and maxc = max_{0 <= i < len(cookies)} cookies[i]. Whenever the function returns a result r, r <= max(maxc, total - maxc).
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k <= len(cookies). -/
  theorem spec_4 (cookies : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)) :
      ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        r.val ≤ max (listMax (vals cookies))
          (listSum (vals cookies) - listMax (vals cookies)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)), ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          r.val ≤ max (listMax (vals cookies))
            (listSum (vals cookies) - listMax (vals cookies))) := by
    sorry

  /-- Whenever the function returns a result r, there exists a function f from {0, ..., len(cookies)-1} to {0, ..., k-1} such that for every child c in {0, ..., k-1}, the sum of cookies[i] over all i with f(i) = c is at most r, and at least one child has sum exactly r.
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k <= len(cookies). -/
  theorem spec_5 (cookies : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)) :
      ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        ∃ assign : Fin (cookies.val.length) → Fin k.val.toNat,
          (∀ c : Fin k.val.toNat,
              childLoad (vals cookies) (loadFun assign) c.val ≤ r.val) ∧
            (∃ c : Fin k.val.toNat,
              childLoad (vals cookies) (loadFun assign) c.val = r.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)), ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          ∃ assign : Fin (cookies.val.length) → Fin k.val.toNat,
            (∀ c : Fin k.val.toNat,
                childLoad (vals cookies) (loadFun assign) c.val ≤ r.val) ∧
              (∃ c : Fin k.val.toNat,
                childLoad (vals cookies) (loadFun assign) c.val = r.val)) := by
    sorry

  /-- Whenever the function returns a result r, for every function f from {0, ..., len(cookies)-1} to {0, ..., k-1}, the maximum over c in {0, ..., k-1} of the sum of cookies[i] over all i with f(i) = c is at least r.
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k <= len(cookies). -/
  theorem spec_6 (cookies : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)) :
      ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        ∀ assign : Fin (cookies.val.length) → Fin k.val.toNat,
          r.val ≤ maxLoad (vals cookies) k.val.toNat (loadFun assign) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)), ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          ∀ assign : Fin (cookies.val.length) → Fin k.val.toNat,
            r.val ≤ maxLoad (vals cookies) k.val.toNat (loadFun assign)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a subset S of {0, ..., len(cookies)-1} such that sum_{i in S} cookies[i] = r.
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k <= len(cookies). -/
  theorem spec_7 (cookies : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)) :
      ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        ∃ sel : Fin (cookies.val.length) → Bool, r.val = subsetSum (vals cookies) sel := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)), ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          ∃ sel : Fin (cookies.val.length) → Bool, r.val = subsetSum (vals cookies) sel) := by
    sorry

  /-- Whenever the function returns a result r, r = max_{0 <= i < len(cookies)} cookies[i].
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; k = len(cookies). -/
  theorem spec_8 (cookies : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk : k.val = (cookies.val.length : Int)) :
      ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        r.val = listMax (vals cookies) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk : k.val = (cookies.val.length : Int)), ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          r.val = listMax (vals cookies)) := by
    sorry

  /-- Let a and b be the two smallest values among cookies, counted with multiplicity (if n = len(cookies) and s[0] <= s[1] <= ... <= s[n-1] is the sorted list of cookies, then a = s[0] and b = s[1]). Let maxc = max_{0 <= i < n} cookies[i]. Whenever the function returns a result r, r = max(maxc, a + b).
    Preconditions: 3 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; k = len(cookies) - 1. -/
  theorem spec_9 (cookies : Slice Std.I64) (k : Std.I64) (a b : Int)
      (hlen : 3 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk : k.val = (cookies.val.length : Int) - 1)
      (hab : TwoSmallest (vals cookies) a b) :
      ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        r.val = max (listMax (vals cookies)) (a + b) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64) (a b : Int)
        (hlen : 3 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk : k.val = (cookies.val.length : Int) - 1)
        (hab : TwoSmallest (vals cookies) a b), ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          r.val = max (listMax (vals cookies)) (a + b)) := by
    sorry

  /-- Whenever the function returns a result r, r = v * ceil(len(cookies) / k), where ceil(len(cookies) / k) is the smallest integer m such that m * k >= len(cookies).
    Preconditions: 2 <= len(cookies) <= 8; there exists v with 1 <= v <= 100000 such that cookies[i] = v for every i with 0 <= i < len(cookies); 2 <= k <= len(cookies). -/
  theorem spec_10 (cookies : Slice Std.I64) (k : Std.I64) (v : Int)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hv1 : 1 ≤ v) (hv2 : v ≤ 100000)
      (hconst : ∀ x ∈ cookies.val, x.val = v)
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)) :
      ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        ∃ m : Int, IsCeilDiv (cookies.val.length : Int) k.val m ∧ r.val = v * m := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64) (v : Int)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hv1 : 1 ≤ v) (hv2 : v ≤ 100000)
        (hconst : ∀ x ∈ cookies.val, x.val = v)
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)), ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          ∃ m : Int, IsCeilDiv (cookies.val.length : Int) k.val m ∧ r.val = v * m) := by
    sorry

  /-- Whenever the function returns a result r, r = maxc.
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k <= len(cookies); let maxc = max_{0 <= i < len(cookies)} cookies[i] and total = sum_{i=0}^{len(cookies)-1} cookies[i]; assume maxc >= total - maxc. -/
  theorem spec_11 (cookies : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int))
      (hdom : listSum (vals cookies) - listMax (vals cookies) ≤ listMax (vals cookies)) :
      ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        r.val = listMax (vals cookies) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int))
        (hdom : listSum (vals cookies) - listMax (vals cookies) ≤ listMax (vals cookies)), ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          r.val = listMax (vals cookies)) := by
    sorry

  /-- Whenever the function returns a result r on input (cookies, k) and a result r' on input (cookies', k), we have r = r'.
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k <= len(cookies); pi is a permutation of {0, ..., len(cookies)-1}; cookies' is defined by cookies'[i] = cookies[pi(i)] for every i. -/
  theorem spec_12 (cookies cookies' : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int))
      (hperm : ∃ pi : Fin (vals cookies).length → Fin (vals cookies).length,
        Function.Bijective pi ∧ vals cookies' = permute (vals cookies) pi) :
      ∀ r r', Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        Aegis.DistributeCookies.distribute_cookies cookies' k = ok r' → r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (cookies cookies' : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int))
        (hperm : ∃ pi : Fin (vals cookies).length → Fin (vals cookies).length,
          Function.Bijective pi ∧ vals cookies' = permute (vals cookies) pi), ∀ r r', Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          Aegis.DistributeCookies.distribute_cookies cookies' k = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns r on input (cookies, k) and r' on input (cookies', k), we have r <= r'.
    Preconditions: Let n = len(cookies) = len(cookies'). 2 <= n <= 8; for every i with 0 <= i < n, 1 <= cookies[i] <= 100000 and 1 <= cookies'[i] <= 100000; cookies[i] <= cookies'[i] for every i with 0 <= i < n; 2 <= k <= n. -/
  theorem spec_13 (cookies cookies' : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies)) (hb' : AllBounded (vals cookies'))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int))
      (hlen' : (vals cookies').length = (vals cookies).length)
      (hmono : ∀ i, i < (vals cookies).length →
        (vals cookies).getD i 0 ≤ (vals cookies').getD i 0) :
      ∀ r r', Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        Aegis.DistributeCookies.distribute_cookies cookies' k = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (cookies cookies' : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies)) (hb' : AllBounded (vals cookies'))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int))
        (hlen' : (vals cookies').length = (vals cookies).length)
        (hmono : ∀ i, i < (vals cookies).length →
          (vals cookies).getD i 0 ≤ (vals cookies').getD i 0), ∀ r r', Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          Aegis.DistributeCookies.distribute_cookies cookies' k = ok r' → r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function returns r1 on input (cookies, k1) and r2 on input (cookies, k2), we have r2 <= r1.
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k1 <= k2 <= len(cookies). -/
  theorem spec_14 (cookies : Slice Std.I64) (k1 k2 : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk1 : 2 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
      (hk2n : k2.val ≤ (cookies.val.length : Int)) :
      ∀ r1 r2, Aegis.DistributeCookies.distribute_cookies cookies k1 = ok r1 →
        Aegis.DistributeCookies.distribute_cookies cookies k2 = ok r2 → r2.val ≤ r1.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k1 k2 : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk1 : 2 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
        (hk2n : k2.val ≤ (cookies.val.length : Int)), ∀ r1 r2, Aegis.DistributeCookies.distribute_cookies cookies k1 = ok r1 →
          Aegis.DistributeCookies.distribute_cookies cookies k2 = ok r2 → r2.val ≤ r1.val) := by
    sorry

  /-- Whenever the function returns r on input (cookies, k) and r' on input (cookies', k), we have r' = c * r.
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k <= len(cookies); c is a positive integer; define cookies'[i] = c * cookies[i] for every i; assume 1 <= cookies'[i] <= 100000 for every i. -/
  theorem spec_15 (cookies cookies' : Slice Std.I64) (k : Std.I64) (c : Int)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies)) (hb' : AllBounded (vals cookies'))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int))
      (hc : 1 ≤ c)
      (hlen' : (vals cookies').length = (vals cookies).length)
      (hscale : ∀ i, i < (vals cookies).length →
        (vals cookies').getD i 0 = c * (vals cookies).getD i 0) :
      ∀ r r', Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        Aegis.DistributeCookies.distribute_cookies cookies' k = ok r' → r'.val = c * r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (cookies cookies' : Slice Std.I64) (k : Std.I64) (c : Int)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies)) (hb' : AllBounded (vals cookies'))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int))
        (hc : 1 ≤ c)
        (hlen' : (vals cookies').length = (vals cookies).length)
        (hscale : ∀ i, i < (vals cookies).length →
          (vals cookies').getD i 0 = c * (vals cookies).getD i 0), ∀ r r', Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          Aegis.DistributeCookies.distribute_cookies cookies' k = ok r' → r'.val = c * r.val) := by
    sorry

  /-- Let total = sum_{i=0}^{len(cookies)-1} cookies[i]. Whenever the function returns a result r, r >= ceil(total / k), where ceil(total / k) is the smallest integer m such that m * k >= total.
    Preconditions: 2 <= len(cookies) <= 8; for every i with 0 <= i < len(cookies), 1 <= cookies[i] <= 100000; 2 <= k <= len(cookies). -/
  theorem spec_16 (cookies : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
      (hb : AllBounded (vals cookies))
      (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)) :
      ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
        ∃ m : Int, IsCeilDiv (listSum (vals cookies)) k.val m ∧ m ≤ r.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (cookies : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ cookies.val.length) (hlen8 : cookies.val.length ≤ 8)
        (hb : AllBounded (vals cookies))
        (hk2 : 2 ≤ k.val) (hkn : k.val ≤ (cookies.val.length : Int)), ∀ r, Aegis.DistributeCookies.distribute_cookies cookies k = ok r →
          ∃ m : Int, IsCeilDiv (listSum (vals cookies)) k.val m ∧ m ≤ r.val) := by
    sorry

  end AegisSpec.DistributeCookies
