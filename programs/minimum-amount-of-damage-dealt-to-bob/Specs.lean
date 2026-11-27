import Aegis.MinDamage.Code.Funs

/-!
# Specifications of `Aegis.MinDamage.min_damage`

LeetCode problem `minimum-amount-of-damage-dealt-to-bob`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinDamage

  def ceilDiv (a b : Int) : Int := (a + b - 1) / b

  def contents (s : Slice I64) : List Int := s.val.map (fun x => x.val)

  def entry (s : Slice I64) (i : Nat) : Int := (contents s).getD i 0

  def turns (power : Int) (health : Slice I64) (i : Nat) : Int := ceilDiv (entry health i) power

  def IsPerm (n : Nat) (p : Nat → Nat) : Prop :=
    (∀ i, i < n → p i < n) ∧ ∀ i, i < n → ∀ j, j < n → p i = p j → i = j

  def cost (t d : Nat → Int) (n : Nat) (p : Nat → Nat) : Int :=
    ∑ k ∈ Finset.range n, t (p k) * ∑ j ∈ (Finset.range n).filter (fun j => k ≤ j), d (p j)

  def NonIncreasing (l : List Int) : Prop := l.Pairwise (fun a b => b ≤ a)

  def NonDecreasing (l : List Int) : Prop := l.Pairwise (fun a b => a ≤ b)

  /-- Whenever min_damage(power, damage, health) returns a result r, define t_i = ceil(health[i]/power) for 0<=i<n, i.e. the least positive integer k with k*power>=health[i]. For a permutation p=(p_0,...,p_{n-1}) of {0,...,n-1}, define T(p) = sum_{k=0}^{n-1} t_{p_k} * (sum_{j=k}^{n-1} damage[p_j]). Then r = min { T(p) | p is a permutation of {0,...,n-1} }.
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power<=10^4, and for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4. -/
  theorem spec_1 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r) :
      (∃ p, IsPerm n p ∧ cost (turns power.val health) (fun i => entry damage i) n p = r.val) ∧
        ∀ p, IsPerm n p → r.val ≤ cost (turns power.val health) (fun i => entry damage i) n p := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r), (∃ p, IsPerm n p ∧ cost (turns power.val health) (fun i => entry damage i) n p = r.val) ∧
          ∀ p, IsPerm n p → r.val ≤ cost (turns power.val health) (fun i => entry damage i) n p) := by
    sorry

  /-- The call min_damage(power, damage, health) returns a result (some Result.ok value); it does not fail with overflow, out-of-bounds, or panic.
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power<=10^4, and for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4. -/
  theorem spec_2 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4) :
      ∃ r : I64, Aegis.MinDamage.min_damage power damage health = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4), ∃ r : I64, Aegis.MinDamage.min_damage power damage health = ok r) := by
    sorry

  /-- Whenever the call returns a result r, with t_i = ceil(health[i]/power), we have r >= sum_{i=0}^{n-1} damage[i] * t_i.
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power<=10^4, and for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4. -/
  theorem spec_3 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r) :
      r.val ≥ ∑ i ∈ Finset.range n, entry damage i * turns power.val health i := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r), r.val ≥ ∑ i ∈ Finset.range n, entry damage i * turns power.val health i) := by
    sorry

  /-- Whenever the call returns a result r, let T = sum_{i=0}^{n-1} ceil(health[i]/power). Then r <= (sum_{i=0}^{n-1} damage[i]) * T.
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power<=10^4, and for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4. -/
  theorem spec_4 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r) :
      r.val ≤
        (∑ i ∈ Finset.range n, entry damage i) * ∑ i ∈ Finset.range n, turns power.val health i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r), r.val ≤
          (∑ i ∈ Finset.range n, entry damage i) * ∑ i ∈ Finset.range n, turns power.val health i) := by
    sorry

  /-- Whenever the call returns r, r = damage[0] * ceil(health[0]/power).
    Preconditions: len(damage)=len(health)=n, n=1, 1<=power<=10^4, 1<=damage[0]<=10^4, and 1<=health[0]<=10^4. -/
  theorem spec_5 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn : n = 1)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam0_lo : 1 ≤ entry damage 0) (hdam0_hi : entry damage 0 ≤ 10 ^ 4)
      (hhea0_lo : 1 ≤ entry health 0) (hhea0_hi : entry health 0 ≤ 10 ^ 4)
      (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r) :
      r.val = entry damage 0 * turns power.val health 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn : n = 1)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam0_lo : 1 ≤ entry damage 0) (hdam0_hi : entry damage 0 ≤ 10 ^ 4)
        (hhea0_lo : 1 ≤ entry health 0) (hhea0_hi : entry health 0 ≤ 10 ^ 4)
        (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r), r.val = entry damage 0 * turns power.val health 0) := by
    sorry

  /-- Let d_(0) >= d_(1) >= ... >= d_(n-1) be the values damage[0],...,damage[n-1] sorted in non-increasing order. Whenever the call returns r, r = sum_{j=0}^{n-1} (j+1) * d_(j).
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power<=10^4, for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4, and for every i with 0<=i<n, health[i]<=power. -/
  theorem spec_6 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (hsmall : ∀ i, i < n → entry health i ≤ power.val)
      (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r) :
      ∃ ds : List Int, NonIncreasing ds ∧ ds.Perm (contents damage) ∧ ds.length = n ∧
        r.val = ∑ j ∈ Finset.range n, ((j : Int) + 1) * ds.getD j 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (hsmall : ∀ i, i < n → entry health i ≤ power.val)
        (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r), ∃ ds : List Int, NonIncreasing ds ∧ ds.Perm (contents damage) ∧ ds.length = n ∧
          r.val = ∑ j ∈ Finset.range n, ((j : Int) + 1) * ds.getD j 0) := by
    sorry

  /-- Let t_i = ceil(health[i]/power), and let t_(0) <= t_(1) <= ... <= t_(n-1) be these values sorted in non-decreasing order. Whenever the call returns r, r = D * sum_{j=0}^{n-1} t_(j) * (n-j).
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power<=10^4, for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4, and there exists D with damage[i]=D for every i with 0<=i<n. -/
  theorem spec_7 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (D : Int) (hD : ∀ i, i < n → entry damage i = D)
      (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r) :
      ∃ ts : List Int, NonDecreasing ts ∧ ts.Perm ((List.range n).map (turns power.val health)) ∧
        ts.length = n ∧
        r.val = D * ∑ j ∈ Finset.range n, ts.getD j 0 * ((n : Int) - (j : Int)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (D : Int) (hD : ∀ i, i < n → entry damage i = D)
        (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r), ∃ ts : List Int, NonDecreasing ts ∧ ts.Perm ((List.range n).map (turns power.val health)) ∧
          ts.length = n ∧
          r.val = D * ∑ j ∈ Finset.range n, ts.getD j 0 * ((n : Int) - (j : Int))) := by
    sorry

  /-- Let t = ceil(h/power), and let d_(0) >= d_(1) >= ... >= d_(n-1) be the values damage[0],...,damage[n-1] sorted in non-increasing order. Whenever the call returns r, r = t * sum_{j=0}^{n-1} (j+1) * d_(j).
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power<=10^4, for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4, and there exists h with health[i]=h for every i with 0<=i<n. -/
  theorem spec_8 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (h : Int) (hh : ∀ i, i < n → entry health i = h)
      (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r) :
      ∃ ds : List Int, NonIncreasing ds ∧ ds.Perm (contents damage) ∧ ds.length = n ∧
        r.val = ceilDiv h power.val * ∑ j ∈ Finset.range n, ((j : Int) + 1) * ds.getD j 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (h : Int) (hh : ∀ i, i < n → entry health i = h)
        (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r), ∃ ds : List Int, NonIncreasing ds ∧ ds.Perm (contents damage) ∧ ds.length = n ∧
          r.val = ceilDiv h power.val * ∑ j ∈ Finset.range n, ((j : Int) + 1) * ds.getD j 0) := by
    sorry

  /-- Whenever min_damage(power, damage, health) returns r and min_damage(power, damage', health') returns r', we have r = r'.
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power<=10^4, for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4. Also let sigma be any permutation of {0,...,n-1}, and define damage'[i]=damage[sigma(i)] and health'[i]=health[sigma(i)] for 0<=i<n. -/
  theorem spec_9 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (sigma : Nat → Nat) (hsigma : IsPerm n sigma)
      (damage' health' : Slice I64)
      (hdam' : contents damage' = (List.range n).map (fun i => entry damage (sigma i)))
      (hhea' : contents health' = (List.range n).map (fun i => entry health (sigma i)))
      (r r' : I64)
      (hr : Aegis.MinDamage.min_damage power damage health = ok r)
      (hr' : Aegis.MinDamage.min_damage power damage' health' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (sigma : Nat → Nat) (hsigma : IsPerm n sigma)
        (damage' health' : Slice I64)
        (hdam' : contents damage' = (List.range n).map (fun i => entry damage (sigma i)))
        (hhea' : contents health' = (List.range n).map (fun i => entry health (sigma i)))
        (r r' : I64)
        (hr : Aegis.MinDamage.min_damage power damage health = ok r)
        (hr' : Aegis.MinDamage.min_damage power damage' health' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever min_damage(power, damage, health) returns r and min_damage(power, damage', health) returns r', we have r' = c * r.
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power<=10^4, for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4. Also let c be an integer with 1<=c and 1<=c*damage[i]<=10^4 for every i, and define damage'[i]=c*damage[i]. -/
  theorem spec_10 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (c : Int) (hc_lo : 1 ≤ c)
      (hc_dam : ∀ i, i < n → 1 ≤ c * entry damage i ∧ c * entry damage i ≤ 10 ^ 4)
      (damage' : Slice I64)
      (hdam' : contents damage' = (contents damage).map (fun x => c * x))
      (r r' : I64)
      (hr : Aegis.MinDamage.min_damage power damage health = ok r)
      (hr' : Aegis.MinDamage.min_damage power damage' health = ok r') :
      r'.val = c * r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (c : Int) (hc_lo : 1 ≤ c)
        (hc_dam : ∀ i, i < n → 1 ≤ c * entry damage i ∧ c * entry damage i ≤ 10 ^ 4)
        (damage' : Slice I64)
        (hdam' : contents damage' = (contents damage).map (fun x => c * x))
        (r r' : I64)
        (hr : Aegis.MinDamage.min_damage power damage health = ok r)
        (hr' : Aegis.MinDamage.min_damage power damage' health = ok r'), r'.val = c * r.val) := by
    sorry

  /-- Whenever min_damage(power, damage, health) returns r and min_damage(power', damage, health') returns r', we have r' = r.
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power<=10^4, for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4. Also let c be an integer with 1<=c, c*power<=10^4, and 1<=c*health[i]<=10^4 for every i. Define power'=c*power and health'[i]=c*health[i]. -/
  theorem spec_11 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (c : Int) (hc_lo : 1 ≤ c) (hc_pow : c * power.val ≤ 10 ^ 4)
      (hc_hea : ∀ i, i < n → 1 ≤ c * entry health i ∧ c * entry health i ≤ 10 ^ 4)
      (power' : I64) (hpow' : power'.val = c * power.val)
      (health' : Slice I64)
      (hhea' : contents health' = (contents health).map (fun x => c * x))
      (r r' : I64)
      (hr : Aegis.MinDamage.min_damage power damage health = ok r)
      (hr' : Aegis.MinDamage.min_damage power' damage health' = ok r') :
      r'.val = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (c : Int) (hc_lo : 1 ≤ c) (hc_pow : c * power.val ≤ 10 ^ 4)
        (hc_hea : ∀ i, i < n → 1 ≤ c * entry health i ∧ c * entry health i ≤ 10 ^ 4)
        (power' : I64) (hpow' : power'.val = c * power.val)
        (health' : Slice I64)
        (hhea' : contents health' = (contents health).map (fun x => c * x))
        (r r' : I64)
        (hr : Aegis.MinDamage.min_damage power damage health = ok r)
        (hr' : Aegis.MinDamage.min_damage power' damage health' = ok r'), r'.val = r.val) := by
    sorry

  /-- Whenever min_damage(power, damage, health) returns r, there exists a permutation p=(p_0,...,p_{n-1}) of {0,...,n-1} such that, with t_i=ceil(health[i]/power) and T(p)=sum_{k=0}^{n-1} t_{p_k}*(sum_{j=k}^{n-1} damage[p_j]), we have T(p)=r and, for all 0<=a<b<n, t_{p_a}*damage[p_b] <= t_{p_b}*damage[p_a].
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power<=10^4, and for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4. -/
  theorem spec_12 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r) :
      ∃ p, IsPerm n p ∧ cost (turns power.val health) (fun i => entry damage i) n p = r.val ∧
        ∀ a b, a < b → b < n →
          turns power.val health (p a) * entry damage (p b) ≤
            turns power.val health (p b) * entry damage (p a) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (r : I64) (hr : Aegis.MinDamage.min_damage power damage health = ok r), ∃ p, IsPerm n p ∧ cost (turns power.val health) (fun i => entry damage i) n p = r.val ∧
          ∀ a b, a < b → b < n →
            turns power.val health (p a) * entry damage (p b) ≤
              turns power.val health (p b) * entry damage (p a)) := by
    sorry

  /-- Whenever min_damage(power, damage, health) returns r and min_damage(power, damage', health') returns r', we have r' > r.
    Preconditions: len(damage)=len(health)=n, 1<=n<10^5, 1<=power<=10^4, for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4. Also let d,h be integers with 1<=d<=10^4 and 1<=h<=10^4, and define damage' = damage with d appended and health' = health with h appended. -/
  theorem spec_13 (power : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n < 10 ^ 5)
      (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (d h : Int) (hd_lo : 1 ≤ d) (hd_hi : d ≤ 10 ^ 4) (hh_lo : 1 ≤ h) (hh_hi : h ≤ 10 ^ 4)
      (damage' health' : Slice I64)
      (hdam' : contents damage' = contents damage ++ [d])
      (hhea' : contents health' = contents health ++ [h])
      (r r' : I64)
      (hr : Aegis.MinDamage.min_damage power damage health = ok r)
      (hr' : Aegis.MinDamage.min_damage power damage' health' = ok r') :
      r'.val > r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (power : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n < 10 ^ 5)
        (hpow_lo : 1 ≤ power.val) (hpow_hi : power.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (d h : Int) (hd_lo : 1 ≤ d) (hd_hi : d ≤ 10 ^ 4) (hh_lo : 1 ≤ h) (hh_hi : h ≤ 10 ^ 4)
        (damage' health' : Slice I64)
        (hdam' : contents damage' = contents damage ++ [d])
        (hhea' : contents health' = contents health ++ [h])
        (r r' : I64)
        (hr : Aegis.MinDamage.min_damage power damage health = ok r)
        (hr' : Aegis.MinDamage.min_damage power damage' health' = ok r'), r'.val > r.val) := by
    sorry

  /-- Whenever min_damage(power1, damage, health) returns r1 and min_damage(power2, damage, health) returns r2, we have r2 <= r1.
    Preconditions: len(damage)=len(health)=n, 1<=n<=10^5, 1<=power1<=power2<=10^4, and for every i with 0<=i<n, 1<=damage[i]<=10^4 and 1<=health[i]<=10^4. -/
  theorem spec_14 (power1 power2 : I64) (damage health : Slice I64) (n : Nat)
      (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hp1_lo : 1 ≤ power1.val) (hp_le : power1.val ≤ power2.val) (hp2_hi : power2.val ≤ 10 ^ 4)
      (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
      (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
      (r1 r2 : I64)
      (hr1 : Aegis.MinDamage.min_damage power1 damage health = ok r1)
      (hr2 : Aegis.MinDamage.min_damage power2 damage health = ok r2) :
      r2.val ≤ r1.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (power1 power2 : I64) (damage health : Slice I64) (n : Nat)
        (hdam_len : damage.val.length = n) (hhea_len : health.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hp1_lo : 1 ≤ power1.val) (hp_le : power1.val ≤ power2.val) (hp2_hi : power2.val ≤ 10 ^ 4)
        (hdam_lo : ∀ i, i < n → 1 ≤ entry damage i) (hdam_hi : ∀ i, i < n → entry damage i ≤ 10 ^ 4)
        (hhea_lo : ∀ i, i < n → 1 ≤ entry health i) (hhea_hi : ∀ i, i < n → entry health i ≤ 10 ^ 4)
        (r1 r2 : I64)
        (hr1 : Aegis.MinDamage.min_damage power1 damage health = ok r1)
        (hr2 : Aegis.MinDamage.min_damage power2 damage health = ok r2), r2.val ≤ r1.val) := by
    sorry

  end AegisSpec.MinDamage
