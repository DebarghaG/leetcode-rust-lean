import Aegis.LargestAltitude.Code.Funs

/-!
# Specifications of `Aegis.LargestAltitude.largest_altitude`

LeetCode problem `find-the-highest-altitude`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LargestAltitude

def prefixAlt (gain : Slice Std.I64) (k : Nat) : Int :=
  (gain.val.take k).foldl (fun acc x => acc + x.val) (0 : Int)

def maxAlt (gain : Slice Std.I64) : Int :=
  ((List.range (gain.val.length + 1)).map (prefixAlt gain)).foldr max 0

def ElementBounds (gain : Slice Std.I64) : Prop :=
  ∀ (i : Nat) (h : i < gain.val.length), -100 ≤ (gain.val[i]'h).val ∧ (gain.val[i]'h).val ≤ 100

def positiveSum (gain : Slice Std.I64) : Int :=
  (gain.val.map (fun x => max x.val 0)).sum

/-- Let A(0)=0 and, for each integer k with 1 <= k <= len(gain), let A(k)=gain[0]+gain[1]+...+gain[k-1]. The function returns a result r (it does not fail), and r = max { A(k) | 0 <= k <= len(gain) }.
  Preconditions: gain is a slice of 64-bit integers with 1 <= len(gain) <= 100 and, for every i with 0 <= i < len(gain), -100 <= gain[i] <= 100. -/
theorem spec_1 (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain) :
    ∃ r, Aegis.LargestAltitude.largest_altitude gain = ok r ∧ r.val = maxAlt gain := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain), ∃ r, Aegis.LargestAltitude.largest_altitude gain = ok r ∧ r.val = maxAlt gain) := by
  sorry

/-- The function returns a result r for every gain satisfying the preconditions; it does not fail because of overflow, out-of-bounds indexing, or panic.
  Preconditions: gain is a slice of 64-bit integers with 1 <= len(gain) <= 100 and, for every i with 0 <= i < len(gain), -100 <= gain[i] <= 100. -/
theorem spec_2 (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain) :
    ∃ r, Aegis.LargestAltitude.largest_altitude gain = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain), ∃ r, Aegis.LargestAltitude.largest_altitude gain = ok r) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer k with 0 <= k <= len(gain) such that r = A(k), where A(0)=0 and A(k)=gain[0]+...+gain[k-1] for 1 <= k <= len(gain).
  Preconditions: gain is a slice of 64-bit integers with 1 <= len(gain) <= 100 and, for every i with 0 <= i < len(gain), -100 <= gain[i] <= 100. -/
theorem spec_3 (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain) :
    ∀ r, Aegis.LargestAltitude.largest_altitude gain = ok r →
      ∃ k : Nat, k ≤ gain.val.length ∧ r.val = prefixAlt gain k := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain), ∀ r, Aegis.LargestAltitude.largest_altitude gain = ok r →
      ∃ k : Nat, k ≤ gain.val.length ∧ r.val = prefixAlt gain k) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 0 <= k <= len(gain), A(k) <= r, where A(0)=0 and A(k)=gain[0]+...+gain[k-1] for 1 <= k <= len(gain).
  Preconditions: gain is a slice of 64-bit integers with 1 <= len(gain) <= 100 and, for every i with 0 <= i < len(gain), -100 <= gain[i] <= 100. -/
theorem spec_4 (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain) :
    ∀ r, Aegis.LargestAltitude.largest_altitude gain = ok r →
      ∀ k : Nat, k ≤ gain.val.length → prefixAlt gain k ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain), ∀ r, Aegis.LargestAltitude.largest_altitude gain = ok r →
      ∀ k : Nat, k ≤ gain.val.length → prefixAlt gain k ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer M, if A(k) <= M for every integer k with 0 <= k <= len(gain), then r <= M, where A(0)=0 and A(k)=gain[0]+...+gain[k-1] for 1 <= k <= len(gain).
  Preconditions: gain is a slice of 64-bit integers with 1 <= len(gain) <= 100 and, for every i with 0 <= i < len(gain), -100 <= gain[i] <= 100. -/
theorem spec_5 (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain) :
    ∀ r, Aegis.LargestAltitude.largest_altitude gain = ok r →
      ∀ M : Int, (∀ k : Nat, k ≤ gain.val.length → prefixAlt gain k ≤ M) → r.val ≤ M := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain), ∀ r, Aegis.LargestAltitude.largest_altitude gain = ok r →
      ∀ M : Int, (∀ k : Nat, k ≤ gain.val.length → prefixAlt gain k ≤ M) → r.val ≤ M) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if A(k) <= 0 for every integer k with 0 <= k <= len(gain), where A(0)=0 and A(k)=gain[0]+...+gain[k-1] for 1 <= k <= len(gain).
  Preconditions: gain is a slice of 64-bit integers with 1 <= len(gain) <= 100 and, for every i with 0 <= i < len(gain), -100 <= gain[i] <= 100. -/
theorem spec_6 (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain) :
    ∀ r, Aegis.LargestAltitude.largest_altitude gain = ok r →
      (r.val = 0 ↔ ∀ k : Nat, k ≤ gain.val.length → prefixAlt gain k ≤ 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain), ∀ r, Aegis.LargestAltitude.largest_altitude gain = ok r →
      (r.val = 0 ↔ ∀ k : Nat, k ≤ gain.val.length → prefixAlt gain k ≤ 0)) := by
  sorry

/-- For every slice h of 64-bit integers with 1 <= len(h) = len(gain) <= 100 and -100 <= h[i] <= 100 for every i with 0 <= i < len(h), if gain[i] <= h[i] for every i with 0 <= i < len(gain), then whenever largest_altitude(gain) returns r and largest_altitude(h) returns s, r <= s.
  Preconditions: gain is a slice of 64-bit integers with 1 <= len(gain) <= 100 and, for every i with 0 <= i < len(gain), -100 <= gain[i] <= 100. -/
theorem spec_7 (gain h : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain)
    (hhlen : 1 ≤ h.val.length) (hheq : h.val.length = gain.val.length)
    (hhbounds : ElementBounds h)
    (hle : ∀ (i : Nat) (hi : i < gain.val.length) (hi' : i < h.val.length),
      (gain.val[i]'hi).val ≤ (h.val[i]'hi').val) :
    ∀ r s, Aegis.LargestAltitude.largest_altitude gain = ok r →
      Aegis.LargestAltitude.largest_altitude h = ok s → r.val ≤ s.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (gain h : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain)
    (hhlen : 1 ≤ h.val.length) (hheq : h.val.length = gain.val.length)
    (hhbounds : ElementBounds h)
    (hle : ∀ (i : Nat) (hi : i < gain.val.length) (hi' : i < h.val.length),
      (gain.val[i]'hi).val ≤ (h.val[i]'hi').val), ∀ r s, Aegis.LargestAltitude.largest_altitude gain = ok r →
      Aegis.LargestAltitude.largest_altitude h = ok s → r.val ≤ s.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{len(gain)-1} max(gain[i], 0).
  Preconditions: gain is a slice of 64-bit integers with 1 <= len(gain) <= 100 and, for every i with 0 <= i < len(gain), -100 <= gain[i] <= 100. -/
theorem spec_8 (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain) :
    ∀ r, Aegis.LargestAltitude.largest_altitude gain = ok r → r.val ≤ positiveSum gain := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (gain : Slice Std.I64)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 100)
    (hbounds : ElementBounds gain), ∀ r, Aegis.LargestAltitude.largest_altitude gain = ok r → r.val ≤ positiveSum gain) := by
  sorry

/-- For every integer c with -100 <= c <= 0, let h be the slice of 64-bit integers of length len(gain)+1 such that h[i]=gain[i] for every i with 0 <= i < len(gain) and h[len(gain)]=c. Then whenever largest_altitude(gain) returns r and largest_altitude(h) returns s, r = s.
  Preconditions: gain is a slice of 64-bit integers with 1 <= len(gain) <= 99 and, for every i with 0 <= i < len(gain), -100 <= gain[i] <= 100. -/
theorem spec_9 (gain h : Slice Std.I64) (c : Int)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 99)
    (hbounds : ElementBounds gain)
    (hc_low : -100 ≤ c) (hc_high : c ≤ 0)
    (hhlen : h.val.length = gain.val.length + 1)
    (hprefix : ∀ (i : Nat), i < gain.val.length → h.val[i]? = gain.val[i]?)
    (hlast : ∀ (x : Std.I64), h.val[gain.val.length]? = some x → x.val = c) :
    ∀ r s, Aegis.LargestAltitude.largest_altitude gain = ok r →
      Aegis.LargestAltitude.largest_altitude h = ok s → r.val = s.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (gain h : Slice Std.I64) (c : Int)
    (hlen : 1 ≤ gain.val.length) (hlen_le : gain.val.length ≤ 99)
    (hbounds : ElementBounds gain)
    (hc_low : -100 ≤ c) (hc_high : c ≤ 0)
    (hhlen : h.val.length = gain.val.length + 1)
    (hprefix : ∀ (i : Nat), i < gain.val.length → h.val[i]? = gain.val[i]?)
    (hlast : ∀ (x : Std.I64), h.val[gain.val.length]? = some x → x.val = c), ∀ r s, Aegis.LargestAltitude.largest_altitude gain = ok r →
      Aegis.LargestAltitude.largest_altitude h = ok s → r.val = s.val) := by
  sorry

end AegisSpec.LargestAltitude
