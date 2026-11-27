import Aegis.MaxConsecutive.Code.Funs

/-!
# Specifications of `Aegis.MaxConsecutive.max_consecutive`

LeetCode problem `maximum-consecutive-floors-without-special-floors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxConsecutive

  namespace AegisSpec.MaxConsecutive

  def IsSpecial (special : Slice Std.I64) (x : ℤ) : Prop :=
    ∃ v ∈ special.val, v.val = x

  def AllNonSpecial (special : Slice Std.I64) (l u : ℤ) : Prop :=
    ∀ x, l ≤ x → x ≤ u → ¬ IsSpecial special x

  def IsMaxRunLength (bottom top : Std.I64) (special : Slice Std.I64) (r : ℤ) : Prop :=
    (r = 0 ∧ ∀ x, bottom.val ≤ x → x ≤ top.val → IsSpecial special x) ∨
      (1 ≤ r ∧
        ∃ l u, bottom.val ≤ l ∧ l ≤ u ∧ u ≤ top.val ∧ u - l + 1 = r ∧
          AllNonSpecial special l u ∧
          ∀ l' u', bottom.val ≤ l' → l' ≤ u' → u' ≤ top.val → AllNonSpecial special l' u' →
            u' - l' + 1 ≤ r)

  def maxAdjacentGap : List ℤ → ℤ
    | [] => 0
    | [_] => 0
    | x :: y :: rest => max (y - x - 1) (maxAdjacentGap (y :: rest))

  structure Pre (bottom top : Std.I64) (special : Slice Std.I64) : Prop where

    bottom_pos : 1 ≤ bottom.val

    bottom_le_top : bottom.val ≤ top.val

    top_le_max : top.val ≤ 1000000000

    len_pos : 1 ≤ special.val.length

    len_le_max : special.val.length ≤ 100000

    in_range : ∀ v ∈ special.val, bottom.val ≤ v.val ∧ v.val ≤ top.val

    distinct :
      ∀ (i j : ℕ) (hi : i < special.val.length) (hj : j < special.val.length),
        i ≠ j → special.val[i] ≠ special.val[j]

  theorem length_pos_of_length_eq (bottom top : Std.I64) (special : Slice Std.I64)
      (h : Pre bottom top special) {s : List ℤ} (hs : s.length = special.val.length) :
      0 < s.length := by
    have h1 := h.len_pos
    omega

  theorem last_index_lt (bottom top : Std.I64) (special : Slice Std.I64)
      (h : Pre bottom top special) {s : List ℤ} (hs : s.length = special.val.length) :
      s.length - 1 < s.length := by
    have h1 := h.len_pos
    omega

  /-- The function returns a result r (it does not fail), and r is the maximum number of consecutive non-special floors inside the rented interval [bottom, top]. Formally, call an integer x special iff there exists j with 0 <= j < len(special) and special[j] = x. Then r = 0 if every integer x with bottom <= x <= top is special; otherwise r is the largest integer L >= 1 for which there exist integers l and u with bottom <= l <= u <= top, u - l + 1 = L, and every integer x with l <= x <= u is not special.
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. -/
  theorem spec_1 (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special) :
      ∃ r : Std.I64, max_consecutive bottom top special = .ok r ∧
        IsMaxRunLength bottom top special r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special), ∃ r : Std.I64, max_consecutive bottom top special = Result.ok r ∧
          IsMaxRunLength bottom top special r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. -/
  theorem spec_2 (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special) :
      ∀ r : Std.I64, max_consecutive bottom top special = .ok r → 0 ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special), ∀ r : Std.I64, max_consecutive bottom top special = Result.ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= (top - bottom + 1) - len(special).
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. -/
  theorem spec_3 (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special) :
      ∀ r : Std.I64, max_consecutive bottom top special = .ok r →
        r.val ≤ (top.val - bottom.val + 1) - (special.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special), ∀ r : Std.I64, max_consecutive bottom top special = Result.ok r →
          r.val ≤ (top.val - bottom.val + 1) - (special.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r and r > 0, there exist integers l and u such that bottom <= l <= u <= top, u - l + 1 = r, and for every integer x with l <= x <= u, x is not special (that is, there is no j with 0 <= j < len(special) and special[j] = x).
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. -/
  theorem spec_4 (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special) :
      ∀ r : Std.I64, max_consecutive bottom top special = .ok r → 0 < r.val →
        ∃ l u, bottom.val ≤ l ∧ l ≤ u ∧ u ≤ top.val ∧ u - l + 1 = r.val ∧
          AllNonSpecial special l u := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special), ∀ r : Std.I64, max_consecutive bottom top special = Result.ok r → 0 < r.val →
          ∃ l u, bottom.val ≤ l ∧ l ≤ u ∧ u ≤ top.val ∧ u - l + 1 = r.val ∧
            AllNonSpecial special l u) := by
    sorry

  /-- Whenever the function returns a result r, for all integers l and u with bottom <= l <= u <= top such that every integer x with l <= x <= u is not special, we have u - l + 1 <= r.
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. -/
  theorem spec_5 (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special) :
      ∀ r : Std.I64, max_consecutive bottom top special = .ok r →
        ∀ l u, bottom.val ≤ l → l ≤ u → u ≤ top.val → AllNonSpecial special l u →
          u - l + 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special), ∀ r : Std.I64, max_consecutive bottom top special = Result.ok r →
          ∀ l u, bottom.val ≤ l → l ≤ u → u ≤ top.val → AllNonSpecial special l u →
            u - l + 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if every integer x with bottom <= x <= top is special (i.e. for every such x there exists j with 0 <= j < len(special) and special[j] = x).
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. -/
  theorem spec_6 (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special) :
      ∀ r : Std.I64, max_consecutive bottom top special = .ok r →
        (r.val = 0 ↔ ∀ x, bottom.val ≤ x → x ≤ top.val → IsSpecial special x) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special), ∀ r : Std.I64, max_consecutive bottom top special = Result.ok r →
          (r.val = 0 ↔ ∀ x, bottom.val ≤ x → x ≤ top.val → IsSpecial special x)) := by
    sorry

  /-- Let s be the sequence of length len(special) whose entries are exactly the entries of special in strictly increasing order (well defined because all special values are distinct and lie in [bottom, top]). Whenever the function returns a result r, r equals the maximum of the set containing 0, s[0] - bottom, top - s[len(special)-1], and every value s[i+1] - s[i] - 1 for 0 <= i < len(special)-1. Equivalently, r is the largest number of floors in any of the ranges before the first special floor, after the last special floor, and between consecutive special floors.
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. -/
  theorem spec_7 (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special) :
      ∀ r : Std.I64, max_consecutive bottom top special = .ok r →
        ∀ (s : List ℤ) (hs : s.length = special.val.length),
          (∀ (i : ℕ) (hi : i + 1 < s.length), s[i] < s[i + 1]) →
          (∀ x : ℤ, x ∈ s ↔ IsSpecial special x) →
          r.val = max 0
            (max (s.get ⟨0, length_pos_of_length_eq bottom top special h hs⟩ - bottom.val)
              (max (top.val - s.get ⟨s.length - 1, last_index_lt bottom top special h hs⟩)
                (maxAdjacentGap s))) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special), ∀ r : Std.I64, max_consecutive bottom top special = Result.ok r →
          ∀ (s : List ℤ) (hs : s.length = special.val.length),
            (∀ (i : ℕ) (hi : i + 1 < s.length), s[i] < s[i + 1]) →
            (∀ x : ℤ, x ∈ s ↔ IsSpecial special x) →
            r.val = max 0
              (max (s.get ⟨0, length_pos_of_length_eq bottom top special h hs⟩ - bottom.val)
                (max (top.val - s.get ⟨s.length - 1, last_index_lt bottom top special h hs⟩)
                  (maxAdjacentGap s)))) := by
    sorry

  /-- For every slice special' with len(special') = len(special) and with the same multiset of entries as special (equivalently, special' is a permutation of special), whenever the function returns r on (bottom, top, special) and r' on (bottom, top, special'), we have r = r'.
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. -/
  theorem spec_8 (bottom top : Std.I64) (special special' : Slice Std.I64)
      (h : Pre bottom top special)
      (hlen : special'.val.length = special.val.length)
      (hperm : (special'.val.map (fun v => v.val)).Perm (special.val.map (fun v => v.val))) :
      ∀ r r' : Std.I64, max_consecutive bottom top special = .ok r →
        max_consecutive bottom top special' = .ok r' → r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (bottom top : Std.I64) (special special' : Slice Std.I64)
        (h : Pre bottom top special)
        (hlen : special'.val.length = special.val.length)
        (hperm : (special'.val.map (fun v => v.val)).Perm (special.val.map (fun v => v.val))), ∀ r r' : Std.I64, max_consecutive bottom top special = Result.ok r →
          max_consecutive bottom top special' = Result.ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on (bottom, top, special) and r' on (bottom', top', special'), we have r = r'.
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. Also, k is an integer such that the shifted parameters bottom' = bottom + k, top' = top + k, and special' with len(special') = len(special) and special'[i] = special[i] + k for every 0 <= i < len(special) still satisfy 1 <= bottom' <= top' <= 1000000000 and bottom' <= special'[i] <= top' for every i. -/
  theorem spec_9 (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special)
      (k : ℤ) (bottom' top' : Std.I64) (special' : Slice Std.I64)
      (hbottom' : bottom'.val = bottom.val + k) (htop' : top'.val = top.val + k)
      (hlen : special'.val.length = special.val.length)
      (hshift : special'.val.map (fun v => v.val) = (special.val.map (fun v => v.val)).map (· + k))
      (hrange : 1 ≤ bottom'.val ∧ bottom'.val ≤ top'.val ∧ top'.val ≤ 1000000000)
      (hin_range : ∀ v ∈ special'.val, bottom'.val ≤ v.val ∧ v.val ≤ top'.val) :
      ∀ r r' : Std.I64, max_consecutive bottom top special = .ok r →
        max_consecutive bottom' top' special' = .ok r' → r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special)
        (k : ℤ) (bottom' top' : Std.I64) (special' : Slice Std.I64)
        (hbottom' : bottom'.val = bottom.val + k) (htop' : top'.val = top.val + k)
        (hlen : special'.val.length = special.val.length)
        (hshift : special'.val.map (fun v => v.val) = (special.val.map (fun v => v.val)).map (· + k))
        (hrange : 1 ≤ bottom'.val ∧ bottom'.val ≤ top'.val ∧ top'.val ≤ 1000000000)
        (hin_range : ∀ v ∈ special'.val, bottom'.val ≤ v.val ∧ v.val ≤ top'.val), ∀ r r' : Std.I64, max_consecutive bottom top special = Result.ok r →
          max_consecutive bottom' top' special' = Result.ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r, r is at least the greatest integer c such that c * (len(special) + 1) <= top - bottom + 1.
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. -/
  theorem spec_10 (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special) :
      ∀ r : Std.I64, max_consecutive bottom top special = .ok r →
        ∀ c : ℤ, c * ((special.val.length : ℤ) + 1) ≤ top.val - bottom.val + 1 → c ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special), ∀ r : Std.I64, max_consecutive bottom top special = Result.ok r →
          ∀ c : ℤ, c * ((special.val.length : ℤ) + 1) ≤ top.val - bottom.val + 1 → c ≤ r.val) := by
    sorry

  /-- Whenever the function returns r on (bottom, top, special) and r' on (bottom, top, special'), we have r' <= r.
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. Also, special' is a slice satisfying the same constraints (1 <= len(special') <= 100000, all entries in [bottom, top], and all entries distinct), and every entry of special occurs as an entry of special'. -/
  theorem spec_11 (bottom top : Std.I64) (special special' : Slice Std.I64)
      (h : Pre bottom top special) (h' : Pre bottom top special')
      (hsub : ∀ v ∈ special.val, ∃ w ∈ special'.val, w.val = v.val) :
      ∀ r r' : Std.I64, max_consecutive bottom top special = .ok r →
        max_consecutive bottom top special' = .ok r' → r'.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (bottom top : Std.I64) (special special' : Slice Std.I64)
        (h : Pre bottom top special) (h' : Pre bottom top special')
        (hsub : ∀ v ∈ special.val, ∃ w ∈ special'.val, w.val = v.val), ∀ r r' : Std.I64, max_consecutive bottom top special = Result.ok r →
          max_consecutive bottom top special' = Result.ok r' → r'.val ≤ r.val) := by
    sorry

  /-- For every bottom, top, and special satisfying the preconditions, the function returns a result: there exists an I64 value r such that max_consecutive bottom top special = Result.ok r. It does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: bottom, top, and special are I64 values; 1 <= bottom <= top <= 1000000000; 1 <= len(special) <= 100000; for every i with 0 <= i < len(special), bottom <= special[i] <= top; and for all 0 <= i < j < len(special), special[i] != special[j]. -/
  theorem spec_12 (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special) :
      ∃ r : Std.I64, max_consecutive bottom top special = .ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (bottom top : Std.I64) (special : Slice Std.I64) (h : Pre bottom top special), ∃ r : Std.I64, max_consecutive bottom top special = Result.ok r) := by
    sorry

  end AegisSpec.MaxConsecutive
