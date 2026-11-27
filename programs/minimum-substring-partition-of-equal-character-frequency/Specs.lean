import Aegis.MinimumSubstringsInPartition.Code.Funs

/-!
# Specifications of `Aegis.MinimumSubstringsInPartition.minimum_substrings_in_partition`

LeetCode problem `minimum-substring-partition-of-equal-character-frequency`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumSubstringsInPartition

  namespace AegisSpec.MinimumSubstringsInPartition

  def IsLowerByte (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def lowerBytes : Set U8 := {b | IsLowerByte b}

  def AllLower (l : List U8) : Prop := ∀ (i : Nat) (hi : i < l.length), IsLowerByte (l[i])

  def countByte (l : List U8) (c : U8) : Nat := l.count c

  def Balanced (l : List U8) : Prop :=
    ∀ c d : U8, 0 < countByte l c → 0 < countByte l d → countByte l c = countByte l d

  def segment (l : List U8) (l₀ u : Nat) : List U8 := (l.drop l₀).take (u - l₀)

  def IsBalancedPartition (l : List U8) (k : Nat) (p : Nat → Nat) : Prop :=
    p 0 = 0 ∧ p k = l.length ∧
      (∀ j, j < k → p j < p (j + 1)) ∧
      (∀ j, j < k → Balanced (segment l (p j) (p (j + 1))))

  def HasBalancedPartition (l : List U8) (k : Nat) : Prop :=
    ∃ p : Nat → Nat, IsBalancedPartition l k p

  /-- Whenever the function returns a result r, r is the least integer k with k >= 1 for which there exist indices 0 = p0 < p1 < ... < pk = len(s) such that, for every j with 1 <= j <= k, the segment s[p_{j-1}..p_j) is balanced. A segment s[l..u) with 0 <= l < u <= len(s) is balanced iff, for every byte c, letting cnt(c) = #{i | l <= i < u and s[i] = c}, the set of positive values cnt(c) over all bytes c has exactly one element; equivalently, whenever cnt(c) > 0 and cnt(d) > 0, cnt(c) = cnt(d).
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_1 (s : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val) :
      ∀ r : I64, minimum_substrings_in_partition s = ok r →
        ∃ k : Nat, r.val = (k : Int) ∧ 1 ≤ k ∧ HasBalancedPartition s.val k ∧
          ∀ m : Nat, 1 ≤ m → HasBalancedPartition s.val m → k ≤ m := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val), ∀ r : I64, minimum_substrings_in_partition s = ok r →
          ∃ k : Nat, r.val = (k : Int) ∧ 1 ≤ k ∧ HasBalancedPartition s.val k ∧
            ∀ m : Nat, 1 ≤ m → HasBalancedPartition s.val m → k ≤ m) := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_2 (s : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val) :
      ∃ r : I64, minimum_substrings_in_partition s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val), ∃ r : I64, minimum_substrings_in_partition s = ok r) := by
    sorry

  /-- Whenever the function returns a result res, res >= 1.
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_3 (s : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val) :
      ∀ res : I64, minimum_substrings_in_partition s = ok res → 1 ≤ res.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val), ∀ res : I64, minimum_substrings_in_partition s = ok res → 1 ≤ res.val) := by
    sorry

  /-- Whenever the function returns a result res, there exist indices 0 = p0 < p1 < ... < p_k = len(s) with k = res such that every part s[p_{j-1}..p_j) for 1 <= j <= k is balanced (all positive character counts in that part are equal).
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_4 (s : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val) :
      ∀ res : I64, minimum_substrings_in_partition s = ok res →
        ∃ k : Nat, res.val = (k : Int) ∧ HasBalancedPartition s.val k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val), ∀ res : I64, minimum_substrings_in_partition s = ok res →
          ∃ k : Nat, res.val = (k : Int) ∧ HasBalancedPartition s.val k) := by
    sorry

  /-- Whenever the function returns a result res, for every m >= 1 and every sequence 0 = p0 < p1 < ... < pm = len(s) such that each part s[p_{j-1}..p_j) is balanced (all positive character counts in that part are equal), we have res <= m.
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_5 (s : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val) :
      ∀ res : I64, minimum_substrings_in_partition s = ok res →
        ∀ m : Nat, 1 ≤ m → HasBalancedPartition s.val m → res.val ≤ (m : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val), ∀ res : I64, minimum_substrings_in_partition s = ok res →
          ∀ m : Nat, 1 ≤ m → HasBalancedPartition s.val m → res.val ≤ (m : Int)) := by
    sorry

  /-- Whenever the function returns a result res, res = 1 if and only if the whole string s[0..len(s)) is balanced, meaning that for every two bytes c and d, if c occurs in s and d occurs in s, then their occurrence counts in s are equal.
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_6 (s : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val) :
      ∀ res : I64, minimum_substrings_in_partition s = ok res →
        (res.val = 1 ↔ Balanced s.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val), ∀ res : I64, minimum_substrings_in_partition s = ok res →
          (res.val = 1 ↔ Balanced s.val)) := by
    sorry

  /-- Whenever the function returns a result res, res = 2 if and only if all three following conditions hold: (a) len(s) > 1; (b) the whole string s[0..len(s)) is not balanced; (c) there exists an index p with 0 < p < len(s) such that both s[0..p) and s[p..len(s)) are balanced (all positive character counts within each of these two segments are equal).
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_7 (s : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val) :
      ∀ res : I64, minimum_substrings_in_partition s = ok res →
        (res.val = 2 ↔
          1 < s.val.length ∧ ¬ Balanced s.val ∧
            ∃ p : Nat, 0 < p ∧ p < s.val.length ∧
              Balanced (segment s.val 0 p) ∧ Balanced (segment s.val p s.val.length)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val), ∀ res : I64, minimum_substrings_in_partition s = ok res →
          (res.val = 2 ↔
            1 < s.val.length ∧ ¬ Balanced s.val ∧
              ∃ p : Nat, 0 < p ∧ p < s.val.length ∧
                Balanced (segment s.val 0 p) ∧ Balanced (segment s.val p s.val.length))) := by
    sorry

  /-- For every slice t of bytes with len(t) = len(s), every t[i] being a lowercase English letter, and every bijection phi from the set of lowercase English letters to itself, if t[i] = phi(s[i]) for every i with 0 <= i < len(s), then whenever the function returns res on input s and returns res' on input t, res = res'.
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_8 (s t : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val)
      (hlen_t : t.val.length = s.val.length)
      (hlow_t : AllLower t.val)
      (φ : U8 → U8) (hφ : Set.BijOn φ lowerBytes lowerBytes)
      (hmap : ∀ (i : Nat) (hi : i < s.val.length), t.val[i]'(by omega) = φ (s.val[i])) :
      ∀ res res' : I64, minimum_substrings_in_partition s = ok res →
        minimum_substrings_in_partition t = ok res' → res = res' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val)
        (hlen_t : t.val.length = s.val.length)
        (hlow_t : AllLower t.val)
        (φ : U8 → U8) (hφ : Set.BijOn φ lowerBytes lowerBytes)
        (hmap : ∀ (i : Nat) (hi : i < s.val.length), t.val[i]'(by omega) = φ (s.val[i])), ∀ res res' : I64, minimum_substrings_in_partition s = ok res →
          minimum_substrings_in_partition t = ok res' → res = res') := by
    sorry

  /-- For every slice t of lowercase bytes with len(t) = len(s) and t[i] = s[len(s)-1-i] for every i with 0 <= i < len(s), whenever the function returns res on input s and returns res' on input t, res = res'.
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_9 (s t : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val)
      (hlen_t : t.val.length = s.val.length)
      (hlow_t : AllLower t.val)
      (hrev : ∀ (i : Nat) (hi : i < t.val.length),
        t.val[i] = s.val[s.val.length - 1 - i]'(by omega)) :
      ∀ res res' : I64, minimum_substrings_in_partition s = ok res →
        minimum_substrings_in_partition t = ok res' → res = res' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val)
        (hlen_t : t.val.length = s.val.length)
        (hlow_t : AllLower t.val)
        (hrev : ∀ (i : Nat) (hi : i < t.val.length),
          t.val[i] = s.val[s.val.length - 1 - i]'(by omega)), ∀ res res' : I64, minimum_substrings_in_partition s = ok res →
          minimum_substrings_in_partition t = ok res' → res = res') := by
    sorry

  /-- For every nonempty slice u of lowercase bytes and every slice t of lowercase bytes such that len(t) = len(s) + len(u), t[0..len(s)) = s, t[len(s)..len(t)) = u, len(t) <= 1000, and u is balanced (all positive character counts in u are equal), if the function returns res on input s and returns res' on input t, then res' <= res + 1.
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_10 (s u t : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val)
      (hu_ne : 0 < u.val.length)
      (hu_low : AllLower u.val)
      (ht_low : AllLower t.val)
      (ht_len : t.val.length = s.val.length + u.val.length)
      (ht_bound : t.val.length ≤ 1000)
      (hpre : segment t.val 0 s.val.length = s.val)
      (hsuf : segment t.val s.val.length t.val.length = u.val)
      (hu_bal : Balanced u.val) :
      ∀ res res' : I64, minimum_substrings_in_partition s = ok res →
        minimum_substrings_in_partition t = ok res' → res'.val ≤ res.val + 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s u t : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val)
        (hu_ne : 0 < u.val.length)
        (hu_low : AllLower u.val)
        (ht_low : AllLower t.val)
        (ht_len : t.val.length = s.val.length + u.val.length)
        (ht_bound : t.val.length ≤ 1000)
        (hpre : segment t.val 0 s.val.length = s.val)
        (hsuf : segment t.val s.val.length t.val.length = u.val)
        (hu_bal : Balanced u.val), ∀ res res' : I64, minimum_substrings_in_partition s = ok res →
          minimum_substrings_in_partition t = ok res' → res'.val ≤ res.val + 1) := by
    sorry

  /-- Whenever the function returns res on s, for every split point p with 0 < p < len(s), letting res_left be the function's result on s[0..p) and res_right be the function's result on s[p..len(s)), we have res <= res_left + res_right.
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_11 (s : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val) :
      ∀ res : I64, minimum_substrings_in_partition s = ok res →
        ∀ (p : Nat), 0 < p → p < s.val.length → ∀ sL sR : Slice U8,
          sL.val = segment s.val 0 p → sR.val = segment s.val p s.val.length →
          ∀ resL resR : I64, minimum_substrings_in_partition sL = ok resL →
            minimum_substrings_in_partition sR = ok resR → res.val ≤ resL.val + resR.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val), ∀ res : I64, minimum_substrings_in_partition s = ok res →
          ∀ (p : Nat), 0 < p → p < s.val.length → ∀ sL sR : Slice U8,
            sL.val = segment s.val 0 p → sR.val = segment s.val p s.val.length →
            ∀ resL resR : I64, minimum_substrings_in_partition sL = ok resL →
              minimum_substrings_in_partition sR = ok resR → res.val ≤ resL.val + resR.val) := by
    sorry

  /-- Whenever the function returns res and 0 = p0 < p1 < ... < p_res = len(s) is an optimal balanced partition (each part s[p_{j-1}..p_j) is balanced), then for every j with 1 <= j < res, the merged segment s[p_{j-1}..p_{j+1}) is not balanced.
    Preconditions: 1 <= len(s) <= 1000 and every byte s[i] with 0 <= i < len(s) is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_12 (s : Slice U8)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
      (hlow : AllLower s.val) :
      ∀ res : I64, minimum_substrings_in_partition s = ok res →
        ∀ (k : Nat) (p : Nat → Nat), res.val = (k : Int) → IsBalancedPartition s.val k p →
          ∀ j : Nat, 1 ≤ j → j < k →
            ¬ Balanced (segment s.val (p (j - 1)) (p (j + 1))) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice U8)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 1000)
        (hlow : AllLower s.val), ∀ res : I64, minimum_substrings_in_partition s = ok res →
          ∀ (k : Nat) (p : Nat → Nat), res.val = (k : Int) → IsBalancedPartition s.val k p →
            ∀ j : Nat, 1 ≤ j → j < k →
              ¬ Balanced (segment s.val (p (j - 1)) (p (j + 1)))) := by
    sorry

  end AegisSpec.MinimumSubstringsInPartition
