import Aegis.IsDecomposable.Code.Funs

/-!
# Specifications of `Aegis.IsDecomposable.is_decomposable`

LeetCode problem `check-if-string-is-decomposable-into-value-equal-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsDecomposable

  def IsDigit (b : Std.U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

  def runScan (cur : Option (Std.U8 × ℕ)) (acc : List ℕ) : List Std.U8 → List ℕ
    | [] =>
        match cur with
        | some (_, k) => acc ++ [k]
        | none => acc
    | b :: rest =>
        match cur with
        | some (c, k) =>
            if b = c then runScan (some (c, k + 1)) acc rest
            else runScan (some (b, 1)) (acc ++ [k]) rest
        | none => runScan (some (b, 1)) acc rest

  def RunLens (l : List Std.U8) : List ℕ := runScan none [] l

  def FlatOn (l : List Std.U8) (a b : ℕ) : Prop :=
    ∀ (hb : b ≤ l.length) (i : ℕ) (hi : a ≤ i) (hi' : i < b)
      (j : ℕ) (hj : a ≤ j) (hj' : j < b),
      l[i]'(by omega) = l[j]'(by omega)

  def IsMaximalRun (l : List Std.U8) (a b : ℕ) : Prop :=
    a < b ∧ b ≤ l.length ∧ FlatOn l a b ∧
      (∀ (ha : 0 < a) (hb : a < l.length), l[a - 1]'(by omega) ≠ l[a]'hb) ∧
      (∀ (hb : b < l.length), l[b]'hb ≠ l[b - 1]'(by omega))

  def AllEqual (l : List Std.U8) : Prop :=
    ∀ (i : ℕ) (hi : i < l.length) (j : ℕ) (hj : j < l.length), l[i]'hi = l[j]'hj

  def BlockLens (bs : List ℕ) : List ℕ := (bs.zip (bs.drop 1)).map (fun p => p.2 - p.1)

  /-- Whenever the function returns a result r, r = true if and only if the following holds. Let L_0, L_1, ..., L_{m-1} be the lengths, in order, of all maximal runs of s, where a run is a nonempty interval [l,u) of indices with s[l] = s[l+1] = ... = s[u-1], with l = 0 or s[l-1] != s[l], and with u = len(s) or s[u] != s[u-1]. Then exactly one of the numbers L_0, ..., L_{m-1} is congruent to 2 modulo 3, and every other number among them is congruent to 0 modulo 3.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is one of the ASCII byte values for the digits '0' through '9'. -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi)) :
      ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r →
        (r = true ↔
          (RunLens s.val).countP (fun L => L % 3 == 2) = 1 ∧
            ∀ L ∈ RunLens s.val, L % 3 = 2 ∨ L % 3 = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi)), ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r →
          (r = true ↔
            (RunLens s.val).countP (fun L => L % 3 == 2) = 1 ∧
              ∀ L ∈ RunLens s.val, L % 3 = 2 ∨ L % 3 = 0)) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns a result r (it does not fail).
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is one of the ASCII byte values for the digits '0' through '9'. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi)) :
      ∃ r : Bool, Aegis.IsDecomposable.is_decomposable s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi)), ∃ r : Bool, Aegis.IsDecomposable.is_decomposable s = ok r) := by
    sorry

  /-- Whenever the function returns a result r and r = true, len(s) mod 3 = 2.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is one of the ASCII byte values for the digits '0' through '9'. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi)) :
      ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r → r = true →
        s.val.length % 3 = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi)), ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r → r = true →
          s.val.length % 3 = 2) := by
    sorry

  /-- Whenever the function returns a result r and r = true, there exists an integer a with 0 <= a such that 3*a + 1 < len(s) and s[3*a] = s[3*a+1].
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is one of the ASCII byte values for the digits '0' through '9'. -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi)) :
      ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r → r = true →
        ∃ (a : ℕ) (ha : 3 * a + 1 < s.val.length),
          s.val[3 * a]'(by omega) = s.val[3 * a + 1]'ha := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi)), ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r → r = true →
          ∃ (a : ℕ) (ha : 3 * a + 1 < s.val.length),
            s.val[3 * a]'(by omega) = s.val[3 * a + 1]'ha) := by
    sorry

  /-- Whenever the function returns a result r and len(s) = 2, r = true if and only if s[0] = s[1].
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is one of the ASCII byte values for the digits '0' through '9'. -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
      (hlen2 : s.val.length = 2) :
      ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r →
        (r = true ↔ s.val[0]'(by omega) = s.val[1]'(by omega)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
        (hlen2 : s.val.length = 2), ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r →
          (r = true ↔ s.val[0]'(by omega) = s.val[1]'(by omega))) := by
    sorry

  /-- Whenever the function returns a result r and len(s) = 5, r = true if and only if either (s[0] = s[1] and s[2] = s[3] and s[3] = s[4]) or (s[0] = s[1] and s[1] = s[2] and s[3] = s[4]).
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is one of the ASCII byte values for the digits '0' through '9'. -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
      (hlen5 : s.val.length = 5) :
      ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r →
        (r = true ↔
          (s.val[0]'(by omega) = s.val[1]'(by omega) ∧
              s.val[2]'(by omega) = s.val[3]'(by omega) ∧
              s.val[3]'(by omega) = s.val[4]'(by omega)) ∨
            (s.val[0]'(by omega) = s.val[1]'(by omega) ∧
              s.val[1]'(by omega) = s.val[2]'(by omega) ∧
              s.val[3]'(by omega) = s.val[4]'(by omega))) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
        (hlen5 : s.val.length = 5), ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r →
          (r = true ↔
            (s.val[0]'(by omega) = s.val[1]'(by omega) ∧
                s.val[2]'(by omega) = s.val[3]'(by omega) ∧
                s.val[3]'(by omega) = s.val[4]'(by omega)) ∨
              (s.val[0]'(by omega) = s.val[1]'(by omega) ∧
                s.val[1]'(by omega) = s.val[2]'(by omega) ∧
                s.val[3]'(by omega) = s.val[4]'(by omega)))) := by
    sorry

  /-- If all bytes of s are equal, then whenever the function returns a result r, r = true if and only if len(s) mod 3 = 2.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is one of the ASCII byte values for the digits '0' through '9'. -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
      (heq : AllEqual s.val) :
      ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r →
        (r = true ↔ s.val.length % 3 = 2) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
        (heq : AllEqual s.val), ∀ (r : Bool), Aegis.IsDecomposable.is_decomposable s = ok r →
          (r = true ↔ s.val.length % 3 = 2)) := by
    sorry

  /-- If s has a maximal interval [l,u) with 0 <= l < u <= len(s) such that s[l] = s[l+1] = ... = s[u-1], and no byte immediately before l (if any) equals s[l], and no byte immediately after u-1 (if any) equals s[u-1], and L = u - l satisfies L mod 3 = 1, then whenever the function returns a result res, res = false.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is one of the ASCII byte values for the digits '0' through '9'. -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
      (l u : ℕ) (hrun : IsMaximalRun s.val l u) (hmod : (u - l) % 3 = 1) :
      ∀ (res : Bool), Aegis.IsDecomposable.is_decomposable s = ok res → res = false := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
        (l u : ℕ) (hrun : IsMaximalRun s.val l u) (hmod : (u - l) % 3 = 1), ∀ (res : Bool), Aegis.IsDecomposable.is_decomposable s = ok res → res = false) := by
    sorry

  /-- If s has two distinct maximal intervals [l,u) and [l',u') of the same type (all bytes inside each interval are equal and neither interval can be extended), whose lengths L = u - l and L' = u' - l' both satisfy L mod 3 = 2 and L' mod 3 = 2, then whenever the function returns a result res, res = false.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is one of the ASCII byte values for the digits '0' through '9'. -/
  theorem spec_9 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
      (l u l' u' : ℕ) (hrun : IsMaximalRun s.val l u) (hrun' : IsMaximalRun s.val l' u')
      (hne : (l, u) ≠ (l', u'))
      (hmod : (u - l) % 3 = 2) (hmod' : (u' - l') % 3 = 2) :
      ∀ (res : Bool), Aegis.IsDecomposable.is_decomposable s = ok res → res = false := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
        (l u l' u' : ℕ) (hrun : IsMaximalRun s.val l u) (hrun' : IsMaximalRun s.val l' u')
        (hne : (l, u) ≠ (l', u'))
        (hmod : (u - l) % 3 = 2) (hmod' : (u' - l') % 3 = 2), ∀ (res : Bool), Aegis.IsDecomposable.is_decomposable s = ok res → res = false) := by
    sorry

  /-- Whenever the function returns a result res and res = true, there exist an integer k >= 1 and indices 0 = b_0 < b_1 < ... < b_k = len(s) such that for every t with 0 <= t < k, all bytes s[b_t], s[b_t+1], ..., s[b_{t+1}-1] are equal, the length b_{t+1}-b_t is either 2 or 3, and exactly one t has b_{t+1}-b_t = 2 (all other t have b_{t+1}-b_t = 3).
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is one of the ASCII byte values for the digits '0' through '9'. -/
  theorem spec_10 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi)) :
      ∀ (res : Bool), Aegis.IsDecomposable.is_decomposable s = ok res → res = true →
        ∃ bs : List ℕ,
          2 ≤ bs.length ∧
            bs.head? = some 0 ∧
            bs.getLast? = some s.val.length ∧
            bs.Pairwise (· < ·) ∧
            (∀ p ∈ bs.zip (bs.drop 1), FlatOn s.val p.1 p.2) ∧
            (∀ L ∈ BlockLens bs, L = 2 ∨ L = 3) ∧
            (BlockLens bs).countP (fun L => L == 2) = 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi)), ∀ (res : Bool), Aegis.IsDecomposable.is_decomposable s = ok res → res = true →
          ∃ bs : List ℕ,
            2 ≤ bs.length ∧
              bs.head? = some 0 ∧
              bs.getLast? = some s.val.length ∧
              bs.Pairwise (· < ·) ∧
              (∀ p ∈ bs.zip (bs.drop 1), FlatOn s.val p.1 p.2) ∧
              (∀ L ∈ BlockLens bs, L = 2 ∨ L = 3) ∧
              (BlockLens bs).countP (fun L => L == 2) = 1) := by
    sorry

  /-- If for every i with 0 <= i < len(s) - 1, s[i] = s[i+1] if and only if t[i] = t[i+1], then whenever is_decomposable(s) returns res_s and is_decomposable(t) returns res_t, res_s = res_t.
    Preconditions: 1 <= len(s) <= 1000, 1 <= len(t) <= 1000, len(s) = len(t), and every byte of s and of t is one of the ASCII byte values for the digits '0' through '9'. -/
  theorem spec_11 (s t : Slice Std.U8)
      (hs : 1 ≤ s.val.length) (hs' : s.val.length ≤ 1000)
      (ht : 1 ≤ t.val.length) (ht' : t.val.length ≤ 1000)
      (hlen : s.val.length = t.val.length)
      (hdigs : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
      (hdigt : ∀ (i : ℕ) (hi : i < t.val.length), IsDigit (t.val[i]'hi))
      (hadj : ∀ (i : ℕ) (hi : i + 1 < s.val.length),
        (s.val[i]'(by omega) = s.val[i + 1]'hi ↔
          t.val[i]'(by omega) = t.val[i + 1]'(by omega))) :
      ∀ (res_s res_t : Bool),
        Aegis.IsDecomposable.is_decomposable s = ok res_s →
          Aegis.IsDecomposable.is_decomposable t = ok res_t → res_s = res_t := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hs : 1 ≤ s.val.length) (hs' : s.val.length ≤ 1000)
        (ht : 1 ≤ t.val.length) (ht' : t.val.length ≤ 1000)
        (hlen : s.val.length = t.val.length)
        (hdigs : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
        (hdigt : ∀ (i : ℕ) (hi : i < t.val.length), IsDigit (t.val[i]'hi))
        (hadj : ∀ (i : ℕ) (hi : i + 1 < s.val.length),
          (s.val[i]'(by omega) = s.val[i + 1]'hi ↔
            t.val[i]'(by omega) = t.val[i + 1]'(by omega))), ∀ (res_s res_t : Bool),
          Aegis.IsDecomposable.is_decomposable s = ok res_s →
            Aegis.IsDecomposable.is_decomposable t = ok res_t → res_s = res_t) := by
    sorry

  /-- Whenever is_decomposable(s) returns res_s and is_decomposable(t) returns res_t, res_s = res_t.
    Preconditions: 1 <= len(s) <= 1000, every byte of s is an ASCII digit, and t is the byte sequence of length len(s) with t[i] = s[len(s)-1-i] for every 0 <= i < len(s). -/
  theorem spec_12 (s t : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
      (hlen_t : t.val.length = s.val.length)
      (htrev : ∀ (i : ℕ) (hi : i < t.val.length),
        t.val[i]'hi = s.val[s.val.length - 1 - i]'(by omega)) :
      ∀ (res_s res_t : Bool),
        Aegis.IsDecomposable.is_decomposable s = ok res_s →
          Aegis.IsDecomposable.is_decomposable t = ok res_t → res_s = res_t := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.val.length), IsDigit (s.val[i]'hi))
        (hlen_t : t.val.length = s.val.length)
        (htrev : ∀ (i : ℕ) (hi : i < t.val.length),
          t.val[i]'hi = s.val[s.val.length - 1 - i]'(by omega)), ∀ (res_s res_t : Bool),
          Aegis.IsDecomposable.is_decomposable s = ok res_s →
            Aegis.IsDecomposable.is_decomposable t = ok res_t → res_s = res_t) := by
    sorry

  end AegisSpec.IsDecomposable
