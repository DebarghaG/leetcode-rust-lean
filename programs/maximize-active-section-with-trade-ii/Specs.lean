import Aegis.MaxActiveSectionsAfterTrade.Code.Funs

/-!
# Specifications of `Aegis.MaxActiveSectionsAfterTrade.max_active_sections_after_trade`

LeetCode problem `maximize-active-section-with-trade-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxActiveSectionsAfterTrade

  namespace AegisSpec.MaxActiveSectionsAfterTrade

  @[reducible] def byteAt (s : Slice Std.U8) (j : Int) : Option Nat :=
    if 0 ≤ j then (s.val[j.toNat]?).map (fun b => b.val) else none

  @[reducible] def isZero (s : Slice Std.U8) (j : Int) : Prop := byteAt s j = some 48

  @[reducible] def isOne (s : Slice Std.U8) (j : Int) : Prop := byteAt s j = some 49

  def onesCount (s : Slice Std.U8) : Nat := s.val.countP (fun b => b.val == 49)

  def zerosIn (s : Slice Std.U8) (l r : Int) : Nat :=
    ((List.range s.val.length).filter
      (fun j => decide (l ≤ (j : Int) ∧ (j : Int) ≤ r ∧ isZero s (j : Int)))).length

  def zerosLeftAux (s : Slice Std.U8) (l : Int) : Nat → Int → Nat
    | 0, _ => 0
    | k + 1, j => if l ≤ j ∧ isZero s j then zerosLeftAux s l k (j - 1) + 1 else 0

  def zerosLeft (s : Slice Std.U8) (l a : Int) : Nat :=
    zerosLeftAux s l (a - l).toNat (a - 1)

  def zerosRightAux (s : Slice Std.U8) (r : Int) : Nat → Int → Nat
    | 0, _ => 0
    | k + 1, j => if j ≤ r ∧ isZero s j then zerosRightAux s r k (j + 1) + 1 else 0

  def zerosRight (s : Slice Std.U8) (r b : Int) : Nat :=
    zerosRightAux s r (r - b).toNat (b + 1)

  def tradeBlock (s : Slice Std.U8) (l r a b : Int) : Prop :=
    l < a ∧ a ≤ b ∧ b < r ∧ (∀ j : Int, a ≤ j → j ≤ b → isOne s j) ∧
      isZero s (a - 1) ∧ isZero s (b + 1)

  def hasTradeBlock (s : Slice Std.U8) (l r : Int) : Prop := ∃ a b : Int, tradeBlock s l r a b

  def tradeGain (s : Slice Std.U8) (l r a b : Int) : Nat :=
    zerosLeft s l a + zerosRight s r b

  noncomputable def tradeGains (s : Slice Std.U8) (l r : Int) : List Nat := by
    classical
    exact (List.range (r - l).toNat).flatMap (fun da =>
      (List.range (r - l).toNat).flatMap (fun db =>
        let a : Int := l + 1 + (da : Int)
        let b : Int := a + (db : Int)
        if tradeBlock s l r a b then [tradeGain s l r a b] else []))

  noncomputable def G (s : Slice Std.U8) (l r : Int) : Nat :=
    (tradeGains s l r).foldr max 0

  def queryEntry (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) :
      Option (alloc.vec.Vec Std.I64) :=
    queries.val[i]?

  def qL (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    ((queryEntry queries i).bind (fun v => (v.val[0]?).map (fun x => x.val))).getD 0

  def qR (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    ((queryEntry queries i).bind (fun v => (v.val[1]?).map (fun x => x.val))).getD 0

  /-- Whenever max_active_sections_after_trade(s, queries) returns a result out, len(out) = m and for every i with 0 <= i < m the following holds. Let ones(s) = #{j | 0 <= j < n and s[j] = 49}. Call a pair (a,b) an i-trade-block if l_i < a <= b < r_i, s[j] = 49 for every j with a <= j <= b, s[a-1] = 48, and s[b+1] = 48. For an i-trade-block (a,b), let L_i(a,b) = max { L >= 0 | a - L >= l_i and s[a-h] = 48 for every h with 1 <= h <= L } and R_i(a,b) = max { R >= 0 | b + R <= r_i and s[b+h] = 48 for every h with 1 <= h <= R }. Let G_i = max( {0} union { L_i(a,b) + R_i(a,b) | (a,b) is an i-trade-block } ). Then out[i] = ones(s) + G_i.
    Preconditions: Let n = len(s) and m = len(queries). Assume 1 <= n <= 100000. For every j with 0 <= j < n, s[j] is the ASCII byte for '0' (48) or '1' (49). Assume 1 <= m <= 100000. For every i with 0 <= i < m, len(queries[i]) = 2; write l_i = queries[i][0] and r_i = queries[i][1] as integers, and assume 0 <= l_i <= r_i < n. -/
  theorem spec_1
      (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
      (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
      (hqlen : ∀ i, i < queries.val.length →
        ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
      (hqrng : ∀ i, i < queries.val.length →
        0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)) :
      ∀ out, max_active_sections_after_trade s queries = ok out →
        out.val.length = queries.val.length ∧
        ∀ i, i < queries.val.length → ∀ (hi : i < out.val.length),
          (out.val[i]'hi).val =
            (onesCount s : Int) + (G s (qL queries i) (qR queries i) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
        (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
        (hqlen : ∀ i, i < queries.val.length →
          ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
        (hqrng : ∀ i, i < queries.val.length →
          0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)), ∀ out, max_active_sections_after_trade s queries = ok out →
          out.val.length = queries.val.length ∧
          ∀ i, i < queries.val.length → ∀ (hi : i < out.val.length),
            (out.val[i]'hi).val =
              (onesCount s : Int) + (G s (qL queries i) (qR queries i) : Int)) := by
    sorry

  /-- The function max_active_sections_after_trade(s, queries) returns a result out. Under these preconditions it does not fail due to integer overflow, out-of-bounds indexing, or panic.
    Preconditions: Let n = len(s) and m = len(queries). Assume 1 <= n <= 100000. For every j with 0 <= j < n, s[j] is the ASCII byte for '0' (48) or '1' (49). Assume 1 <= m <= 100000. For every i with 0 <= i < m, len(queries[i]) = 2; write l_i = queries[i][0] and r_i = queries[i][1] as integers, and assume 0 <= l_i <= r_i < n. -/
  theorem spec_2
      (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
      (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
      (hqlen : ∀ i, i < queries.val.length →
        ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
      (hqrng : ∀ i, i < queries.val.length →
        0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)) :
      ∃ out, max_active_sections_after_trade s queries = ok out := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
        (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
        (hqlen : ∀ i, i < queries.val.length →
          ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
        (hqrng : ∀ i, i < queries.val.length →
          0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)), ∃ out, max_active_sections_after_trade s queries = ok out) := by
    sorry

  /-- Whenever max_active_sections_after_trade(s, queries) returns a result out, for every i with 0 <= i < m, out[i] >= ones(s), where ones(s) = #{j | 0 <= j < n and s[j] = 49}.
    Preconditions: Let n = len(s) and m = len(queries). Assume 1 <= n <= 100000. For every j with 0 <= j < n, s[j] is the ASCII byte for '0' (48) or '1' (49). Assume 1 <= m <= 100000. For every i with 0 <= i < m, len(queries[i]) = 2; write l_i = queries[i][0] and r_i = queries[i][1] as integers, and assume 0 <= l_i <= r_i < n. -/
  theorem spec_3
      (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
      (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
      (hqlen : ∀ i, i < queries.val.length →
        ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
      (hqrng : ∀ i, i < queries.val.length →
        0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)) :
      ∀ out, max_active_sections_after_trade s queries = ok out →
        ∀ i, i < queries.val.length → ∀ (hi : i < out.val.length),
          (onesCount s : Int) ≤ (out.val[i]'hi).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
        (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
        (hqlen : ∀ i, i < queries.val.length →
          ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
        (hqrng : ∀ i, i < queries.val.length →
          0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)), ∀ out, max_active_sections_after_trade s queries = ok out →
          ∀ i, i < queries.val.length → ∀ (hi : i < out.val.length),
            (onesCount s : Int) ≤ (out.val[i]'hi).val) := by
    sorry

  /-- Whenever max_active_sections_after_trade(s, queries) returns a result out, for every i with 0 <= i < m, out[i] <= ones(s) + z_i, where ones(s) = #{j | 0 <= j < n and s[j] = 49} and z_i = #{j | l_i <= j <= r_i and s[j] = 48}.
    Preconditions: Let n = len(s) and m = len(queries). Assume 1 <= n <= 100000. For every j with 0 <= j < n, s[j] is the ASCII byte for '0' (48) or '1' (49). Assume 1 <= m <= 100000. For every i with 0 <= i < m, len(queries[i]) = 2; write l_i = queries[i][0] and r_i = queries[i][1] as integers, and assume 0 <= l_i <= r_i < n. -/
  theorem spec_4
      (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
      (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
      (hqlen : ∀ i, i < queries.val.length →
        ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
      (hqrng : ∀ i, i < queries.val.length →
        0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)) :
      ∀ out, max_active_sections_after_trade s queries = ok out →
        ∀ i, i < queries.val.length → ∀ (hi : i < out.val.length),
          (out.val[i]'hi).val ≤
            (onesCount s : Int) + (zerosIn s (qL queries i) (qR queries i) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
        (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
        (hqlen : ∀ i, i < queries.val.length →
          ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
        (hqrng : ∀ i, i < queries.val.length →
          0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)), ∀ out, max_active_sections_after_trade s queries = ok out →
          ∀ i, i < queries.val.length → ∀ (hi : i < out.val.length),
            (out.val[i]'hi).val ≤
              (onesCount s : Int) + (zerosIn s (qL queries i) (qR queries i) : Int)) := by
    sorry

  /-- Whenever max_active_sections_after_trade(s, queries) returns a result out, for every i with 0 <= i < m, if there is no pair (a,b) such that l_i < a <= b < r_i, s[j] = 49 for all j with a <= j <= b, s[a-1] = 48, and s[b+1] = 48, then out[i] = ones(s), where ones(s) = #{j | 0 <= j < n and s[j] = 49}.
    Preconditions: Let n = len(s) and m = len(queries). Assume 1 <= n <= 100000. For every j with 0 <= j < n, s[j] is the ASCII byte for '0' (48) or '1' (49). Assume 1 <= m <= 100000. For every i with 0 <= i < m, len(queries[i]) = 2; write l_i = queries[i][0] and r_i = queries[i][1] as integers, and assume 0 <= l_i <= r_i < n. -/
  theorem spec_5
      (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
      (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
      (hqlen : ∀ i, i < queries.val.length →
        ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
      (hqrng : ∀ i, i < queries.val.length →
        0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)) :
      ∀ out, max_active_sections_after_trade s queries = ok out →
        ∀ i, i < queries.val.length →
          ¬ hasTradeBlock s (qL queries i) (qR queries i) →
          ∀ (hi : i < out.val.length), (out.val[i]'hi).val = (onesCount s : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
        (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
        (hqlen : ∀ i, i < queries.val.length →
          ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
        (hqrng : ∀ i, i < queries.val.length →
          0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)), ∀ out, max_active_sections_after_trade s queries = ok out →
          ∀ i, i < queries.val.length →
            ¬ hasTradeBlock s (qL queries i) (qR queries i) →
            ∀ (hi : i < out.val.length), (out.val[i]'hi).val = (onesCount s : Int)) := by
    sorry

  /-- Whenever max_active_sections_after_trade(s, queries) returns a result out, for every i with 0 <= i < m and every pair (a,b) satisfying l_i < a <= b < r_i, s[j] = 49 for all j with a <= j <= b, s[a-1] = 48, and s[b+1] = 48, we have out[i] >= ones(s) + L + R, where ones(s) = #{j | 0 <= j < n and s[j] = 49}, L = max { L0 >= 0 | a - L0 >= l_i and s[a-h] = 48 for every h with 1 <= h <= L0 }, and R = max { R0 >= 0 | b + R0 <= r_i and s[b+h] = 48 for every h with 1 <= h <= R0 }.
    Preconditions: Let n = len(s) and m = len(queries). Assume 1 <= n <= 100000. For every j with 0 <= j < n, s[j] is the ASCII byte for '0' (48) or '1' (49). Assume 1 <= m <= 100000. For every i with 0 <= i < m, len(queries[i]) = 2; write l_i = queries[i][0] and r_i = queries[i][1] as integers, and assume 0 <= l_i <= r_i < n. -/
  theorem spec_6
      (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
      (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
      (hqlen : ∀ i, i < queries.val.length →
        ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
      (hqrng : ∀ i, i < queries.val.length →
        0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)) :
      ∀ out, max_active_sections_after_trade s queries = ok out →
        ∀ i, i < queries.val.length →
          ∀ a b : Int, tradeBlock s (qL queries i) (qR queries i) a b →
          ∀ (hi : i < out.val.length),
            (onesCount s : Int) + (zerosLeft s (qL queries i) a : Int) +
                (zerosRight s (qR queries i) b : Int) ≤
              (out.val[i]'hi).val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
        (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
        (hqlen : ∀ i, i < queries.val.length →
          ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
        (hqrng : ∀ i, i < queries.val.length →
          0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)), ∀ out, max_active_sections_after_trade s queries = ok out →
          ∀ i, i < queries.val.length →
            ∀ a b : Int, tradeBlock s (qL queries i) (qR queries i) a b →
            ∀ (hi : i < out.val.length),
              (onesCount s : Int) + (zerosLeft s (qL queries i) a : Int) +
                  (zerosRight s (qR queries i) b : Int) ≤
                (out.val[i]'hi).val) := by
    sorry

  /-- Whenever max_active_sections_after_trade(s, queries) returns a result out, for every i with 0 <= i < m, either out[i] = ones(s), or there exists an i-trade-block (a,b) such that out[i] = ones(s) + L_i(a,b) + R_i(a,b). Here ones(s) = #{j | 0 <= j < n and s[j] = 49}; an i-trade-block is a pair (a,b) with l_i < a <= b < r_i, s[j] = 49 for all a <= j <= b, s[a-1] = 48, and s[b+1] = 48; L_i(a,b) = max { L >= 0 | a - L >= l_i and s[a-h] = 48 for all 1 <= h <= L }; and R_i(a,b) = max { R >= 0 | b + R <= r_i and s[b+h] = 48 for all 1 <= h <= R }.
    Preconditions: Let n = len(s) and m = len(queries). Assume 1 <= n <= 100000. For every j with 0 <= j < n, s[j] is the ASCII byte for '0' (48) or '1' (49). Assume 1 <= m <= 100000. For every i with 0 <= i < m, len(queries[i]) = 2; write l_i = queries[i][0] and r_i = queries[i][1] as integers, and assume 0 <= l_i <= r_i < n. -/
  theorem spec_7
      (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
      (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
      (hqlen : ∀ i, i < queries.val.length →
        ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
      (hqrng : ∀ i, i < queries.val.length →
        0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)) :
      ∀ out, max_active_sections_after_trade s queries = ok out →
        ∀ i, i < queries.val.length → ∀ (hi : i < out.val.length),
          (out.val[i]'hi).val = (onesCount s : Int) ∨
            ∃ a b : Int, tradeBlock s (qL queries i) (qR queries i) a b ∧
              (out.val[i]'hi).val = (onesCount s : Int) + (zerosLeft s (qL queries i) a : Int) +
                (zerosRight s (qR queries i) b : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
        (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
        (hqlen : ∀ i, i < queries.val.length →
          ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
        (hqrng : ∀ i, i < queries.val.length →
          0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)), ∀ out, max_active_sections_after_trade s queries = ok out →
          ∀ i, i < queries.val.length → ∀ (hi : i < out.val.length),
            (out.val[i]'hi).val = (onesCount s : Int) ∨
              ∃ a b : Int, tradeBlock s (qL queries i) (qR queries i) a b ∧
                (out.val[i]'hi).val = (onesCount s : Int) + (zerosLeft s (qL queries i) a : Int) +
                  (zerosRight s (qR queries i) b : Int)) := by
    sorry

  /-- Whenever max_active_sections_after_trade(s, queries) returns a result out, for all i and k with 0 <= i < m and 0 <= k < m, if l_i <= l_k and r_k <= r_i, then out[i] >= out[k].
    Preconditions: Let n = len(s) and m = len(queries). Assume 1 <= n <= 100000. For every j with 0 <= j < n, s[j] is the ASCII byte for '0' (48) or '1' (49). Assume 1 <= m <= 100000. For every i with 0 <= i < m, len(queries[i]) = 2; write l_i = queries[i][0] and r_i = queries[i][1] as integers, and assume 0 <= l_i <= r_i < n. -/
  theorem spec_8
      (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
      (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
      (hqlen : ∀ i, i < queries.val.length →
        ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
      (hqrng : ∀ i, i < queries.val.length →
        0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)) :
      ∀ out, max_active_sections_after_trade s queries = ok out →
        ∀ i k, i < queries.val.length → k < queries.val.length →
          qL queries i ≤ qL queries k → qR queries k ≤ qR queries i →
          ∀ (hi : i < out.val.length) (hk : k < out.val.length),
            (out.val[k]'hk).val ≤ (out.val[i]'hi).val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
        (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
        (hqlen : ∀ i, i < queries.val.length →
          ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
        (hqrng : ∀ i, i < queries.val.length →
          0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int)), ∀ out, max_active_sections_after_trade s queries = ok out →
          ∀ i k, i < queries.val.length → k < queries.val.length →
            qL queries i ≤ qL queries k → qR queries k ≤ qR queries i →
            ∀ (hi : i < out.val.length) (hk : k < out.val.length),
              (out.val[k]'hk).val ≤ (out.val[i]'hi).val) := by
    sorry

  /-- Whenever max_active_sections_after_trade(s, queries) returns out and max_active_sections_after_trade(s, queries2) returns out2, if queries2 is a permutation of queries, i.e. there exists a bijection pi on {0,...,m-1} such that queries2[i] = queries[pi(i)] for every i, then len(out2) = m and out2[i] = out[pi(i)] for every i with 0 <= i < m.
    Preconditions: Let n = len(s) and m = len(queries). Assume 1 <= n <= 100000. For every j with 0 <= j < n, s[j] is the ASCII byte for '0' (48) or '1' (49). Assume 1 <= m <= 100000. For every i with 0 <= i < m, len(queries[i]) = 2; write l_i = queries[i][0] and r_i = queries[i][1] as integers, and assume 0 <= l_i <= r_i < n. Let queries2 be another Slice of Vec I64 with len(queries2) = m, and assume every queries2[i] has length 2 with entries between 0 and n-1 and first entry <= second entry. -/
  theorem spec_9
      (s : Slice Std.U8) (queries queries2 : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
      (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
      (hqlen : ∀ i, i < queries.val.length →
        ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
      (hqrng : ∀ i, i < queries.val.length →
        0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int))
      (hq2len : queries2.val.length = queries.val.length)
      (hq2len2 : ∀ i, i < queries2.val.length →
        ∃ v, queryEntry queries2 i = some v ∧ v.val.length = 2)
      (hq2rng : ∀ i, i < queries2.val.length →
        0 ≤ qL queries2 i ∧ qL queries2 i ≤ qR queries2 i ∧
          qR queries2 i < (s.val.length : Int)) :
      ∀ out out2, max_active_sections_after_trade s queries = ok out →
        max_active_sections_after_trade s queries2 = ok out2 →
        ∀ (pi : Equiv.Perm (Fin queries.val.length)),
          (∀ i (hi : i < queries.val.length),
            queries2.val[i]? = queries.val[(pi ⟨i, hi⟩).val]?) →
          out2.val.length = queries.val.length ∧
            ∀ i (hi : i < queries.val.length),
              out2.val[i]? = out.val[(pi ⟨i, hi⟩).val]? := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (queries queries2 : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
        (hs : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 100000)
        (hqlen : ∀ i, i < queries.val.length →
          ∃ v, queryEntry queries i = some v ∧ v.val.length = 2)
        (hqrng : ∀ i, i < queries.val.length →
          0 ≤ qL queries i ∧ qL queries i ≤ qR queries i ∧ qR queries i < (s.val.length : Int))
        (hq2len : queries2.val.length = queries.val.length)
        (hq2len2 : ∀ i, i < queries2.val.length →
          ∃ v, queryEntry queries2 i = some v ∧ v.val.length = 2)
        (hq2rng : ∀ i, i < queries2.val.length →
          0 ≤ qL queries2 i ∧ qL queries2 i ≤ qR queries2 i ∧
            qR queries2 i < (s.val.length : Int)), ∀ out out2, max_active_sections_after_trade s queries = ok out →
          max_active_sections_after_trade s queries2 = ok out2 →
          ∀ (pi : Equiv.Perm (Fin queries.val.length)),
            (∀ i (hi : i < queries.val.length),
              queries2.val[i]? = queries.val[(pi ⟨i, hi⟩).val]?) →
            out2.val.length = queries.val.length ∧
              ∀ i (hi : i < queries.val.length),
                out2.val[i]? = out.val[(pi ⟨i, hi⟩).val]?) := by
    sorry

  end AegisSpec.MaxActiveSectionsAfterTrade
