import Aegis.PlatesBetweenCandles.Code.Funs

/-!
# Specifications of `Aegis.PlatesBetweenCandles.plates_between_candles`

LeetCode problem `plates-between-candles`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PlatesBetweenCandles

  def sLen (s : Slice U8) : Nat := (Slice.len s).val

  def sByte (s : Slice U8) (p : Nat) : Option Nat := (s.val[p]?).map (fun b => b.val)

  def isPlate (s : Slice U8) (L R : Int) (p : Nat) : Bool :=
    decide (L ≤ (p : Int) ∧ (p : Int) ≤ R ∧ sByte s p = some 42) &&
      (List.range (sLen s)).any
        (fun (a : Nat) => decide (L ≤ (a : Int) ∧ (a : Int) < (p : Int) ∧
          sByte s a = some 124)) &&
      (List.range (sLen s)).any
        (fun (b : Nat) => decide ((p : Int) < (b : Int) ∧ (b : Int) ≤ R ∧
          sByte s b = some 124))

  def plateCount (s : Slice U8) (L R : Int) : Nat :=
    ((List.range (sLen s)).filter (fun (p : Nat) => isPlate s L R p)).length

  def starCountBetween (s : Slice U8) (a b : Int) : Nat :=
    ((List.range (sLen s)).filter
      (fun (p : Nat) => decide (a < (p : Int) ∧ (p : Int) < b ∧ sByte s p = some 42))).length

  def IsLeastPipe (s : Slice U8) (L R : Int) (a : Nat) : Prop :=
    L ≤ (a : Int) ∧ (a : Int) ≤ R ∧ sByte s a = some 124 ∧
      ∀ i : Nat, L ≤ (i : Int) → (i : Int) ≤ R → sByte s i = some 124 → (a : Int) ≤ (i : Int)

  def IsGreatestPipe (s : Slice U8) (L R : Int) (b : Nat) : Prop :=
    L ≤ (b : Int) ∧ (b : Int) ≤ R ∧ sByte s b = some 124 ∧
      ∀ i : Nat, L ≤ (i : Int) → (i : Int) ≤ R → sByte s i = some 124 → (i : Int) ≤ (b : Int)

  def qLen (queries : Slice (alloc.vec.Vec I64)) : Nat := (Slice.len queries).val

  def queryContents (queries : Slice (alloc.vec.Vec I64)) (k : Nat) : Option (List Int) :=
    (queries.val[k]?).map (fun q => q.val.map (fun x => x.val))

  def queryLeft (queries : Slice (alloc.vec.Vec I64)) (k : Nat) : Option Int :=
    (queryContents queries k).bind (fun l => l[0]?)

  def queryRight (queries : Slice (alloc.vec.Vec I64)) (k : Nat) : Option Int :=
    (queryContents queries k).bind (fun l => l[1]?)

  def resultAt (r : alloc.vec.Vec I64) (k : Nat) : Option Int := (r.val[k]?).map (fun x => x.val)

  /-- Whenever the function returns a result r, len(r) = len(queries) and for every k with 0 <= k < len(queries), writing L = L_k and R = R_k, r[k] is the number of indices p such that L <= p <= R, s[p] = 42, and there exist indices a and b with L <= a < p < b <= R, s[a] = 124, and s[b] = 124.
    Preconditions: Preconditions: s is a byte slice over the ASCII characters '*' (byte 42) and '|' (byte 124), with 3 <= len(s) <= 100000; queries is a nonempty slice with 1 <= len(queries) <= 100000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; and, writing L_k = queries[k][0] and R_k = queries[k][1], we have 0 <= L_k <= R_k < len(s). -/
  theorem spec_1 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hbytes : ∀ b ∈ s.val, b.val = 42 ∨ b.val = 124)
      (hs_lower : 3 ≤ (Slice.len s).val) (hs_upper : (Slice.len s).val ≤ 100000)
      (hq_nonempty : 1 ≤ (Slice.len queries).val) (hq_upper : (Slice.len queries).val ≤ 100000)
      (hq_len : ∀ k : Nat, k < (Slice.len queries).val →
        (queryContents queries k).map List.length = some 2)
      (hq_bounds : ∀ k : Nat, k < (Slice.len queries).val →
        ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
          0 ≤ L ∧ L ≤ R ∧ R < ((Slice.len s).val : Int)) :
      ∀ r, Aegis.PlatesBetweenCandles.plates_between_candles s queries = ok r →
        r.val.length = (Slice.len queries).val ∧
          ∀ k : Nat, k < (Slice.len queries).val →
            ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
              resultAt r k = some ((plateCount s L R : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hbytes : ∀ b ∈ s.val, b.val = 42 ∨ b.val = 124)
        (hs_lower : 3 ≤ (Slice.len s).val) (hs_upper : (Slice.len s).val ≤ 100000)
        (hq_nonempty : 1 ≤ (Slice.len queries).val) (hq_upper : (Slice.len queries).val ≤ 100000)
        (hq_len : ∀ k : Nat, k < (Slice.len queries).val →
          (queryContents queries k).map List.length = some 2)
        (hq_bounds : ∀ k : Nat, k < (Slice.len queries).val →
          ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
            0 ≤ L ∧ L ≤ R ∧ R < ((Slice.len s).val : Int)), ∀ r, Aegis.PlatesBetweenCandles.plates_between_candles s queries = ok r →
          r.val.length = (Slice.len queries).val ∧
            ∀ k : Nat, k < (Slice.len queries).val →
              ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
                resultAt r k = some ((plateCount s L R : Nat) : Int)) := by
    sorry

  /-- For every s and queries satisfying the preconditions, the function returns a result r (it does not fail).
    Preconditions: Preconditions: s is a byte slice over the ASCII characters '*' (byte 42) and '|' (byte 124), with 3 <= len(s) <= 100000; queries is a nonempty slice with 1 <= len(queries) <= 100000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; and, writing L_k = queries[k][0] and R_k = queries[k][1], we have 0 <= L_k <= R_k < len(s). -/
  theorem spec_2 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hbytes : ∀ b ∈ s.val, b.val = 42 ∨ b.val = 124)
      (hs_lower : 3 ≤ (Slice.len s).val) (hs_upper : (Slice.len s).val ≤ 100000)
      (hq_nonempty : 1 ≤ (Slice.len queries).val) (hq_upper : (Slice.len queries).val ≤ 100000)
      (hq_len : ∀ k : Nat, k < (Slice.len queries).val →
        (queryContents queries k).map List.length = some 2)
      (hq_bounds : ∀ k : Nat, k < (Slice.len queries).val →
        ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
          0 ≤ L ∧ L ≤ R ∧ R < ((Slice.len s).val : Int)) :
      ∃ r, Aegis.PlatesBetweenCandles.plates_between_candles s queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hbytes : ∀ b ∈ s.val, b.val = 42 ∨ b.val = 124)
        (hs_lower : 3 ≤ (Slice.len s).val) (hs_upper : (Slice.len s).val ≤ 100000)
        (hq_nonempty : 1 ≤ (Slice.len queries).val) (hq_upper : (Slice.len queries).val ≤ 100000)
        (hq_len : ∀ k : Nat, k < (Slice.len queries).val →
          (queryContents queries k).map List.length = some 2)
        (hq_bounds : ∀ k : Nat, k < (Slice.len queries).val →
          ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
            0 ≤ L ∧ L ≤ R ∧ R < ((Slice.len s).val : Int)), ∃ r, Aegis.PlatesBetweenCandles.plates_between_candles s queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(queries), if there are at least two indices i with L_k <= i <= R_k and s[i] = 124, and a is the least such index and b is the greatest such index, then r[k] equals the number of indices p with a < p < b and s[p] = 42.
    Preconditions: Preconditions: s is a byte slice over the ASCII characters '*' (byte 42) and '|' (byte 124), with 3 <= len(s) <= 100000; queries is a nonempty slice with 1 <= len(queries) <= 100000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; and, writing L_k = queries[k][0] and R_k = queries[k][1], we have 0 <= L_k <= R_k < len(s). -/
  theorem spec_3 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hbytes : ∀ b ∈ s.val, b.val = 42 ∨ b.val = 124)
      (hs_lower : 3 ≤ (Slice.len s).val) (hs_upper : (Slice.len s).val ≤ 100000)
      (hq_nonempty : 1 ≤ (Slice.len queries).val) (hq_upper : (Slice.len queries).val ≤ 100000)
      (hq_len : ∀ k : Nat, k < (Slice.len queries).val →
        (queryContents queries k).map List.length = some 2)
      (hq_bounds : ∀ k : Nat, k < (Slice.len queries).val →
        ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
          0 ≤ L ∧ L ≤ R ∧ R < ((Slice.len s).val : Int)) :
      ∀ r, Aegis.PlatesBetweenCandles.plates_between_candles s queries = ok r →
        ∀ k : Nat, k < (Slice.len queries).val →
          ∀ L R : Int, queryLeft queries k = some L → queryRight queries k = some R →
            ∀ a b : Nat, IsLeastPipe s L R a → IsGreatestPipe s L R b → (a : Int) < (b : Int) →
              resultAt r k = some ((starCountBetween s (a : Int) (b : Int) : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hbytes : ∀ b ∈ s.val, b.val = 42 ∨ b.val = 124)
        (hs_lower : 3 ≤ (Slice.len s).val) (hs_upper : (Slice.len s).val ≤ 100000)
        (hq_nonempty : 1 ≤ (Slice.len queries).val) (hq_upper : (Slice.len queries).val ≤ 100000)
        (hq_len : ∀ k : Nat, k < (Slice.len queries).val →
          (queryContents queries k).map List.length = some 2)
        (hq_bounds : ∀ k : Nat, k < (Slice.len queries).val →
          ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
            0 ≤ L ∧ L ≤ R ∧ R < ((Slice.len s).val : Int)), ∀ r, Aegis.PlatesBetweenCandles.plates_between_candles s queries = ok r →
          ∀ k : Nat, k < (Slice.len queries).val →
            ∀ L R : Int, queryLeft queries k = some L → queryRight queries k = some R →
              ∀ a b : Nat, IsLeastPipe s L R a → IsGreatestPipe s L R b → (a : Int) < (b : Int) →
                resultAt r k = some ((starCountBetween s (a : Int) (b : Int) : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every k and j with 0 <= k < len(queries) and 0 <= j < len(queries), if L_j <= L_k and R_k <= R_j, then r[k] <= r[j].
    Preconditions: Preconditions: s is a byte slice over the ASCII characters '*' (byte 42) and '|' (byte 124), with 3 <= len(s) <= 100000; queries is a nonempty slice with 1 <= len(queries) <= 100000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; and, writing L_k = queries[k][0] and R_k = queries[k][1], we have 0 <= L_k <= R_k < len(s). -/
  theorem spec_4 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hbytes : ∀ b ∈ s.val, b.val = 42 ∨ b.val = 124)
      (hs_lower : 3 ≤ (Slice.len s).val) (hs_upper : (Slice.len s).val ≤ 100000)
      (hq_nonempty : 1 ≤ (Slice.len queries).val) (hq_upper : (Slice.len queries).val ≤ 100000)
      (hq_len : ∀ k : Nat, k < (Slice.len queries).val →
        (queryContents queries k).map List.length = some 2)
      (hq_bounds : ∀ k : Nat, k < (Slice.len queries).val →
        ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
          0 ≤ L ∧ L ≤ R ∧ R < ((Slice.len s).val : Int)) :
      ∀ r, Aegis.PlatesBetweenCandles.plates_between_candles s queries = ok r →
        ∀ k j : Nat, k < (Slice.len queries).val → j < (Slice.len queries).val →
          ∀ Lk Rk Lj Rj : Int,
            queryLeft queries k = some Lk → queryRight queries k = some Rk →
            queryLeft queries j = some Lj → queryRight queries j = some Rj →
            Lj ≤ Lk → Rk ≤ Rj →
              ∀ ck cj : Int, resultAt r k = some ck → resultAt r j = some cj → ck ≤ cj := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hbytes : ∀ b ∈ s.val, b.val = 42 ∨ b.val = 124)
        (hs_lower : 3 ≤ (Slice.len s).val) (hs_upper : (Slice.len s).val ≤ 100000)
        (hq_nonempty : 1 ≤ (Slice.len queries).val) (hq_upper : (Slice.len queries).val ≤ 100000)
        (hq_len : ∀ k : Nat, k < (Slice.len queries).val →
          (queryContents queries k).map List.length = some 2)
        (hq_bounds : ∀ k : Nat, k < (Slice.len queries).val →
          ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
            0 ≤ L ∧ L ≤ R ∧ R < ((Slice.len s).val : Int)), ∀ r, Aegis.PlatesBetweenCandles.plates_between_candles s queries = ok r →
          ∀ k j : Nat, k < (Slice.len queries).val → j < (Slice.len queries).val →
            ∀ Lk Rk Lj Rj : Int,
              queryLeft queries k = some Lk → queryRight queries k = some Rk →
              queryLeft queries j = some Lj → queryRight queries j = some Rj →
              Lj ≤ Lk → Rk ≤ Rj →
                ∀ ck cj : Int, resultAt r k = some ck → resultAt r j = some cj → ck ≤ cj) := by
    sorry

  /-- Whenever the function returns a result r, for every k and j with 0 <= k < len(queries) and 0 <= j < len(queries), if R_k - L_k = R_j - L_j and for every t with 0 <= t <= R_k - L_k we have s[L_k + t] = s[L_j + t], then r[k] = r[j].
    Preconditions: Preconditions: s is a byte slice over the ASCII characters '*' (byte 42) and '|' (byte 124), with 3 <= len(s) <= 100000; queries is a nonempty slice with 1 <= len(queries) <= 100000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; and, writing L_k = queries[k][0] and R_k = queries[k][1], we have 0 <= L_k <= R_k < len(s). -/
  theorem spec_5 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hbytes : ∀ b ∈ s.val, b.val = 42 ∨ b.val = 124)
      (hs_lower : 3 ≤ (Slice.len s).val) (hs_upper : (Slice.len s).val ≤ 100000)
      (hq_nonempty : 1 ≤ (Slice.len queries).val) (hq_upper : (Slice.len queries).val ≤ 100000)
      (hq_len : ∀ k : Nat, k < (Slice.len queries).val →
        (queryContents queries k).map List.length = some 2)
      (hq_bounds : ∀ k : Nat, k < (Slice.len queries).val →
        ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
          0 ≤ L ∧ L ≤ R ∧ R < ((Slice.len s).val : Int)) :
      ∀ r, Aegis.PlatesBetweenCandles.plates_between_candles s queries = ok r →
        ∀ k j : Nat, k < (Slice.len queries).val → j < (Slice.len queries).val →
          ∀ Lk Rk Lj Rj : Int,
            queryLeft queries k = some Lk → queryRight queries k = some Rk →
            queryLeft queries j = some Lj → queryRight queries j = some Rj →
            Rk - Lk = Rj - Lj →
              (∀ t : Int, 0 ≤ t → t ≤ Rk - Lk →
                sByte s (Lk + t).toNat = sByte s (Lj + t).toNat) →
                ∀ ck cj : Int, resultAt r k = some ck → resultAt r j = some cj → ck = cj := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hbytes : ∀ b ∈ s.val, b.val = 42 ∨ b.val = 124)
        (hs_lower : 3 ≤ (Slice.len s).val) (hs_upper : (Slice.len s).val ≤ 100000)
        (hq_nonempty : 1 ≤ (Slice.len queries).val) (hq_upper : (Slice.len queries).val ≤ 100000)
        (hq_len : ∀ k : Nat, k < (Slice.len queries).val →
          (queryContents queries k).map List.length = some 2)
        (hq_bounds : ∀ k : Nat, k < (Slice.len queries).val →
          ∃ L R : Int, queryLeft queries k = some L ∧ queryRight queries k = some R ∧
            0 ≤ L ∧ L ≤ R ∧ R < ((Slice.len s).val : Int)), ∀ r, Aegis.PlatesBetweenCandles.plates_between_candles s queries = ok r →
          ∀ k j : Nat, k < (Slice.len queries).val → j < (Slice.len queries).val →
            ∀ Lk Rk Lj Rj : Int,
              queryLeft queries k = some Lk → queryRight queries k = some Rk →
              queryLeft queries j = some Lj → queryRight queries j = some Rj →
              Rk - Lk = Rj - Lj →
                (∀ t : Int, 0 ≤ t → t ≤ Rk - Lk →
                  sByte s (Lk + t).toNat = sByte s (Lj + t).toNat) →
                  ∀ ck cj : Int, resultAt r k = some ck → resultAt r j = some cj → ck = cj) := by
    sorry

  end AegisSpec.PlatesBetweenCandles
