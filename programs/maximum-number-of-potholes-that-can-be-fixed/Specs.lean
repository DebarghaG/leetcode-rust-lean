import Aegis.MaxPotholes.Code.Funs

/-!
# Specifications of `Aegis.MaxPotholes.max_potholes`

LeetCode problem `maximum-number-of-potholes-that-can-be-fixed`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxPotholes

def dotByte : ℕ := 46

def xByte : ℕ := 120

def isX (b : ℕ) : Bool := b == xByte

def roadBytes (road : Slice Std.U8) : List ℕ := road.val.map (fun b => b.val)

def runLensAux (p : ℕ → Bool) (cur : ℕ) (l : List ℕ) : List ℕ :=
  match l with
  | [] => if cur = 0 then [] else [cur]
  | b :: l =>
    if p b then runLensAux p (cur + 1) l
    else if cur = 0 then runLensAux p 0 l
    else cur :: runLensAux p 0 l

def xRunLens (bytes : List ℕ) : List ℕ := runLensAux isX 0 bytes

def xCount (bytes : List ℕ) : ℕ := bytes.countP isX

def roadRunLens (road : Slice Std.U8) : List ℕ := xRunLens (roadBytes road)

def roadXCount (road : Slice Std.U8) : ℕ := xCount (roadBytes road)

def roadRunCount (road : Slice Std.U8) : ℕ := (roadRunLens road).length

def runCost (n : ℕ) : ℕ := if n = 0 then 0 else n + 1

def totalCost (ns : List ℕ) : ℕ := (ns.map runCost).sum

def totalCostSucc (amts : List ℕ) : ℕ := (amts.map (fun a => a + 1)).sum

def IsFeasible (Ls ns : List ℕ) (b : ℤ) : Prop :=
  ns.length = Ls.length ∧ List.Forall₂ (fun n L => n ≤ L) ns Ls ∧ (totalCost ns : ℤ) ≤ b

def Witness (Ls ks amts : List ℕ) (b r : ℤ) : Prop :=
  amts.length = ks.length ∧
    List.Pairwise (· < ·) ks ∧
    (∀ k ∈ ks, k < Ls.length) ∧
    (∀ a ∈ amts, 0 < a) ∧
    List.Forall₂ (fun k a => a ≤ Ls.getD k 0) ks amts ∧
    (amts.sum : ℤ) = r ∧
    (totalCostSucc amts : ℤ) ≤ b

def SupportsX (xs ys : List ℕ) : Prop :=
  ∀ i, i < xs.length → xs.getD i 0 = xByte → ys.getD i 0 = xByte

def roadRev (road : Slice Std.U8) : Slice Std.U8 :=
  ⟨road.val.reverse.length, Aeneas.Data.ListN.ListN.fromList road.val.reverse, by
    simpa [Slice.val, Aeneas.Data.ListN.ListN_length] using road.bound⟩

theorem roadRev_val (road : Slice Std.U8) : (roadRev road).val = road.val.reverse := by
  simp [roadRev, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

/-- Let L_1, ..., L_m be the lengths of the maximal nonempty contiguous blocks of indices i with road[i] = 'x' (the x-runs), in left-to-right order; if road has no 'x' then m = 0. The function returns a result r such that: (1) there exist integers n_1, ..., n_m with 0 <= n_i <= L_i for every i, sum_{i=1..m} n_i = r, and sum_{i=1..m} (n_i + 1 if n_i > 0 else 0) <= budget; and (2) for every tuple of integers q_1, ..., q_m with 0 <= q_i <= L_i for every i and sum_{i=1..m} (q_i + 1 if q_i > 0 else 0) <= budget, we have sum_{i=1..m} q_i <= r.
  Preconditions: len(road) is between 1 and 100000 inclusive; every byte of road is the ASCII code for '.' or the ASCII code for 'x'; 1 <= budget <= 100001; budget is an i64 value in range. -/
theorem spec_1 (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001) :
    ∃ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r ∧
        (∃ ns : List ℕ, IsFeasible (roadRunLens road) ns budget.val ∧ (ns.sum : ℤ) = r.val) ∧
        (∀ qs : List ℕ,
          IsFeasible (roadRunLens road) qs budget.val → (qs.sum : ℤ) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001), ∃ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r ∧
        (∃ ns : List ℕ, IsFeasible (roadRunLens road) ns budget.val ∧ (ns.sum : ℤ) = r.val) ∧
        (∀ qs : List ℕ,
          IsFeasible (roadRunLens road) qs budget.val → (qs.sum : ℤ) ≤ r.val)) := by
  sorry

/-- For every input satisfying the preconditions, max_potholes(road, budget) returns a value r; it does not fail due to integer overflow, out-of-bounds indexing, or panic.
  Preconditions: len(road) is between 1 and 100000 inclusive; every byte of road is the ASCII code for '.' or the ASCII code for 'x'; 1 <= budget <= 100001; budget is an i64 value in range. -/
theorem spec_2 (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001) :
    ∃ r : Std.I64, Aegis.MaxPotholes.max_potholes road budget = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001), ∃ r : Std.I64, Aegis.MaxPotholes.max_potholes road budget = ok r) := by
  sorry

/-- Let X be the number of indices i with 0 <= i < len(road) and road[i] = 'x'. Whenever the function returns a result r, 0 <= r <= X.
  Preconditions: len(road) is between 1 and 100000 inclusive; every byte of road is the ASCII code for '.' or the ASCII code for 'x'; 1 <= budget <= 100001; budget is an i64 value in range. -/
theorem spec_3 (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001) :
    ∀ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r →
        0 ≤ r.val ∧ r.val ≤ (roadXCount road : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001), ∀ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r →
        0 ≤ r.val ∧ r.val ≤ (roadXCount road : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r <= max(0, budget - 1). In particular, if r > 0 then r + 1 <= budget.
  Preconditions: len(road) is between 1 and 100000 inclusive; every byte of road is the ASCII code for '.' or the ASCII code for 'x'; 1 <= budget <= 100001; budget is an i64 value in range. -/
theorem spec_4 (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001) :
    ∀ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r →
        r.val ≤ max 0 (budget.val - 1) ∧ (0 < r.val → r.val + 1 ≤ budget.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001), ∀ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r →
        r.val ≤ max 0 (budget.val - 1) ∧ (0 < r.val → r.val + 1 ≤ budget.val)) := by
  sorry

/-- Let X be the number of indices i with 0 <= i < len(road) and road[i] = 'x'. The function returns r = 0 if and only if X = 0 or budget < 2.
  Preconditions: len(road) is between 1 and 100000 inclusive; every byte of road is the ASCII code for '.' or the ASCII code for 'x'; 1 <= budget <= 100001; budget is an i64 value in range. -/
theorem spec_5 (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001) :
    ∃ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r ∧
        (r.val = 0 ↔ (roadXCount road = 0 ∨ budget.val < 2)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001), ∃ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r ∧
        (r.val = 0 ↔ (roadXCount road = 0 ∨ budget.val < 2))) := by
  sorry

/-- Let X be the number of indices i with road[i] = 'x', and let m be the number of maximal x-runs in road. If X + m <= budget, then the function returns r = X.
  Preconditions: len(road) is between 1 and 100000 inclusive; every byte of road is the ASCII code for '.' or the ASCII code for 'x'; 1 <= budget <= 100001; budget is an i64 value in range. -/
theorem spec_6 (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001)
    (hfit : (roadXCount road : ℤ) + (roadRunCount road : ℤ) ≤ budget.val) :
    ∀ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r → r.val = (roadXCount road : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001)
    (hfit : (roadXCount road : ℤ) + (roadRunCount road : ℤ) ≤ budget.val), ∀ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r → r.val = (roadXCount road : ℤ)) := by
  sorry

/-- Let L be the length of that unique x-run. The function returns r = 0 if budget < 2, and r = min(L, budget - 1) if budget >= 2.
  Preconditions: The general preconditions hold, and road has exactly one maximal nonempty contiguous block of indices i with road[i] = 'x'. -/
theorem spec_7 (road : Slice Std.U8) (budget : Std.I64) (L : ℕ)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001)
    (hL : roadRunLens road = [L]) :
    ∃ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r ∧
        ((budget.val < 2 ∧ r.val = 0) ∨
          (2 ≤ budget.val ∧ r.val = min (L : ℤ) (budget.val - 1))) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (road : Slice Std.U8) (budget : Std.I64) (L : ℕ)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001)
    (hL : roadRunLens road = [L]), ∃ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r ∧
        ((budget.val < 2 ∧ r.val = 0) ∨
          (2 ≤ budget.val ∧ r.val = min (L : ℤ) (budget.val - 1)))) := by
  sorry

/-- Let X be the number of indices i with road[i] = 'x', and let q be the largest integer with 2*q <= budget. The function returns r = min(X, q).
  Preconditions: The general preconditions hold, and no two indices i and i+1 both contain 'x' (equivalently, every maximal x-run has length 1). -/
theorem spec_8 (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001)
    (hsingle : ∀ l ∈ roadRunLens road, l = 1) :
    ∀ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r →
        r.val = min (roadXCount road : ℤ) (budget.val / 2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001)
    (hsingle : ∀ l ∈ roadRunLens road, l = 1), ∀ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r →
        r.val = min (roadXCount road : ℤ) (budget.val / 2)) := by
  sorry

/-- If road contains at least one 'x', the function returns r = 1; if road contains no 'x', it returns r = 0.
  Preconditions: The general preconditions hold, and budget = 2. -/
theorem spec_9 (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001)
    (hbudget : budget.val = 2) :
    ∃ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r ∧
        (0 < roadXCount road → r.val = 1) ∧ (roadXCount road = 0 → r.val = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001)
    (hbudget : budget.val = 2), ∃ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r ∧
        (0 < roadXCount road → r.val = 1) ∧ (roadXCount road = 0 → r.val = 0)) := by
  sorry

/-- Let r1 be the result of max_potholes(road, B1) and r2 be the result of max_potholes(road, B2). Then r1 <= r2.
  Preconditions: road satisfies the general length and character constraints; B1 and B2 are i64 values with 1 <= B1 <= B2 <= 100001. -/
theorem spec_10 (road : Slice Std.U8) (B1 B2 : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hB1 : 1 ≤ B1.val) (hB12 : B1.val ≤ B2.val) (hB2 : B2.val ≤ 100001) :
    ∀ r1 r2 : Std.I64,
      Aegis.MaxPotholes.max_potholes road B1 = ok r1 →
        Aegis.MaxPotholes.max_potholes road B2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (road : Slice Std.U8) (B1 B2 : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hB1 : 1 ≤ B1.val) (hB12 : B1.val ≤ B2.val) (hB2 : B2.val ≤ 100001), ∀ r1 r2 : Std.I64,
      Aegis.MaxPotholes.max_potholes road B1 = ok r1 →
        Aegis.MaxPotholes.max_potholes road B2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Let r be the result of max_potholes(road, B) and let r' be the result of max_potholes(road, B + 1). Then r' <= r + 1.
  Preconditions: road satisfies the general length and character constraints; B is an i64 value with 1 <= B < 100001. -/
theorem spec_11 (road : Slice Std.U8) (B B' : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hB : 1 ≤ B.val) (hB_hi : B.val < 100001) (hB' : B'.val = B.val + 1) :
    ∀ r r' : Std.I64,
      Aegis.MaxPotholes.max_potholes road B = ok r →
        Aegis.MaxPotholes.max_potholes road B' = ok r' → r'.val ≤ r.val + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (road : Slice Std.U8) (B B' : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hB : 1 ≤ B.val) (hB_hi : B.val < 100001) (hB' : B'.val = B.val + 1), ∀ r r' : Std.I64,
      Aegis.MaxPotholes.max_potholes road B = ok r →
        Aegis.MaxPotholes.max_potholes road B' = ok r' → r'.val ≤ r.val + 1) := by
  sorry

/-- Let road_rev be the sequence defined by len(road_rev) = len(road) and road_rev[i] = road[len(road)-1-i] for 0 <= i < len(road). For every valid budget, max_potholes(road, budget) = max_potholes(road_rev, budget).
  Preconditions: len(road) is between 1 and 100000 inclusive; every byte of road is the ASCII code for '.' or the ASCII code for 'x'. -/
theorem spec_12 (road : Slice Std.U8)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte) :
    ∀ budget : Std.I64,
      1 ≤ budget.val → budget.val ≤ 100001 →
        Aegis.MaxPotholes.max_potholes road budget =
          Aegis.MaxPotholes.max_potholes (roadRev road) budget := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (road : Slice Std.U8)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte), ∀ budget : Std.I64,
      1 ≤ budget.val → budget.val ≤ 100001 →
        Aegis.MaxPotholes.max_potholes road budget =
          Aegis.MaxPotholes.max_potholes (roadRev road) budget) := by
  sorry

/-- For every budget B with 1 <= B <= 100001, max_potholes(road, B) = max_potholes(road2, B).
  Preconditions: road and road2 are two valid roads (length 1..100000, bytes '.' or 'x'). They have the same number m of maximal x-runs, and for every i from 1 to m, the i-th maximal x-run of road and the i-th maximal x-run of road2 have the same length. -/
theorem spec_13 (road road2 : Slice Std.U8)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hlen2_lo : 1 ≤ road2.length) (hlen2_hi : road2.length ≤ 100000)
    (hbytes2 : ∀ b ∈ road2.val, b.val = dotByte ∨ b.val = xByte)
    (hsame : roadRunLens road = roadRunLens road2) :
    ∀ B : Std.I64,
      1 ≤ B.val → B.val ≤ 100001 →
        Aegis.MaxPotholes.max_potholes road B = Aegis.MaxPotholes.max_potholes road2 B := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (road road2 : Slice Std.U8)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hlen2_lo : 1 ≤ road2.length) (hlen2_hi : road2.length ≤ 100000)
    (hbytes2 : ∀ b ∈ road2.val, b.val = dotByte ∨ b.val = xByte)
    (hsame : roadRunLens road = roadRunLens road2), ∀ B : Std.I64,
      1 ≤ B.val → B.val ≤ 100001 →
        Aegis.MaxPotholes.max_potholes road B = Aegis.MaxPotholes.max_potholes road2 B) := by
  sorry

/-- For every budget B with 1 <= B <= 100001, max_potholes(road, B) <= max_potholes(road2, B).
  Preconditions: road and road2 are valid roads of the same length; for every index i, if road[i] = 'x' then road2[i] = 'x' (so road2 is obtained from road by changing zero or more '.' characters to 'x'). -/
theorem spec_14 (road road2 : Slice Std.U8)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hlen_eq : road.length = road2.length)
    (hlen2_lo : 1 ≤ road2.length) (hlen2_hi : road2.length ≤ 100000)
    (hmono : SupportsX (roadBytes road) (roadBytes road2)) :
    ∀ B : Std.I64,
      1 ≤ B.val → B.val ≤ 100001 →
        ∀ r r2 : Std.I64,
          Aegis.MaxPotholes.max_potholes road B = ok r →
            Aegis.MaxPotholes.max_potholes road2 B = ok r2 → r.val ≤ r2.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (road road2 : Slice Std.U8)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hlen_eq : road.length = road2.length)
    (hlen2_lo : 1 ≤ road2.length) (hlen2_hi : road2.length ≤ 100000)
    (hmono : SupportsX (roadBytes road) (roadBytes road2)), ∀ B : Std.I64,
      1 ≤ B.val → B.val ≤ 100001 →
        ∀ r r2 : Std.I64,
          Aegis.MaxPotholes.max_potholes road B = ok r →
            Aegis.MaxPotholes.max_potholes road2 B = ok r2 → r.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns r, there exist an integer k >= 0, distinct indices i_1, ..., i_k of maximal x-runs of road, and positive integers a_1, ..., a_k such that a_j <= L_{i_j} for every j (where L_{i_j} is the length of x-run i_j), sum_{j=1..k} a_j = r, and sum_{j=1..k} (a_j + 1) <= budget.
  Preconditions: len(road) is between 1 and 100000 inclusive; every byte of road is the ASCII code for '.' or the ASCII code for 'x'; 1 <= budget <= 100001; budget is an i64 value in range. -/
theorem spec_15 (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001) :
    ∀ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r →
        ∃ ks amts : List ℕ, Witness (roadRunLens road) ks amts budget.val r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001), ∀ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r →
        ∃ ks amts : List ℕ, Witness (roadRunLens road) ks amts budget.val r.val) := by
  sorry

/-- Let X be the number of indices i with road[i] = 'x' and let m be the number of maximal x-runs of road. The function returns r = X if and only if X + m <= budget.
  Preconditions: len(road) is between 1 and 100000 inclusive; every byte of road is the ASCII code for '.' or the ASCII code for 'x'; 1 <= budget <= 100001. -/
theorem spec_16 (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001) :
    ∃ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r ∧
        (r.val = (roadXCount road : ℤ) ↔
          (roadXCount road : ℤ) + (roadRunCount road : ℤ) ≤ budget.val) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (road : Slice Std.U8) (budget : Std.I64)
    (hlen_lo : 1 ≤ road.length) (hlen_hi : road.length ≤ 100000)
    (hbytes : ∀ b ∈ road.val, b.val = dotByte ∨ b.val = xByte)
    (hbudget_lo : 1 ≤ budget.val) (hbudget_hi : budget.val ≤ 100001), ∃ r : Std.I64,
      Aegis.MaxPotholes.max_potholes road budget = ok r ∧
        (r.val = (roadXCount road : ℤ) ↔
          (roadXCount road : ℤ) + (roadRunCount road : ℤ) ≤ budget.val)) := by
  sorry

end AegisSpec.MaxPotholes
