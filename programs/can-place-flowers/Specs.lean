import Aegis.CanPlaceFlowers.Code.Funs

/-!
# Specifications of `Aegis.CanPlaceFlowers.can_place_flowers`

LeetCode problem `can-place-flowers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CanPlaceFlowers

  set_option autoImplicit false

  namespace AegisSpec.CanPlaceFlowers

  def plot (bed : List Std.I64) (i : ℕ) : ℤ := ((bed[i]?).map (fun x => x.val)).getD 0

  def plotZ (bed : List Std.I64) (i : ℤ) : ℤ := plot bed i.toNat

  def IsBinary (bed : List Std.I64) : Prop :=
    ∀ i, i < bed.length → plot bed i = 0 ∨ plot bed i = 1

  def NoAdjacentOnes (bed : List Std.I64) : Prop :=
    ∀ i, i + 1 < bed.length → ¬ (plot bed i = 1 ∧ plot bed (i + 1) = 1)

  def Feasible (bed : List Std.I64) (n : ℤ) : Prop :=
    ∃ S : Finset ℤ,
      (∀ i ∈ S, 0 ≤ i ∧ i < (bed.length : ℤ) ∧ plotZ bed i = 0) ∧
      (S.card : ℤ) = n ∧
      (∀ i ∈ S, ∀ j : ℤ, |j - i| = 1 → j ∉ S) ∧
      (∀ i ∈ S, (0 < i → plotZ bed (i - 1) = 0) ∧
        (i + 1 < (bed.length : ℤ) → plotZ bed (i + 1) = 0))

  def zeroCount (bed : List Std.I64) : ℕ :=
    (List.range bed.length).countP (fun i => decide (plot bed i = 0))

  def zeroRunLen (bed : List Std.I64) (s : ℕ) : ℕ :=
    ((bed.drop s).takeWhile (fun x => decide (x.val = 0))).length

  def capAt (bed : List Std.I64) (s : ℕ) : ℕ :=
    if s = 0 ∧ s + zeroRunLen bed s = bed.length then (zeroRunLen bed s + 1) / 2
    else if s = 0 ∨ s + zeroRunLen bed s = bed.length then zeroRunLen bed s / 2
    else (zeroRunLen bed s - 1) / 2

  def capacity (bed : List Std.I64) : ℕ :=
    (((List.range bed.length).filter
        (fun s => decide (plot bed s = 0 ∧ (s = 0 ∨ plot bed (s - 1) = 1)))).map
      (capAt bed)).sum

  theorem slice_val_length {α : Type} (s : Slice α) : s.val.length = s.leng :=
    Aeneas.Data.ListN.ListN_length s.list

  def revSlice (flowerbed : Slice Std.I64) : Slice Std.I64 :=
    ⟨flowerbed.val.reverse.length, Aeneas.Data.ListN.ListN.fromList flowerbed.val.reverse, by
      simpa [List.length_reverse, slice_val_length] using flowerbed.bound⟩

  /-- Whenever the function returns a result r, r = true if and only if there exists a set S of integers such that (1) for every i in S, 0 <= i < L and flowerbed[i] = 0; (2) S has exactly n elements; (3) for every i in S and every integer j with |j - i| = 1, j is not in S; and (4) for every i in S, if i > 0 then flowerbed[i-1] = 0, and if i+1 < L then flowerbed[i+1] = 0. Equivalently, r is true exactly when n flowers can be placed in empty plots so that no two placed flowers are adjacent and no placed flower is adjacent to an already existing flower.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); and 0 <= n <= L, with n interpreted as a natural number. -/
  theorem spec_1 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ)) :
      ∀ r, can_place_flowers flowerbed n = ok r → (r = true ↔ Feasible flowerbed.val n.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ)), ∀ r, can_place_flowers flowerbed n = ok r → (r = true ↔ Feasible flowerbed.val n.val)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (a Boolean); it does not fail, panic, overflow, or access an index out of bounds.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); and 0 <= n <= L, with n interpreted as a natural number. -/
  theorem spec_2 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ)) :
      ∃ r : Bool, can_place_flowers flowerbed n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ)), ∃ r : Bool, can_place_flowers flowerbed n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = true. Equivalently, with zero new flowers the answer is always true.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); 0 <= n <= L; and n = 0. -/
  theorem spec_3 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ))
      (hn : n.val = 0) :
      ∀ r, can_place_flowers flowerbed n = ok r → r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ))
        (hn : n.val = 0), ∀ r, can_place_flowers flowerbed n = ok r → r = true) := by
    sorry

  /-- Whenever the function returns a result r, r = true if and only if there exists an index i such that 0 <= i < L, flowerbed[i] = 0, (i = 0 or flowerbed[i-1] = 0), and (i+1 = L or flowerbed[i+1] = 0). That is, r is true exactly when some empty plot has no adjacent existing flower.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); 0 <= n <= L; and n = 1. -/
  theorem spec_4 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ))
      (hn : n.val = 1) :
      ∀ r, can_place_flowers flowerbed n = ok r →
        (r = true ↔ ∃ i : ℤ,
          0 ≤ i ∧ i < (flowerbed.val.length : ℤ) ∧ plotZ flowerbed.val i = 0 ∧
            (i = 0 ∨ plotZ flowerbed.val (i - 1) = 0) ∧
            (i + 1 = (flowerbed.val.length : ℤ) ∨ plotZ flowerbed.val (i + 1) = 0)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ))
        (hn : n.val = 1), ∀ r, can_place_flowers flowerbed n = ok r →
          (r = true ↔ ∃ i : ℤ,
            0 ≤ i ∧ i < (flowerbed.val.length : ℤ) ∧ plotZ flowerbed.val i = 0 ∧
              (i = 0 ∨ plotZ flowerbed.val (i - 1) = 0) ∧
              (i + 1 = (flowerbed.val.length : ℤ) ∨ plotZ flowerbed.val (i + 1) = 0))) := by
    sorry

  /-- Whenever the function returns a result r, r = true if and only if L = 1 and flowerbed[0] = 0.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); 0 <= n <= L; and n = L. -/
  theorem spec_5 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ))
      (hn : n.val = (flowerbed.val.length : ℤ)) :
      ∀ r, can_place_flowers flowerbed n = ok r →
        (r = true ↔ flowerbed.val.length = 1 ∧ plot flowerbed.val 0 = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ))
        (hn : n.val = (flowerbed.val.length : ℤ)), ∀ r, can_place_flowers flowerbed n = ok r →
          (r = true ↔ flowerbed.val.length = 1 ∧ plot flowerbed.val 0 = 0)) := by
    sorry

  /-- Whenever the function returns a result r, r = true if and only if n <= (L+1)//2, where // denotes integer division rounding down.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); 0 <= n <= L; and for every i with 0 <= i < L, flowerbed[i] = 0. -/
  theorem spec_6 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ))
      (hzero : ∀ i, i < flowerbed.val.length → plot flowerbed.val i = 0) :
      ∀ r, can_place_flowers flowerbed n = ok r →
        (r = true ↔ n.val ≤ (((flowerbed.val.length + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ))
        (hzero : ∀ i, i < flowerbed.val.length → plot flowerbed.val i = 0), ∀ r, can_place_flowers flowerbed n = ok r →
          (r = true ↔ n.val ≤ (((flowerbed.val.length + 1) / 2 : ℕ) : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, r = true if and only if (n = 0) or (n = 1 and flowerbed[0] = 0).
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); 0 <= n <= L; and L = 1. -/
  theorem spec_7 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ))
      (hlen : flowerbed.val.length = 1) :
      ∀ r, can_place_flowers flowerbed n = ok r →
        (r = true ↔ n.val = 0 ∨ (n.val = 1 ∧ plot flowerbed.val 0 = 0)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ))
        (hlen : flowerbed.val.length = 1), ∀ r, can_place_flowers flowerbed n = ok r →
          (r = true ↔ n.val = 0 ∨ (n.val = 1 ∧ plot flowerbed.val 0 = 0))) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then n <= Z, where Z is the number of indices i with 0 <= i < L and flowerbed[i] = 0.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); and 0 <= n <= L. -/
  theorem spec_8 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ)) :
      ∀ r, can_place_flowers flowerbed n = ok r → r = true →
        n.val ≤ (zeroCount flowerbed.val : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ)), ∀ r, can_place_flowers flowerbed n = ok r → r = true →
          n.val ≤ (zeroCount flowerbed.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = true if and only if n = 0.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); 0 <= n <= L; and for every i with 0 <= i < L, if flowerbed[i] = 0 then either (i > 0 and flowerbed[i-1] = 1) or (i+1 < L and flowerbed[i+1] = 1). -/
  theorem spec_9 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ))
      (hsat : ∀ i, i < flowerbed.val.length → plot flowerbed.val i = 0 →
        (0 < i ∧ plot flowerbed.val (i - 1) = 1) ∨
          (i + 1 < flowerbed.val.length ∧ plot flowerbed.val (i + 1) = 1)) :
      ∀ r, can_place_flowers flowerbed n = ok r → (r = true ↔ n.val = 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ))
        (hsat : ∀ i, i < flowerbed.val.length → plot flowerbed.val i = 0 →
          (0 < i ∧ plot flowerbed.val (i - 1) = 1) ∨
            (i + 1 < flowerbed.val.length ∧ plot flowerbed.val (i + 1) = 1)), ∀ r, can_place_flowers flowerbed n = ok r → (r = true ↔ n.val = 0)) := by
    sorry

  /-- Consider two invocations of the function on the same flowerbed, one with n1 and one with n2. Whenever both invocations return results r1 and r2, if r2 = true then r1 = true. Equivalently, feasibility is downward monotone in the requested number of flowers.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); and let n1 and n2 be integers with 0 <= n1 <= n2 <= L. -/
  theorem spec_10 (flowerbed : Slice Std.I64) (n1 n2 : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn1 : 0 ≤ n1.val)
      (hle : n1.val ≤ n2.val)
      (hn2 : n2.val ≤ (flowerbed.val.length : ℤ)) :
      ∀ r1 r2, can_place_flowers flowerbed n1 = ok r1 →
        can_place_flowers flowerbed n2 = ok r2 → r2 = true → r1 = true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n1 n2 : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn1 : 0 ≤ n1.val)
        (hle : n1.val ≤ n2.val)
        (hn2 : n2.val ≤ (flowerbed.val.length : ℤ)), ∀ r1 r2, can_place_flowers flowerbed n1 = ok r1 →
          can_place_flowers flowerbed n2 = ok r2 → r2 = true → r1 = true) := by
    sorry

  /-- Whenever the invocation on G with n returns true and the invocation on F with n returns a result rF, rF = true. In other words, adding existing flowers, changing some 0s to 1s while preserving the no-adjacent-flowers rule, cannot make a placement possible that was not possible with fewer existing flowers.
    Preconditions: Let F = flowerbed and L = len(F). Assume: 1 <= L; for every i with 0 <= i < L, F[i] is either 0 or 1; for every i with 0 <= i < L-1, not (F[i] = 1 and F[i+1] = 1). Let G be another slice of i64 of length L satisfying: for every i with 0 <= i < L, G[i] is 0 or 1; for every i with 0 <= i < L-1, not (G[i] = 1 and G[i+1] = 1); and for every i with 0 <= i < L, F[i] = 1 implies G[i] = 1. Assume 0 <= n <= L. -/
  theorem spec_11 (F G : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ F.val.length)
      (hFbin : IsBinary F.val)
      (hFno : NoAdjacentOnes F.val)
      (hGlen : G.val.length = F.val.length)
      (hGbin : IsBinary G.val)
      (hGno : NoAdjacentOnes G.val)
      (hmono : ∀ i, i < F.val.length → plot F.val i = 1 → plot G.val i = 1)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (F.val.length : ℤ)) :
      ∀ rF, can_place_flowers G n = ok true → can_place_flowers F n = ok rF → rF = true := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (F G : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ F.val.length)
        (hFbin : IsBinary F.val)
        (hFno : NoAdjacentOnes F.val)
        (hGlen : G.val.length = F.val.length)
        (hGbin : IsBinary G.val)
        (hGno : NoAdjacentOnes G.val)
        (hmono : ∀ i, i < F.val.length → plot F.val i = 1 → plot G.val i = 1)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (F.val.length : ℤ)), ∀ rF, can_place_flowers G n = ok true → can_place_flowers F n = ok rF → rF = true) := by
    sorry

  /-- Let rev be the slice of length L defined by rev[i] = flowerbed[L-1-i] for every 0 <= i < L. Whenever the invocation on flowerbed with n and the invocation on rev with n return results r and r_rev, r = r_rev.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); and 0 <= n <= L. -/
  theorem spec_12 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ)) :
      ∀ r r_rev, can_place_flowers flowerbed n = ok r →
        can_place_flowers (revSlice flowerbed) n = ok r_rev → r = r_rev := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ)), ∀ r r_rev, can_place_flowers flowerbed n = ok r →
          can_place_flowers (revSlice flowerbed) n = ok r_rev → r = r_rev) := by
    sorry

  /-- Whenever the invocation with n returns true, there exists an index i such that 0 <= i < L, flowerbed[i] = 0, (i = 0 or flowerbed[i-1] = 0), (i+1 = L or flowerbed[i+1] = 0), and the invocation on the same flowerbed with n-1 returns true. Thus a true answer for n witnesses one safe plot whose planting reduces the problem to a true answer for n-1.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); and 1 <= n <= L. -/
  theorem spec_13 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 1 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ)) :
      can_place_flowers flowerbed n = ok true →
        ∃ (i : ℤ) (n' : Std.I64),
          0 ≤ i ∧ i < (flowerbed.val.length : ℤ) ∧ plotZ flowerbed.val i = 0 ∧
            (i = 0 ∨ plotZ flowerbed.val (i - 1) = 0) ∧
            (i + 1 = (flowerbed.val.length : ℤ) ∨ plotZ flowerbed.val (i + 1) = 0) ∧
            n'.val = n.val - 1 ∧
            can_place_flowers flowerbed n' = ok true := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 1 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ)), can_place_flowers flowerbed n = ok true →
          ∃ (i : ℤ) (n' : Std.I64),
            0 ≤ i ∧ i < (flowerbed.val.length : ℤ) ∧ plotZ flowerbed.val i = 0 ∧
              (i = 0 ∨ plotZ flowerbed.val (i - 1) = 0) ∧
              (i + 1 = (flowerbed.val.length : ℤ) ∨ plotZ flowerbed.val (i + 1) = 0) ∧
              n'.val = n.val - 1 ∧
              can_place_flowers flowerbed n' = ok true) := by
    sorry

  /-- Let C be defined as follows. Consider every maximal interval [s,e] of indices such that flowerbed[i] = 0 for all s <= i <= e, s = 0 or flowerbed[s-1] = 1, and e = L-1 or flowerbed[e+1] = 1. For such an interval let m = e-s+1 and assign capacity c = (m+1)//2 if s = 0 and e = L-1; c = m//2 if exactly one of s = 0 and e = L-1 holds; and c = (m-1)//2 if s > 0 and e < L-1. Let C be the sum of c over all such intervals, with C = 0 if there are no zero intervals. Whenever the function returns a result r, r = true if and only if n <= C. Here // denotes integer division rounding down.
    Preconditions: Let L = len(flowerbed). Assume: 1 <= L; for every i with 0 <= i < L, flowerbed[i] is either 0 or 1; for every i with 0 <= i < L-1, not (flowerbed[i] = 1 and flowerbed[i+1] = 1); and 0 <= n <= L. -/
  theorem spec_14 (flowerbed : Slice Std.I64) (n : Std.I64)
      (hL : 1 ≤ flowerbed.val.length)
      (hbin : IsBinary flowerbed.val)
      (hno : NoAdjacentOnes flowerbed.val)
      (hn0 : 0 ≤ n.val)
      (hnL : n.val ≤ (flowerbed.val.length : ℤ)) :
      ∀ r, can_place_flowers flowerbed n = ok r →
        (r = true ↔ n.val ≤ (capacity flowerbed.val : ℤ)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (flowerbed : Slice Std.I64) (n : Std.I64)
        (hL : 1 ≤ flowerbed.val.length)
        (hbin : IsBinary flowerbed.val)
        (hno : NoAdjacentOnes flowerbed.val)
        (hn0 : 0 ≤ n.val)
        (hnL : n.val ≤ (flowerbed.val.length : ℤ)), ∀ r, can_place_flowers flowerbed n = ok r →
          (r = true ↔ n.val ≤ (capacity flowerbed.val : ℤ))) := by
    sorry

  end AegisSpec.CanPlaceFlowers
